"""
IntelShell
==============================

이 모듈은 가상 터미널(PTY)을 통해 자식 셸 프로세스와 통신하고, 
사용자에게는 prompt_toolkit 기반의 고도로 정제된 인터페이스를 제공하는 래퍼 클래스를 포함합니다.

주요 아키텍처 및 기능:
--------------------
1. 비동기 스트림 처리 (Sequencer):
   - 셸로부터 들어오는 ANSI/OSC 이스케이프 시퀀스를 실시간으로 해석하는 상태 머신입니다.
   - 데이터 조각(chunk)이 경계 지점에서 잘려 들어와도 완벽하게 조립하여 처리합니다.
   - 특정 시퀀스 감지 시 콜백을 트리거하여 프롬프트 변경이나 명령 완료를 감지합니다.

2. 투명한 입력 브릿지 (Type-ahead):
   - 명령어가 실행 중인 동안에도 사용자의 입력을 가로채어 셸의 입력 버퍼(master_fd)로 전달합니다.
   - 동시에 입력된 데이터를 별도 버퍼(`dupin_buffer`)에 보관했다가, 명령 종료 후 
     prompt_toolkit의 입력창이 뜰 때 `Vt100Parser`를 통해 실제 키 이벤트로 재현(Replay)합니다.

3. 커널 상태 기반 워치독 (Self-healing):
   - 셸 프로세스의 TTY 제어권(`tcgetpgrp`)과 시스템 콜(`syscall`) 상태를 감시합니다.
   - 셸이 대기 상태(Standby)가 되었음에도 불구하고 마커 시퀀스가 도착하지 않는 경우,
     사용자가 설정을 파괴(예: source .cshrc)한 것으로 판단하고 통합 스크립트를 재주입합니다.

4. PTY 및 터미널 모드 제어:
   - `os.dup(0)`을 통해 표준 입력을 복제하여 prompt_toolkit과의 FD 충돌을 방지합니다.
   - 명령어 실행 시에는 `TCSANOW`를 통해 터미널 에코를 켜고, 입력 대기 시에는 
     `mute_attrs`를 통해 에코를 제어하여 깔끔한 UI를 유지합니다.

사용 환경:
---------
- Linux/Unix 환경 ( /proc 파일시스템 및 PTY 지원 필요 )
- Python 3.8+ ( asyncio, psutil 라이브러리 의존 )

예시:
--------
기본적인 bash 실행 방법:
>>> from toad.shell import InteractiveShell
>>> shell = InteractiveShell(shell='bash')
>>> shell.run()

사용자 정의 프롬프트 세션을 이용한 csh 실행 방법:
>>> from prompt_toolkit import PromptSession
>>> from prompt_toolkit.styles import Style
>>> custom_style = Style.from_dict({'prompt': 'cyan bold'})
>>> session = PromptSession(style=custom_style)
>>> 
>>> shell = InteractiveShell(shell='csh', prompt=session)
>>> shell.run()

데이터 청크 사이즈 조정 (대량 로그 처리 최적화):
>>> shell = InteractiveShell(shell='zsh', chunk=65536)
>>> shell.run()

구조적 특징:
-----------
- `shell`: 사용할 셸의 종류 ('sh', 'bash', 'zsh', 'csh', 'tcsh' 지원)
- `prompt`: prompt_toolkit의 PromptSession 객체 (스타일, 자동완성 등 설정 가능)
- `chunk`: I/O 처리를 위한 버퍼 크기 (기본값 1MB)
"""

from __future__ import annotations

import array
import asyncio
import codecs
import fcntl
import os
import pty
import re
import select
import shutil
import signal
import struct
import sys
import tempfile
import termios
import tty
from pathlib import Path
from typing import TYPE_CHECKING

import psutil
from prompt_toolkit import PromptSession, ANSI
from prompt_toolkit.application import get_app
from prompt_toolkit.input.vt100_parser import Vt100Parser

if TYPE_CHECKING:
    from typing import Any, Union, Optional, Dict, List, Tuple, Callable
    from asyncio import AbstractEventLoop
    from prompt_toolkit.application import Application

__all__ = [
    "InteractiveShell"
]


class Sequencer:
    """
    ANSI/OSC 이스케이프 시퀀스를 해석하고 특정 패턴 감지 시 콜백을 실행하는 상태 머신.
    데이터가 조각나서 들어와도 상태를 유지하며 완벽한 시퀀스를 조립함.
    """
    def __init__(self, encoding: str = "utf-8", errors: str = "replace"):
        # 내부 상태 및 버퍼 초기화
        self.buffer: bytearray = bytearray()           # 현재 조립 중인 시퀀스 버퍼
        self.between_buffer: bytearray = bytearray()   # 두 시퀀스 사이의 데이터를 담는 버퍼
        self.state: int = 0                            # FSM 상태 (0: GROUND, 1: ESC, 2: CSI, 3: OSC, 4: BETWEEN)

        self.decoder = codecs.getincrementaldecoder(encoding)(errors=errors)
        self.encoding = encoding

        self.callbacks: Dict[bytes, Tuple[Callable, bool]] = {}
        self.between_callbacks: Dict[
            bytes, Tuple[bytes, Callable, bool]
        ] = {}
        self.active_between: Tuple[bytes, bytes, Callable, bool]

    def on_sequence(self, seq: bytes, callback: Callable, remove_seq: bool = True) -> None:
        """특정 단일 시퀀스 감지 시 실행할 콜백 등록"""
        self.callbacks[seq] = (callback, remove_seq)

    def between_sequence(
        self,
        start_seq: bytes,
        end_seq: bytes,
        callback: Callable[[bytes], None],
        remove_seq: bool = True,
    ) -> None:
        """시작 시퀀스와 종료 시퀀스 사이의 내용을 가로채는 콜백 등록"""
        self.between_callbacks[start_seq] = (end_seq, callback, remove_seq)

    def _flush_text(self, buffer: bytearray):
        """버퍼에 쌓인 일반 텍스트 바이트를 디코딩하여 결과 출력물에 추가"""
        try:
            decoded_str = self.decoder.decode(self.buffer, final=False)
            if decoded_str:
                buffer.extend(decoded_str.encode(self.encoding))
                self.buffer.clear()
            else:
                pass
        except Exception:
            buffer.extend(self.buffer)
            self.buffer.clear()

    def _union(self, buffer: bytearray) -> None:
        """완성된 시퀀스를 분석하여 콜백 실행 혹은 출력물로 방출 결정"""
        data = bytes(self.buffer)

        # 1. 구간 캡처 시작 시퀀스인지 확인
        if data in self.between_callbacks:
            end_seq, callback, remove_seq = self.between_callbacks[data]
            self.active_between = (data, end_seq, callback, remove_seq)
            self.between_buffer.clear()
            if not remove_seq:
                buffer.extend(self.buffer)
            self.buffer.clear()
            self.state = 4
            return

        # 2. 단일 이벤트 시퀀스인지 확인
        if data in self.callbacks:
            callback, remove_seq = self.callbacks[data]
            callback()
            if not remove_seq:
                buffer.extend(self.buffer)
        else:
            buffer.extend(self.buffer)

        self.buffer.clear()
        self.state = 0

    def _between(self, byte, buffer: bytearray):
        """종료 시퀀스가 나올 때까지 바이트를 between_buffer에 수집"""
        self.between_buffer.append(byte)
        data = bytes(self.between_buffer)
        start_seq, end_seq, callback, remove_seq = self.active_between
        
        if data.endswith(end_seq):
            payload = data[: -len(end_seq)]
            callback(payload)
            
            if not remove_seq:
                buffer.extend(bytearray(end_seq))

            self.between_buffer.clear()
            if end_seq in self.between_callbacks:
                new_end_seq, new_callback, new_remove_seq = self.between_callbacks[end_seq]
                self.active_between = (end_seq, new_end_seq, new_callback, new_remove_seq)
                self.state = 4 # 상태를 4로 유지하여 바로 다음 구간 수집 시작
            else:
                self.state = 0

    def interpret(self, data: bytes):
        """바이트 스트림을 한 바이트씩 훑으며 상태 머신 가동 (메인 엔진)"""
        output = bytearray()
        
        for byte in data:
            if self.state == 0: # 일반 텍스트 상태
                if byte == 0x1B: # ESC
                    self._flush_text(output)
                    self.buffer.append(byte)
                    self.state = 1
                else:
                    self.buffer.append(byte)

            elif self.state == 1: # ESC 수신 후 상태
                self.buffer.append(byte)
                if byte == 0x5B: # [ (CSI)
                    self.state = 2
                elif byte == 0x5D: # ] (OSC)
                    self.state = 3
                elif 0x40 <= byte <= 0x5F:
                    self._union(output)

            elif self.state == 2: # CSI 처리 중
                self.buffer.append(byte)
                if 0x40 <= byte <= 0x7E:
                    self._union(output)

            elif self.state == 3: # OSC 처리 중
                self.buffer.append(byte)
                if byte == 0x07:
                    self._union(output)
                elif self.buffer.endswith(b"\x1b\\"):
                    self._union(output)

            elif self.state == 4: # 구간 데이터 수집 중
                self._between(byte, output)

        if self.state == 0:
            self._flush_text(output)

        return bytes(output)


class InteractiveShell:
    # 셸 통합(Shell Integration)을 위한 OSC 633 표준 마커 정의
    BEFORE_PROMPT: bytes = b"\x1b]633;S\a"        # 프롬프트 출력 시작
    AFTER_PROMPT: bytes = b"\x1b]633;E\a"         # 프롬프트 출력 종료
    BEFORE_CONTINUATION: bytes = b"\x1b]633;s\a"  # 보조 프롬프트(PS2) 시작
    AFTER_CONTINUATION: bytes = b"\x1b]633;e\a"   # 보조 프롬프트 종료
    COMMAND_START: bytes = b"\x1b]633;C\a"        # 명령어 실행 시작
    COMMAND_DONE: bytes = b"\x1b]633;D\a"         # 명령어 실행 완료

    ALT_SCREEN_START_1: bytes = b"\x1b[?1047h"
    ALT_SCREEN_START_2: bytes = b"\x1b[?1049h"
    ALT_SCREEN_END_1: bytes = b"\x1b[?1047l"
    ALT_SCREEN_END_2: bytes = b"\x1b[?1049l"

    def __init__(
        self,
        shell: str = "bash",
        prompt: PromptSession = PromptSession("> "),
        chunk: int = 1024 * 1024,
    ):
        """환경 설정 및 비동기 이벤트를 위한 초기화"""
        self.encoder: str = sys.stdout.encoding or "utf-8"
        self.chunk_size: int = chunk

        self.stdin_fd: int = sys.stdin.fileno()
        self.stdout_fd: int = sys.stdout.fileno()
        self.stderr_fd: int = sys.stderr.fileno()

        self.master_fd: int
        self.slave_fd: int
        self.dupin_fd: int

        self.original_attrs: List[Union[int, List[int]]]
        self.mute_attrs: List[Union[int, List[int]]]

        self.shell_pipe_path: str = tempfile.mktemp(
            prefix=str(os.getuid()), suffix=".fifo", dir=tempfile.gettempdir()
        )
        self.shell_pipe:int

        self.shell: str = shell
        self.shell_args: Tuple[str, ...] = {
            "sh": ("-i",),
            "bash": ("-i",),
            "zsh": ("-i",),
            "csh": ("-i",),
            "tcsh": ("-i",),
        }.get(self.shell, ())

        self.shell_pid: int = -1
        self.shell_pgid: int = -1
        self.shell_ps: psutil.Process

        self._environ: Dict[str, str] = os.environ.copy()
        self._variable: Dict[str, List[str]] = {}
        self._alias: Dict[str, str] = {}

        self.auxiliary_path: Path = Path("/user...")
        self.shell_integration: str = str(
            {
                "sh": self.auxiliary_path / "shellIntegration.sh",
                "bash": self.auxiliary_path / "shellIntegration.sh",
                "zsh": self.auxiliary_path / "shellIntegration.zsh",
                "csh": self.auxiliary_path / "shellIntegration.csh",
                "tcsh": self.auxiliary_path / "shellIntegration.csh",
            }.get(self.shell, "")
        )
        self.shell_integration_command: str = (
            {
                "sh": f" (source {self.shell_integration} {self.shell_pipe_path} > /dev/null 2>&1 &)",
                "bash": f" (source {self.shell_integration} {self.shell_pipe_path} > /dev/null 2>&1 &)",
                "zsh": f" (source {self.shell_integration} {self.shell_pipe_path} > /dev/null 2>&1 &)",
                "csh": f"(source {self.shell_integration} {self.shell_pipe_path} & ) > & /dev/null",
                "tcsh": f"(source {self.shell_integration} {self.shell_pipe_path} & ) > & /dev/null",
            }.get(self.shell, "")
            if self.shell_integration
            else ""
        )

        common_setter: str = f"source {self.shell_integration} {self.shell_pipe_path}"
        self.init_command: str = {
            "sh": f"{common_setter}",
            "bash": f"{common_setter}",
            "zsh": f"{common_setter}",
            "csh": f"{common_setter}",
            "tcsh": f"{common_setter}",
        }.get(self.shell, common_setter)

        self.prompt_event: asyncio.Event
        self.command_start_event: asyncio.Event
        self.command_done_event: asyncio.Event
        self.continuation_active: asyncio.Event
        self.alt_screen_active: asyncio.Event

        self.loop: AbstractEventLoop
        self.proc: asyncio.subprocess.Process

        self.prompt_tick_rate: float = 0.02
        self.recovering_tick_rate: float = 0.1

        self.tasks: Optional[List[asyncio.Task]]
        self.cleanup_handlers: List[Callable[[], Any]]
        self.message: Union[bytes, str]
        self.shell_pipe_buffer: Union[bytes, str]
        self.dupin_buffer: bytearray

        self.sequencer: Sequencer

        self.session: PromptSession
        self.session_app: Application
        self.session_parser: Vt100Parser

    @staticmethod
    def _set_window_size(fd, col, row, xpix=0, ypix=0) -> None:
        """PTY의 물리적 터미널 크기를 전파"""
        win_size = struct.pack("HHHH", row, col, xpix, ypix)
        fcntl.ioctl(fd, termios.TIOCSWINSZ, win_size)

    def _sigwinch_handler(self, signum, frame) -> None:
        """OS로부터 윈도우 리사이즈 신호를 받았을 때 실행되는 콜백"""
        self._set_window_size(self.master_fd, *shutil.get_terminal_size())

    def _is_standby(self) -> bool:
        """커널 상태를 조회하여 셸이 명령어를 끝내고 대기 중인지 판단"""
        try:
            if os.tcgetpgrp(self.master_fd) != self.shell_pgid:
                return False
            status = self.shell_ps.status()
            return status in {
                psutil.STATUS_SLEEPING,
                psutil.STATUS_IDLE,
                psutil.STATUS_DISK_SLEEP,
            }
        except OSError:
            return False

    def _is_read_syscall(self, pid) -> bool:
        path = f"/proc/{pid}/syscall".encode()
        fd = -1
        try:
            # os.open에 바이트 경로를 직접 전달 (가장 빠름)
            fd = os.open(path, os.O_RDONLY)
            # 2바이트만 읽음 (예: "0 ")
            if os.read(fd, 2) == b"0 ":
                return True
        except:
            pass
        finally:
            if fd != -1:
                os.close(fd)
        return False

    def _set_prompt(self, prompt: bytes) -> None:
        """Sequencer가 캡처한 메인 프롬프트를 prompt-toolkit 메시지로 설정"""
        self.continuation_active.clear()
        cleaned_prompt = prompt.replace(b"\r\n", b"\n")
        self.session.message = ANSI(
            cleaned_prompt.decode(self.encoder, errors="ignore")
        )

    def _set_continuation(self, prompt: bytes) -> None:
        """멀티라인 입력을 위한 보조 프롬프트(PS2) 설정"""
        self.continuation_active.set()
        cleaned_prompt = prompt.replace(b"\r\n", b"\n")
        self.session.message = ANSI(
            cleaned_prompt.decode(self.encoder, errors="ignore")
        )
       
    def _set_command_start(self, command: bytes) -> None:
        """명령어 실행 시그널"""
        self.prompt_event.clear(); self.command_start_event.set(); self.command_done_event.clear()

    def _read(self, fd: int) -> bytes:
        """파일 디스크립터로부터 논블로킹 방식으로 데이터 읽기"""
        try: return os.read(fd, self.chunk_size)
        except (OSError, BlockingIOError): return b""

    def _write(self, fd: int, data: Union[bytes, bytearray]) -> None:
        """BlockingIOError를 방지하며 안전하게 데이터 쓰기"""
        while True:
            try:
                os.write(fd, data)
                break
            except BlockingIOError: continue

    def _echo(self, fd: int, data: bytes, iflags: int, oflags: int, lflags: int) -> None:
        visual_output: bytearray = bytearray()
       
        icrnl = iflags & termios.ICRNL
        echo = lflags & termios.ECHO
        echoe = lflags & termios.ECHOE
        
        if not echo:
            return
       
        i: int = 0
        while i < len(data):
            byte = data[i:i + 1]
            val = data[i]
            if val == 0x1b:
                match = re.match(rb'\x1b\[[0-9;?]*[a-zA-Z~]', data[i:])
                if match:
                    seq = match.group()
                    self.dupin_buffer.extend(seq)
                    visual_output.extend(seq.replace(b'\x1b', b'^['))
                    i += len(seq)
                else:
                    self.dupin_buffer.append(val)
                    visual_output.extend(b'^[')
                    i += 1
            else:
                self.dupin_buffer.append(val)
                if val == 0x08:
                    visual_output.extend(b'\b \b' if echoe else b'\b')
                elif val == 0x0d:
                    visual_output.extend(b'\r\n' if icrnl else b'\n')
                elif val == 0x17:
                    original_len = len(self.dupin_buffer)
                    new_buffer = re.sub(rb'\s*\S+\s*$', b'', self.dupin_buffer)
                    diff = original_len - len(new_buffer)
                    visual_output.extend(b'\b \b' * diff)
                else:
                    visual_output.extend(byte)
                i += 1
        
        result = bytes(visual_output)
        try:
            os.write(fd, result)
        except BlockingIOError:
            pass

    def _input(self, fd: int) -> None:
        """명령어 실행 중 사용자가 입력한 데이터를 PTY로 전달하고 버퍼에 보관"""
        data = self._read(fd)
       
        fg_pgid = os.tcgetpgrp(self.master_fd)
        fg_read = self._is_read_syscall(fg_pgid)
       
        shell_fg = fg_pgid == self.shell_pgid
        attrs = termios.tcgetattr(self.slave_fd)
        
        input_flags = attrs[0]
        output_flags = attrs[1]
        local_flags = attrs[3]
        control_characters = attrs[6]
        isig_signals = {
            control_characters[termios.VINTR], 
            control_characters[termios.VQUIT], 
            control_characters[termios.VSUSP]
        }
        iexten_signals = {
            control_characters[termios.VLNEXT],
            control_characters[termios.VREPRINT],
            control_characters[termios.VDISCARD],
            control_characters[termios.VWERASE],
        }
        raw_mode = (
            not (local_flags & termios.ECHO) or 
            not (local_flags & termios.ICANON)
        )
        
        contains_isig = any(char in data for char in isig_signals if char) and (local_flags & termios.ISIG)
        contains_iexten = any(char in data for char in iexten_signals if char) and (local_flags & termios.IEXTEN)

        if contains_isig:
            self.dupin_buffer.clear()
            self._write(self.master_fd, data)
            return

        if raw_mode:
            self._write(self.master_fd, data)
            if local_flags & termios.ECHO:
                self._echo(self.stdout_fd, data, input_flags, output_flags, local_flags)
            return

        if not shell_fg:
            if self._is_read_syscall(fg_pgid)):
                self._write(self.master_fd, data)
            else:
                if local_flags & termios.ECHO:
                    self._echo(self.stdout_fd, data, input_flags, output_flags, local_flags)
                    if contains_iexten:
                        self._write(self.master_fd, data)
                else:
                    self._write(self.master_fd, data)
            return

        self._echo(self.stdout_fd, data, input_flags, output_flags, local_flags)
        if contains_iexten:
            self._write(self.master_fd, data)

    def _display(self, fd) -> None:
        """셸의 출력을 읽어 Sequencer를 거친 후 실제 터미널(stdin_fd)에 출력"""
        data = self.sequencer.interpret(self._read(fd))
        self._write(self.stdin_fd, data)
        if self.command_done_event.is_set():
            self.prompt_event.set()

    def _update(self, fd: int) -> None:
        """상태 공유용 파이프(FIFO)로부터 정보를 읽어 업데이트 (구현 예정)"""
        pass

    async def _send(self, data: Union[str, bytes]):
        """셸(PTY)의 표준 입력으로 데이터를 비동기 전송"""
        text_bytes = data.encode(self.encoder, "ignore") if isinstance(data, str) else data
        return await asyncio.to_thread(os.write, self.master_fd, text_bytes)

    async def _exec(self, data: Union[str, bytes]) -> None:
        """명령어를 셸에 전달하고, 마커와 커널 상태가 '완료'를 가리킬 때까지 대기"""
        try:
            termios.tcsetattr(self.slave_fd, termios.TCSANOW, self.original_attrs) # 원래 터미널 속성 복구
            termios.tcsetattr(self.dupin_fd, termios.TCSANOW, self.original_attrs) # 원래 터미널 속성 복구
            self.loop.add_reader(self.dupin_fd, self._input, self.dupin_fd) # 입력 중계 시작
            await self._send(data) # 입력 전달
            await asyncio.gather(self.prompt_event.wait(), self.command_done_event.wait()) # 입력 완료 대기
        finally:
            self.loop.remove_reader(self.dupin_fd) # 입력 중계 중단
            self.original_attrs = termios.tcgetattr(self.slave_fd)
            mute_attrs = list(self.original_attrs)
            mute_attrs[3] &= ~termios.ECHO
            termios.tcsetattr(self.slave_fd, termios.TCSANOW, mute_attrs) # 다시 ECHO가 꺼진 속성 적용

    async def _spawn(self) -> None:
        """자식 셸 프로세스를 생성하고 PTY 및 비동기 I/O를 설정"""
        def setup_pty():
            os.setsid()
            fcntl.ioctl(self.slave_fd, termios.TIOCSCTTY, 0)
            termios.tcsetattr(self.slave_fd, termios.TCSANOW, self.mute_attrs)

        self.proc = await asyncio.create_subprocess_exec(
            self.shell,
            *self.shell_args,
            stdin=self.slave_fd,
            stdout=self.slave_fd,
            stderr=self.slave_fd,
            env=self._environ,
            cwd=os.getcwd(),
            preexec_fn=setup_pty,
        )
        self.shell_pid = self.proc.pid
        self.shell_pgid = os.getpgid(self.shell_pid)
        self.shell_ps = psutil.Process(self.shell_pid)

        for fd in [self.stdin_fd, self.dupin_fd, self.master_fd]:
            fl = fcntl.fcntl(fd, fcntl.F_GETFL)
            fcntl.fcntl(fd, fcntl.F_SETFL, fl | os.O_NONBLOCK)

        self.cleanup_handlers.append(lambda: os.close(self.master_fd))
        self.cleanup_handlers.append(lambda: os.close(self.slave_fd))
        self.cleanup_handlers.append(lambda: os.close(self.dupin_fd))
        self.cleanup_handlers.append(lambda: os.close(self.shell_pipe))
        self.cleanup_handlers.append(lambda: os.unlink(self.shell_pipe_path))
        self.cleanup_handlers.append(
            lambda: termios.tcsetattr(
                self.stdin_fd, termios.TCSANOW, self.original_attrs
            )
        )

    async def _recover(self) -> None:
        """마커가 사라진 비정상 상태를 감지하여 셸 통합 스크립트를 재주입하는 워치독"""
        broken_count: int = 0
        recovery_threshold: int = 3
        try:
            while True:
                await self.command_start_event.wait()
                if self.continuation_active.is_set():
                    broken_count = 0
                elif self._is_standby():
                    if self.command_done_event.is_set():
                        broken_count = 0
                        self.command_start_event.clear()
                    else:
                        try:
                            buf = array.array("i", [0])
                            fcntl.ioctl(self.master_fd, termios.FIONREAD, buf)
                            bytes_available = buf[0]
                        except (OSError, BlockingIOError):
                            bytes_available = 0
                        if bytes_available > 0:
                            pass
                        else:
                            broken_count += 1
                if broken_count > recovery_threshold:
                    broken_count = 0
                    self.prompt_event.set()
                    self.command_done_event.set()
                    await self._init(b"\x03" + self.init_command.encode(self.encoder))
                await asyncio.sleep(self.recovering_tick_rate)
        except (asyncio.CancelledError, ProcessLookupError):
            return

    async def _init(self, init_command: Union[str, bytes] = b"") -> None:
        """마커 주입 및 첫 번째 프롬프트 캡처"""
        self.dupin_buffer.clear()
        await self._send(init_command)
        buffer: bytes = b""
        while True:
            ready, _, _ = select.select([self.master_fd], [], [], None)
            buffer += os.read(self.master_fd, self.chunk_size)
            if self.COMMAND_DONE in buffer:
                ready, _, _ = select.select([self.master_fd], [], [], None)
                if ready:
                    prompt = os.read(self.master_fd, self.chunk_size)
                    self.sequencer.interpret(prompt)
                break

    async def _prompt(self) -> None:
        """사용자 입력을 받고 명령어를 실행하는 메인 인터렉티브 루프"""
        def inject_typehead():
            self.session_parser.feed(typehead)
            self.session_app.key_processor.process_keys()
            self.session_app.invalidate()

        await self._init(self.init_command)
        while True:
            if self.dupin_buffer:
                typehead = self.dupin_buffer.decode(self.encoder, errors="ignore")
                self.dupin_buffer.clear()
            else:
                typehead = ""
            try:
                command = await self.session.prompt_async(pre_run=inject_typehead)
                command = command.strip()
            except KeyboardInterrupt:
                await self._exec(b"\x03\r")
                continue
            if command == "exit":
                return
            command += "\n"
            await self._exec(command.encode(self.encoder))

    async def main(self):
        """PTY 자원 확보, 시그널 등록 및 모든 비동기 태스크 시작"""
        self.master_fd, self.slave_fd = pty.openpty()
        self.dupin_fd = os.dup(self.stdin_fd)
        self.original_attrs = termios.tcgetattr(self.stdin_fd)
        self.mute_attrs = termios.tcgetattr(self.master_fd)
        self.mute_attrs[3] &= ~termios.ECHO

        os.mkfifo(self.shell_pipe_path)
        self.shell_pipe = os.open(self.shell_pipe_path, os.O_RDWR | os.O_NONBLOCK)

        tty.setraw(self.stdin_fd)
        signal.signal(signal.SIGWINCH, self._sigwinch_handler)
        self.session.app._on_resize = lambda: self._set_window_size(
            self.master_fd, *shutil.get_terminal_size()
        )

        self.loop = asyncio.get_running_loop()
        self.loop.add_reader(self.master_fd, self._display, self.master_fd)
        self.loop.add_reader(self.shell_pipe, self._update, self.shell_pipe)
        self.loop.add_signal_handler(
            signal.SIGWINCH, self._sigwinch_handler, signal.SIGWINCH, None
        )

        self.prompt_event = asyncio.Event()
        self.prompt_event.set()

        self.continuation_active = asyncio.Event()
        self.continuation_active.clear()

        self.command_start_event = asyncio.Event()
        self.command_start_event.clear()

        self.command_done_event = asyncio.Event()
        self.command_done_event.clear()

        self.sequencer = Sequencer(encoding=self.encoder)
        self.sequencer.on_sequence(self.COMMAND_START, lambda: None)
        self.sequencer.on_sequence(self.COMMAND_DONE, self.command_done_event.set)
        self.sequencer.between_sequence(
            self.BEFORE_PROMPT, self.AFTER_PROMPT, self._set_prompt
        )
        self.sequencer.between_sequence(
            self.BEFORE_CONTINUATION, self.AFTER_CONTINUATION, self._set_continuation
        )
       self.sequencer.between_sequence(
            self.AFTER_PROMPT, self.COMMAND_START, self._set_command_start
        )
       self.sequencer.between_sequence(
            self.AFTER_CONTINUATION, self.COMMAND_START, self._set_command_start
        )

        self.session_app = get_app()
        self.session_parser = Vt100Parser(feed_key_callback=self.session_app.key_processor.feed)

        self._set_window_size(self.master_fd, *shutil.get_terminal_size())
        await self._spawn()

        self.tasks = [
            asyncio.create_task(self._prompt()),
            asyncio.create_task(self._recover()),
        ]
        try:
            done, pending = await asyncio.wait(
                self.tasks, return_when=asyncio.FIRST_COMPLETED, timeout=None
            )
            for task in pending:
                task.cancel()
            await asyncio.gather(*pending, return_exceptions=True)
        except (asyncio.CancelledError, ProcessLookupError):
            pass
        finally:
            self.proc.terminate()
            for handler in self.cleanup_handlers:
                handler()

    def run(self):
        """프로그램의 최종 진입점. asyncio 이벤트 루프 실행"""
        try:
            sys.exit(asyncio.run(self.main()))
        except (ProcessLookupError, RuntimeError, Exception):
            pass
