"""I/C REPL client — TCP connection to I/R (Isabelle/REPL)."""

import socket
import threading
from dataclasses import dataclass

SENTINEL = "<<DONE>>"

# ML evaluation noise markers — everything from the first match onward is stripped
_ML_NOISE = ["\nval it =", "\nML error", "\n[timing]"]


def strip_ml_noise(text: str) -> str:
    """Strip ML evaluator noise from Isabelle error output."""
    for marker in _ML_NOISE:
        idx = text.find(marker)
        if idx >= 0:
            text = text[:idx]
    return text.strip()


@dataclass
class MlOk:
    """ML expression evaluated successfully."""
    output: str


@dataclass
class MlError:
    """ML expression raised an exception."""
    error: str
    output: str = ""  # output printed before the exception


MlResult = MlOk | MlError


class ReplClient:
    """TCP client to I/R REPL server (repl.py)."""

    def __init__(self, host: str = "127.0.0.1", port: int = 9147,
                 token: str | None = None):
        self.host = host
        self.port = port
        self.token = token
        self.sock: socket.socket | None = None

    def connect(self) -> None:
        self.sock = socket.create_connection(
            (self.host, self.port), timeout=30)
        if self.token:
            self.sock.sendall((self.token + "\n").encode())
            # Read and discard the "OK\n" auth acknowledgment
            self.sock.settimeout(10)
            auth = self.sock.recv(256)
            if auth.strip() != b"OK":
                raise ConnectionError(
                    f"Auth failed: {auth.decode('utf-8', errors='replace').strip()}")

    def _recv(self, timeout: float) -> str:
        """Read response until <<DONE>> sentinel. Returns raw text."""
        assert self.sock is not None
        old = self.sock.gettimeout()
        self.sock.settimeout(timeout)
        try:
            buf = b""
            while True:
                chunk = self.sock.recv(8192)
                if not chunk:
                    received = buf.decode("utf-8", errors="replace").strip()
                    if received:
                        raise EOFError(
                            f"Connection closed by server. "
                            f"Last message from server: {received!r}")
                    raise EOFError(
                        "Connection closed by server with no response")
                buf += chunk
                text = buf.decode("utf-8", errors="replace")
                if SENTINEL in text:
                    return text[:text.index(SENTINEL)].strip()
        finally:
            self.sock.settimeout(old)

    def send(self, cmd: str, timeout: float = 300) -> MlResult:
        """Send ML command and parse response.

        Appends ';' for ML statement termination (I/R's TCP server
        accumulates lines until ';'). Uses ERR\\n prefix from I/R
        for error detection. For server /-commands, use send_raw().
        """
        return self.send_raw(cmd.rstrip(";") + ";", timeout=timeout)

    def send_raw(self, cmd: str, timeout: float = 300) -> MlResult:
        """Send command verbatim (no ';' appended).

        Use for server /-commands like /info that must not get ';'.
        """
        assert self.sock is not None
        self.sock.sendall((cmd.strip() + "\n").encode())
        text = self._recv(timeout)
        if text.startswith("ERR\n"):
            error_text = text[4:].strip()
            return MlError(strip_ml_noise(error_text), output=error_text)
        return MlOk(text)

    def close(self) -> None:
        if self.sock:
            self.sock.close()
            self.sock = None


class ReplPool:
    """Pool of ReplClient connections for parallel plan execution."""

    def __init__(self, host: str, port: int, token: str | None,
                 size: int):
        self._semaphore = threading.Semaphore(size)
        self._lock = threading.Lock()
        self._connections: list[ReplClient] = []
        for _ in range(size):
            conn = ReplClient(host, port, token)
            conn.connect()
            self._connections.append(conn)

    def acquire(self) -> ReplClient:
        """Block until a connection is available, then return it."""
        self._semaphore.acquire()
        with self._lock:
            return self._connections.pop()

    def release(self, conn: ReplClient) -> None:
        """Return a connection to the pool."""
        with self._lock:
            self._connections.append(conn)
        self._semaphore.release()

    def close(self) -> None:
        """Close all connections in the pool."""
        with self._lock:
            for c in self._connections:
                c.close()
            self._connections.clear()
