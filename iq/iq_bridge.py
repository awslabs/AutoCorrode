#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT
"""
MCP Bridge for Isabelle with automatic reconnection.
Reconnects to server when connection is lost and new queries come in.
"""

import sys
import json
import socket
import time
import os
from typing import Dict, Any, Optional, List

class MCPBridgeWithReconnect:
    _MAX_REQUEST_TIMEOUT_SEC = 3600.0
    _REQUEST_TIMEOUT_GRACE_SEC = 5.0

    def __init__(self):
        self.isabelle_socket = None
        self.connected = False
        self.last_forward_error: Optional[str] = None
        token = os.environ.get("IQ_MCP_AUTH_TOKEN", "").strip()
        self.auth_token = token if token else None
        self.server_host = os.environ.get("IQ_MCP_BRIDGE_HOST", "localhost").strip() or "localhost"
        self.server_port = self._parse_positive_int_env("IQ_MCP_BRIDGE_PORT", 8765)
        self.response_timeout_sec = float(self._parse_positive_int_env("IQ_MCP_BRIDGE_RESPONSE_TIMEOUT_SEC", 30))
        self.log_max_bytes = self._parse_non_negative_int_env("IQ_MCP_BRIDGE_LOG_MAX_BYTES", 5 * 1024 * 1024)
        self.log_file = os.environ.get(
            "IQ_MCP_BRIDGE_LOG_FILE",
            os.path.join(os.path.dirname(os.path.abspath(__file__)), "bridge_log.txt"),
        )
        self._recv_buffer = b""
        self._response_queue: List[Dict[str, Any]] = []

    def _set_forward_error(self, message: str) -> None:
        self.last_forward_error = message.strip() if message else None

    def _clear_forward_error(self) -> None:
        self.last_forward_error = None

    def _format_request_label(self, request: Dict[str, Any]) -> str:
        method = request.get("method", "unknown")
        if method == "tools/call":
            params = request.get("params", {})
            if isinstance(params, dict):
                tool_name = params.get("name")
                if isinstance(tool_name, str) and tool_name.strip():
                    return f"{method} (tool={tool_name.strip()})"
        return method

    def _forward_failure_message(self, request: Dict[str, Any]) -> str:
        request_label = self._format_request_label(request)
        detail = (self.last_forward_error or "").strip()
        if detail:
            return f"Failed to forward {request_label} to Isabelle server: {detail}"
        return f"Failed to forward {request_label} to Isabelle server"

    def _parse_positive_int_env(self, name: str, default: int) -> int:
        raw = os.environ.get(name, "").strip()
        if not raw:
            return default
        try:
            parsed = int(raw)
            return parsed if parsed > 0 else default
        except ValueError:
            return default

    def _parse_non_negative_int_env(self, name: str, default: int) -> int:
        raw = os.environ.get(name, "").strip()
        if not raw:
            return default
        try:
            parsed = int(raw)
            return parsed if parsed >= 0 else default
        except ValueError:
            return default

    def _coerce_positive_number(self, value: Any) -> Optional[float]:
        if isinstance(value, bool):
            return None
        if isinstance(value, (int, float)):
            return float(value) if value > 0 else None
        if isinstance(value, str):
            raw = value.strip()
            if not raw:
                return None
            try:
                parsed = float(raw)
                return parsed if parsed > 0 else None
            except ValueError:
                return None
        return None

    def _effective_response_timeout_sec(self, request: Dict[str, Any]) -> float:
        """Use request-level timeout hints when available (expressed in milliseconds)."""
        base_timeout_sec = float(self.response_timeout_sec)
        if not isinstance(request, dict):
            return base_timeout_sec

        if request.get("method") != "tools/call":
            return base_timeout_sec

        params = request.get("params")
        if not isinstance(params, dict):
            return base_timeout_sec
        arguments = params.get("arguments")
        if not isinstance(arguments, dict):
            return base_timeout_sec

        timeout_candidates_ms: List[float] = []
        for key in ("timeout", "timeout_ms", "timeout_per_command", "timeout_per_command_ms"):
            parsed = self._coerce_positive_number(arguments.get(key))
            if parsed is not None:
                timeout_candidates_ms.append(parsed)

        if not timeout_candidates_ms:
            return base_timeout_sec

        requested_sec = (max(timeout_candidates_ms) / 1000.0) + self._REQUEST_TIMEOUT_GRACE_SEC
        return min(max(base_timeout_sec, requested_sec), self._MAX_REQUEST_TIMEOUT_SEC)

    def _rotate_log_if_needed(self) -> None:
        if self.log_max_bytes <= 0:
            return
        try:
            if os.path.exists(self.log_file) and os.path.getsize(self.log_file) >= self.log_max_bytes:
                rotated = self.log_file + ".1"
                if os.path.exists(rotated):
                    os.remove(rotated)
                os.replace(self.log_file, rotated)
        except Exception:
            pass

    def log(self, message: str):
        """Log messages to stderr and file with timestamp."""
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        log_message = f"{timestamp} [MCP-Bridge] {message}"

        # Log to stderr
        print(log_message, file=sys.stderr, flush=True)

        # Also log to file
        try:
            self._rotate_log_if_needed()
            with open(self.log_file, "a", encoding="utf-8") as f:
                f.write(log_message + "\n")
                f.flush()
        except Exception:
            pass  # Don't let logging errors break the bridge

    def connect_to_isabelle(self) -> bool:
        """Connect to the Isabelle MCP server."""
        try:
            if self.isabelle_socket:
                try:
                    self.isabelle_socket.close()
                except:
                    pass

            self.isabelle_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.isabelle_socket.settimeout(self.response_timeout_sec)
            self.isabelle_socket.connect((self.server_host, self.server_port))
            self.connected = True
            self._recv_buffer = b""
            self._response_queue = []
            self.log(
                f"Connected to Isabelle MCP server at {self.server_host}:{self.server_port} "
                f"(response timeout: {self.response_timeout_sec:.0f}s)"
            )
            return True

        except Exception as e:
            self.log(f"Connection failed: {e}")
            self._set_forward_error(
                f"cannot connect to {self.server_host}:{self.server_port} ({e})"
            )
            self.connected = False
            if self.isabelle_socket:
                try:
                    self.isabelle_socket.close()
                except:
                    pass
                self.isabelle_socket = None
            self._recv_buffer = b""
            self._response_queue = []
            return False

    def ensure_connection(self) -> bool:
        """Ensure we have a working connection, reconnecting if necessary."""
        if self.connected and self.isabelle_socket:
            return True

        self.log("Connection lost, attempting to reconnect...")
        return self.connect_to_isabelle()

    def forward_to_isabelle(self, request: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """Forward request to Isabelle server with automatic reconnection."""
        if self.auth_token and "auth_token" not in request:
            request["auth_token"] = self.auth_token

        method = request.get('method', 'unknown')

        # Check if this is a notification (no 'id' field)
        is_notification = 'id' not in request

        # Ensure we have a connection
        if not self.ensure_connection():
            self.log(f"Cannot establish connection - cannot forward {method}")
            return None

        try:
            # Send request
            request_str = json.dumps(request)
            payload = (request_str + "\n").encode()
            if hasattr(self.isabelle_socket, "sendall"):
                self.isabelle_socket.sendall(payload)
            else:
                self.isabelle_socket.send(payload)

            # For notifications, don't wait for response
            if is_notification:
                self.log(f"Forwarded notification {method} (no response expected)")
                return None

            # For requests, read the matching framed JSON line (newline-delimited JSON),
            # while preserving additional complete messages for later.
            request_id = request.get("id")
            response_timeout_sec = self._effective_response_timeout_sec(request)
            self.log(
                f"Waiting up to {int(max(1.0, response_timeout_sec))}s for {self._format_request_label(request)} "
                f"(id={request_id})"
            )
            parsed_response = self._read_response_for_id(method, request_id, response_timeout_sec)
            if parsed_response is None:
                return None
            self._clear_forward_error()
            self.log(f"Successfully forwarded {method}")
            return parsed_response

        except Exception as e:
            self.log(f"Error forwarding {method}: {e}")
            self._set_forward_error(str(e))
            self.connected = False
            return None

    def _extract_complete_messages(self, method: str) -> bool:
        """
        Extract complete newline-delimited JSON messages from the receive buffer.
        Returns False on parse/decoding errors, True otherwise.
        """
        while b"\n" in self._recv_buffer:
            raw_line, self._recv_buffer = self._recv_buffer.split(b"\n", 1)
            line = raw_line.strip()
            if not line:
                continue
            try:
                decoded = line.decode("utf-8")
                parsed = json.loads(decoded)
                if isinstance(parsed, dict):
                    self._response_queue.append(parsed)
                else:
                    self.log(f"Ignoring non-object JSON response for {method}: {decoded[:200]}")
            except (UnicodeDecodeError, json.JSONDecodeError) as e:
                self.log(f"Response decode error for {method}: {e}")
                self._set_forward_error(
                    f"invalid JSON response from Isabelle server ({e})"
                )
                return False
        return True

    def _pop_matching_response(self, request_id: Any) -> Optional[Dict[str, Any]]:
        """Pop the first queued response with a matching JSON-RPC id."""
        for idx, response in enumerate(self._response_queue):
            if response.get("id") == request_id:
                return self._response_queue.pop(idx)
        return None

    def _read_response_for_id(self, method: str, request_id: Any, response_timeout_sec: float) -> Optional[Dict[str, Any]]:
        """Read a parsed response with matching JSON-RPC id from the Isabelle socket."""
        deadline = time.time() + max(1.0, response_timeout_sec)
        while True:
            queued = self._pop_matching_response(request_id)
            if queued is not None:
                return queued

            if time.time() >= deadline:
                self.log(f"Timed out waiting for response to {method} (id={request_id})")
                self._set_forward_error(
                    f"timed out waiting for Isabelle server response after {int(max(1.0, response_timeout_sec))}s; "
                    "consider increasing the tool timeout argument and/or IQ_MCP_BRIDGE_RESPONSE_TIMEOUT_SEC"
                )
                self.connected = False
                return None

            try:
                chunk = self.isabelle_socket.recv(4096)
            except socket.timeout:
                continue
            if not chunk:
                self.log(f"No response for {method} - connection closed")
                self._set_forward_error("connection closed by Isabelle server")
                self.connected = False
                return None

            self._recv_buffer += chunk
            if not self._extract_complete_messages(method):
                self.connected = False
                return None

    def create_error_response(self, request_id: Any, code: int, message: str) -> Dict[str, Any]:
        """Create a standard JSON-RPC error response."""
        return {
            "jsonrpc": "2.0",
            "id": request_id,
            "error": {
                "code": code,
                "message": message
            }
        }

    def run(self):
        """Main bridge loop with automatic reconnection."""
        self.log("Starting MCP bridge for Isabelle with automatic reconnection")

        # Initial connection attempt
        if not self.connect_to_isabelle():
            self.log("Failed to establish initial connection - will retry on first request")
        else:
            self.log("Bridge ready with initial connection")

        try:
            for line in sys.stdin:
                line = line.strip()
                if not line:
                    continue

                try:
                    request = json.loads(line)
                    method = request.get("method", "unknown")
                    request_id = request.get("id")
                    is_notification = 'id' not in request

                    # Forward to Isabelle server (with automatic reconnection)
                    response = self.forward_to_isabelle(request)

                    if response:
                        # Send response back to client
                        response_str = json.dumps(response)
                        print(response_str, flush=True)
                        self.log(f"Response sent for {method}")
                    elif is_notification:
                        # No response expected for notifications
                        self.log(f"Notification {method} processed (no response)")
                    else:
                        # Send error if forwarding failed for a request
                        error_response = self.create_error_response(
                            request_id, -32603, self._forward_failure_message(request)
                        )
                        print(json.dumps(error_response), flush=True)
                        self.log(f"Error response sent for {method}")

                except json.JSONDecodeError as e:
                    self.log(f"JSON parse error: {e}")
                    error_response = self.create_error_response(
                        None, -32700, f"Parse error: {e}"
                    )
                    print(json.dumps(error_response), flush=True)

        except KeyboardInterrupt:
            self.log("Bridge interrupted")
        except Exception as e:
            self.log(f"Unexpected error in bridge: {e}")
        finally:
            if self.isabelle_socket:
                try:
                    self.isabelle_socket.close()
                except:
                    pass
            self.log("Bridge shutdown complete")

if __name__ == "__main__":
    bridge = MCPBridgeWithReconnect()
    bridge.run()
