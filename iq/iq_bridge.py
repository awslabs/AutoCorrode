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
    def __init__(self):
        self.isabelle_socket = None
        self.connected = False
        token = os.environ.get("IQ_MCP_AUTH_TOKEN", "").strip()
        self.auth_token = token if token else None
        self._recv_buffer = b""
        self._response_queue: List[Dict[str, Any]] = []

    def log(self, message: str):
        """Log messages to stderr and file with timestamp."""
        timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
        log_message = f"{timestamp} [MCP-Bridge] {message}"

        # Log to stderr
        print(log_message, file=sys.stderr, flush=True)

        # Also log to file
        try:
            import os
            script_dir = os.path.dirname(os.path.abspath(__file__))
            log_file = os.path.join(script_dir, "bridge_log.txt")
            with open(log_file, "a") as f:
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
            self.isabelle_socket.connect(('localhost', 8765))
            self.connected = True
            self._recv_buffer = b""
            self._response_queue = []
            self.log("Connected to Isabelle MCP server")
            return True

        except Exception as e:
            self.log(f"Connection failed: {e}")
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
            self.isabelle_socket.send((request_str + "\n").encode())

            # For notifications, don't wait for response
            if is_notification:
                self.log(f"Forwarded notification {method} (no response expected)")
                return None

            # For requests, read one framed JSON line (newline-delimited JSON),
            # while preserving any additional complete messages for later.
            parsed_response = self._read_one_response(method)
            if parsed_response is None:
                return None
            self.log(f"Successfully forwarded {method}")
            return parsed_response

        except Exception as e:
            self.log(f"Error forwarding {method}: {e}")
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
                return False
        return True

    def _read_one_response(self, method: str) -> Optional[Dict[str, Any]]:
        """Read exactly one parsed response message from the Isabelle socket."""
        while True:
            if self._response_queue:
                return self._response_queue.pop(0)

            chunk = self.isabelle_socket.recv(4096)
            if not chunk:
                self.log(f"No response for {method} - connection closed")
                self.connected = False
                return None

            self._recv_buffer += chunk
            if not self._extract_complete_messages(method):
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
                        # Ensure response has correct ID
                        response["id"] = request_id

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
                            request_id, -32603, f"Failed to forward {method} to Isabelle server"
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
