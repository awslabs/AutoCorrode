(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Generic TCP line server with PIDE-compatible message framing.

   Listens on a localhost port, accepts one connection at a time.
   For each connection, wraps the socket into BinIO streams (following
   Socket_IO) and passes them to a configurable handler.  Input is
   read line-by-line; output uses Byte_Message framing via the
   BinIO.outstream (typically through a Message_Channel).

   The handler is a Synchronized var so it can be registered after
   the structure is loaded.  The server knows nothing about ML evaluation,
   Isabelle, or output capture — it is a pure TCP transport. *)

signature TCP_HANDLER =
sig
  val handler : (string -> BinIO.outstream -> unit) Synchronized.var
  val start : int -> (unit -> unit)
  val stop : unit -> unit
end;

structure Tcp_Handler : TCP_HANDLER =
struct

val handler : (string -> BinIO.outstream -> unit) Synchronized.var =
  Synchronized.var "Tcp_Handler.handler"
    (fn _ => fn out => Byte_Message.write_message_string out ["ERROR: no handler registered"]);

val server_socket : Socket.passive INetSock.stream_sock option Synchronized.var =
  Synchronized.var "Tcp_Handler.socket" NONE;

(* Wrap an accepted socket into BinIO streams, following Socket_IO.make_streams. *)
fun make_streams socket =
  let
    val buffer_size = 65536;
    val rd =
      BinPrimIO.RD {
        name = "tcp_client_in",
        chunkSize = buffer_size,
        readVec = SOME (fn n => Socket.recvVec (socket, n)),
        readArr = SOME (fn buffer => Socket.recvArr (socket, buffer)),
        readVecNB = NONE, readArrNB = NONE,
        block = NONE, canInput = NONE, avail = fn () => NONE,
        getPos = NONE, setPos = NONE, endPos = NONE, verifyPos = NONE,
        close = fn () => Socket.close socket handle OS.SysErr _ => (),
        ioDesc = NONE
      };
    val wr =
      BinPrimIO.WR {
        name = "tcp_client_out",
        chunkSize = buffer_size,
        writeVec = SOME (fn buffer => Socket.sendVec (socket, buffer)),
        writeArr = SOME (fn buffer => Socket.sendArr (socket, buffer)),
        writeVecNB = NONE, writeArrNB = NONE,
        block = NONE, canOutput = NONE,
        getPos = NONE, setPos = NONE, endPos = NONE, verifyPos = NONE,
        close = fn () => Socket.close socket handle OS.SysErr _ => (),
        ioDesc = NONE
      };
    val in_stream =
      BinIO.mkInstream (BinIO.StreamIO.mkInstream (rd, Word8Vector.fromList []));
    val out_stream =
      BinIO.mkOutstream (BinIO.StreamIO.mkOutstream (wr, IO.BLOCK_BUF));
  in (in_stream, out_stream) end;

(* Serve one client connection. *)
fun serve_client socket =
  let
    val (in_stream, out_stream) = make_streams socket
    fun loop () =
      case Byte_Message.read_line in_stream of
        NONE => ()
      | SOME line_bytes =>
          let val line = Bytes.content line_bytes
          in if line = "" then loop ()
             else
               let val h = Synchronized.value handler
               in h line out_stream; loop () end
          end
  in loop ()
     handle OS.SysErr _ => ()
          | IO.Io _ => ()
  end;

(* Accept loop: one client at a time until socket is closed. *)
fun accept_loop () =
  case Synchronized.value server_socket of
    NONE => ()
  | SOME ssock =>
      let val (client, _) = Socket.accept ssock
              handle OS.SysErr _ => raise Fail "stopped"
      in (serve_client client;
          Socket.close client handle OS.SysErr _ => ();
          accept_loop ())
         handle Fail "stopped" => ()
      end;

fun start port =
  let val SOME me = NetHostDB.getByName "127.0.0.1"
      val addr = INetSock.toAddr (NetHostDB.addr me, port)
      val ssock : Socket.passive INetSock.stream_sock = INetSock.TCP.socket ()
      val _ = Socket.Ctl.setREUSEADDR (ssock, true)
      val _ = Socket.bind (ssock, addr)
      val _ = Socket.listen (ssock, 1)
      val _ = Synchronized.change server_socket (K (SOME ssock))
      val _ = writeln ("Tcp_Handler: listening on 127.0.0.1:" ^ string_of_int port)
  in accept_loop end;

fun stop () =
  Synchronized.change server_socket (fn old =>
    (case old of SOME s => (Socket.close s handle OS.SysErr _ => ()) | NONE => ();
     NONE));

end;
