(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Generic TCP server with PIDE-compatible message framing.

   Listens on a localhost port, accepts multiple concurrent connections.
   For each connection, wraps the socket into BinIO streams (following
   Socket_IO) and passes them to a configurable handler.

   Input uses Byte_Message framing: each message has exactly two chunks,
   a request identifier and the command string.  Output uses Byte_Message
   framing via the BinIO.outstream (typically through a Message_Channel).

   The handler is a Synchronized var so it can be registered after
   the structure is loaded.  The server knows nothing about ML evaluation,
   Isabelle, or output capture — it is a pure TCP transport. *)

signature TCP_HANDLER =
sig
  val handler : ((string * string) -> (string -> Properties.T -> XML.body list -> unit) -> unit) Synchronized.var
  val is_running : unit -> bool
  val start : int -> (unit -> unit)
  val stop : unit -> unit
end;

structure Tcp_Handler : TCP_HANDLER =
struct

val handler : ((string * string) -> (string -> Properties.T -> XML.body list -> unit) -> unit) Synchronized.var =
  Synchronized.var "Tcp_Handler.handler"
    (fn _ => fn msg => msg Markup.errorN [] [XML.blob ["ERROR: no handler registered"]]);

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

(* Serve one client connection: read framed messages, dispatch to handler. *)
fun serve_client socket =
  let
    val (in_stream, out_stream) = make_streams socket
    val channel = Message_Channel.make out_stream
    val message = Message_Channel.message channel
    fun loop () =
      case Byte_Message.read_message in_stream of
        NONE => ()
      | SOME [request_id_bytes, command_bytes] =>
          let val request_id = Bytes.content request_id_bytes
              val command = Bytes.content command_bytes
              val h = Synchronized.value handler
          in ignore (Future.fork (fn () => h (request_id, command) message));
             loop ()
          end
      | SOME _ =>
          (message Markup.errorN [] [XML.blob ["expected exactly 2 chunks (request_id, command)"]];
           loop ())
  in loop ()
     handle OS.SysErr _ => ()
          | IO.Io _ => ();
     Message_Channel.shutdown channel
  end;

(* Accept loop: one connection at a time until socket is closed. *)
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

fun is_running () = is_some (Synchronized.value server_socket);

end;
