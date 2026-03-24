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
  val is_running : unit -> bool
  val get_port : unit -> int option
  val start : int -> int * string * (unit -> unit)
  val stop : unit -> unit
  val token : unit -> string option
end;

structure Tcp_Handler : TCP_HANDLER =
struct

val handler : (string -> BinIO.outstream -> unit) Synchronized.var =
  Synchronized.var "Tcp_Handler.handler"
    (fn _ => fn out => Byte_Message.write_message_string out ["ERROR: no handler registered"]);

val server_socket : Socket.passive INetSock.stream_sock option Synchronized.var =
  Synchronized.var "Tcp_Handler.socket" NONE;

val server_token : string option Synchronized.var =
  Synchronized.var "Tcp_Handler.token" NONE;

fun token () = Synchronized.value server_token;

fun get_port () =
  Option.map (fn ssock =>
    #2 (INetSock.fromAddr (Socket.Ctl.getSockName ssock)))
  (Synchronized.value server_socket);

(* Constant-time string comparison to avoid timing side-channels.
   XORs every byte pair and ORs results together — never short-circuits. *)
fun constant_time_equal a b =
  if size a <> size b then false
  else
    let
      fun go i acc =
        if i >= size a then acc
        else go (i + 1)
          (Word8.orb (acc, Word8.xorb (
            Word8.fromInt (Char.ord (String.sub (a, i))),
            Word8.fromInt (Char.ord (String.sub (b, i))))))
    in go 0 (Word8.fromInt 0) = Word8.fromInt 0 end;

(* Generate a random hex token from /dev/urandom. *)
fun generate_token () =
  let
    val stream = BinIO.openIn "/dev/urandom"
    val bytes = BinIO.inputN (stream, 24)
    val _ = BinIO.closeIn stream
    fun byte_hex b =
      let val s = Word8.fmt StringCvt.HEX b
      in if String.size s < 2 then "0" ^ s else s end
  in String.translate (str o Char.toLower)
       (String.concat (Word8Vector.foldr (fn (b, acc) => byte_hex b :: acc) [] bytes))
  end;

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
    fun check_token () =
      case Synchronized.value server_token of
        NONE => true
      | SOME expected =>
          (case Byte_Message.read_line in_stream of
            NONE => false
          | SOME line_bytes => constant_time_equal (Bytes.content line_bytes) expected)
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
  in if check_token () then loop () else ()
  end
     handle OS.SysErr _ => ()
          | IO.Io _ => ();

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

val default_port = 9146;

fun start port =
  let (* port = 0: try default_port first, then any free port.
         port > 0: bind to that specific port.
         In both cases, actual_port is read back via getSockName. *)
      val SOME me = NetHostDB.getByName "127.0.0.1"
      val ssock : Socket.passive INetSock.stream_sock = INetSock.TCP.socket ()
      val _ = Socket.Ctl.setREUSEADDR (ssock, true)
      val _ =
        if port = 0 then
          (Socket.bind (ssock, INetSock.toAddr (NetHostDB.addr me, default_port))
           handle OS.SysErr _ =>
             Socket.bind (ssock, INetSock.toAddr (NetHostDB.addr me, 0)))
        else
          Socket.bind (ssock, INetSock.toAddr (NetHostDB.addr me, port))
      val _ = Socket.listen (ssock, 1)
      val (_, actual_port) = INetSock.fromAddr (Socket.Ctl.getSockName ssock)
      val tok = generate_token ()
      val _ = Synchronized.change server_socket (K (SOME ssock))
      val _ = Synchronized.change server_token (K (SOME tok))
      val _ = writeln ("Tcp_Handler: listening on 127.0.0.1:" ^
                        string_of_int actual_port ^ " (token " ^ quote tok ^ ")")
  in (actual_port, tok, accept_loop) end;

fun stop () =
  (Synchronized.change server_socket (fn old =>
    (case old of SOME s => (Socket.close s handle OS.SysErr _ => ()) | NONE => ();
     NONE));
   Synchronized.change server_token (K NONE));

fun is_running () = is_some (Synchronized.value server_socket);

end;
