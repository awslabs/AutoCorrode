(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Generic TCP line server with PIDE-compatible message framing.

   Listens on a localhost port, accepts concurrent connections (one
   Future.fork per connection).  For each connection, wraps the socket
   into BinIO streams (following Socket_IO) and passes them to a
   configurable handler.

   Two handler modes:
   - connection_handler (preferred): receives (in_stream, out_stream),
     manages the full connection lifecycle including the read loop.
   - handler (legacy): receives (line, out_stream) per line.

   The server knows nothing about ML evaluation, Isabelle, or output
   capture — it is a pure TCP transport. *)

signature TCP_HANDLER =
sig
  val handler : (string -> BinIO.outstream -> unit) Synchronized.var
  val connection_handler :
    (BinIO.instream -> BinIO.outstream -> unit) option Synchronized.var
  val max_connections : int Synchronized.var
  val make_streams :
    Socket.active INetSock.stream_sock -> BinIO.instream * BinIO.outstream
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

(* Per-connection handler: if set, receives (in_stream, out_stream) and
   manages the full connection lifecycle including the read loop.
   If NONE, the legacy per-line handler + built-in loop is used. *)
val connection_handler :
    (BinIO.instream -> BinIO.outstream -> unit) option Synchronized.var =
  Synchronized.var "Tcp_Handler.connection_handler" NONE;

(* Connection limit: each connection blocks a Future worker thread on I/O,
   so we cap at max_threads - 2 to leave headroom for accept_loop + evals.
   accept_loop blocks (via guarded_access) when the limit is reached. *)
val active_connections : int Synchronized.var =
  Synchronized.var "Tcp_Handler.active_connections" 0;

val max_connections : int Synchronized.var =
  Synchronized.var "Tcp_Handler.max_connections"
    (Int.max (2, Multithreading.max_threads () - 2));

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
    fun line_loop () =
      case Byte_Message.read_line in_stream of
        NONE => ()
      | SOME line_bytes =>
          let val line = Bytes.content line_bytes
          in if line = "" then line_loop ()
             else
               let val h = Synchronized.value handler
               in h line out_stream; line_loop () end
          end
  in
    if check_token () then
      case Synchronized.value connection_handler of
        SOME ch => ch in_stream out_stream
      | NONE => line_loop ()
    else ()
  end
     handle OS.SysErr _ => ()
          | IO.Io _ => ();

(* Wait until active_connections < max_connections. *)
fun await_connection_slot () =
  Synchronized.guarded_access active_connections (fn n =>
    if n < Synchronized.value max_connections
    then SOME ((), n + 1)  (* increment and proceed *)
    else NONE);            (* block until signalled *)

fun release_connection_slot () =
  Synchronized.change active_connections (fn n => Int.max (0, n - 1));

(* Accept loop: fork a Future per connection, with a connection limit
   to avoid exhausting the worker thread pool. *)
fun accept_loop () =
  case Synchronized.value server_socket of
    NONE => ()
  | SOME ssock =>
      let
        val _ = await_connection_slot ()
        val (client, _) = Socket.accept ssock
            handle OS.SysErr msg =>
              (release_connection_slot (); raise OS.SysErr msg)
      in ignore (Future.fork (fn () =>
           ((serve_client client
               handle OS.SysErr _ => ()
                    | IO.Io _ => ()
                    | Fail _ => ());
            Socket.close client handle OS.SysErr _ => ();
            release_connection_slot ())));
         accept_loop ()
      end
      handle Fail "stopped" => ()
           | OS.SysErr _ => ();

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
      val _ = Socket.listen (ssock, 16)
      val (_, actual_port) = INetSock.fromAddr (Socket.Ctl.getSockName ssock)
      val tok = generate_token ()
      val _ = Synchronized.change server_socket (K (SOME ssock))
      val _ = Synchronized.change server_token (K (SOME tok))
      val max_conn = Synchronized.value max_connections
      val _ = writeln ("Tcp_Handler: listening on 127.0.0.1:" ^
                        string_of_int actual_port ^
                        " (token " ^ quote tok ^
                        ", max " ^ string_of_int max_conn ^ " connections)")
  in (actual_port, tok, accept_loop) end;

fun stop () =
  (Synchronized.change server_socket (fn old =>
    (case old of SOME s => (Socket.close s handle OS.SysErr _ => ()) | NONE => ();
     NONE));
   Synchronized.change server_token (K NONE);
   Synchronized.change active_connections (K 0));

fun is_running () = is_some (Synchronized.value server_socket);

end;
