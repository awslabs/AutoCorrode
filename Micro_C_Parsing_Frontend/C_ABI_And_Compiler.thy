theory C_ABI_And_Compiler
  imports
    "Isabelle_C.C_Main"
begin

section \<open>C-to-Core Monad Translation Infrastructure\<close>

text \<open>
  This theory defines ML infrastructure for translating Isabelle/C's parsed C11 AST
  into AutoCorrode's core monad terms. The pipeline is:
  \begin{enumerate}
    \item Parse C source via Isabelle/C (reusing the existing @{command "C"} parser)
    \item Walk the \<open>C_Ast.cTranslationUnit\<close> AST
    \item Generate Isabelle @{command definition} commands for each C function
  \end{enumerate}

  The translation is invoked via the \<open>micro_c_translate\<close> command,
  which takes a C source string and produces definitions in the local theory.
\<close>

subsection \<open>ABI Profiles\<close>

text \<open>
  Translation currently supports named ABI profiles (rather than arbitrary ABI formulas),
  so that type inference and overloaded constants remain stable. The default profile is
  @{text "lp64-le"}.

  The ABI option affects translation-time C typing (e.g. long/pointer widths and plain
  char signedness). Byte-level endianness in machine models is selected separately via
  prism overloading (for example, @{text "c_uint_byte_prism"} vs @{text "c_uint_byte_prism_be"}).
\<close>

ML \<open>
structure C_ABI : sig
  datatype profile = LP64_LE | ILP32_LE | LP64_BE | LLP64_LE | ILP32_BE
  val profile_name : profile -> string
  val parse_profile : string -> profile
  val long_bits : profile -> int
  val pointer_bits : profile -> int
  val char_is_signed : profile -> bool
  val big_endian : profile -> bool
end =
struct
  datatype profile = LP64_LE | ILP32_LE | LP64_BE | LLP64_LE | ILP32_BE

  fun profile_name LP64_LE = "lp64-le"
    | profile_name ILP32_LE = "ilp32-le"
    | profile_name LP64_BE = "lp64-be"
    | profile_name LLP64_LE = "llp64-le"
    | profile_name ILP32_BE = "ilp32-be"

  fun parse_profile s =
    let
      val normalized =
        String.map (fn c => if c = #"_" then #"-" else Char.toLower c) s
    in
      (case normalized of
         "lp64-le" => LP64_LE
       | "ilp32-le" => ILP32_LE
       | "lp64-be" => LP64_BE
       | "llp64-le" => LLP64_LE
       | "ilp32-be" => ILP32_BE
       | _ => error ("micro_c_translate: unsupported ABI profile: " ^ s ^
                     " (supported: lp64-le, ilp32-le, lp64-be, llp64-le, ilp32-be)"))
    end

  fun long_bits LP64_LE = 64
    | long_bits ILP32_LE = 32
    | long_bits LP64_BE = 64
    | long_bits LLP64_LE = 32
    | long_bits ILP32_BE = 32

  fun pointer_bits LP64_LE = 64
    | pointer_bits ILP32_LE = 32
    | pointer_bits LP64_BE = 64
    | pointer_bits LLP64_LE = 64
    | pointer_bits ILP32_BE = 32

  fun big_endian LP64_BE = true
    | big_endian ILP32_BE = true
    | big_endian _ = false

  (* NOTE: This function is NOT used by the translation pipeline.
     Plain-char signedness is controlled by C_Compiler.get_compiler_profile,
     which is set via the compiler: option (see resolve_c_type).
     This ABI-level function is retained only for the abi_char_is_signed
     metadata constant; it always returns false. *)
  fun char_is_signed _ = false
end
\<close>

ML \<open>
structure C_Compiler : sig
  datatype signed_shr_behavior = ArithmeticShift | ConservativeShift
  datatype signed_narrowing_behavior = Truncating | Checked

  type profile = {
    char_is_signed: bool,
    signed_shr: signed_shr_behavior,
    signed_narrowing: signed_narrowing_behavior
  }

  val parse_compiler : string -> profile
  val default_profile : profile
  val set_compiler_profile : profile -> unit
  val get_compiler_profile : unit -> profile
end = struct
  datatype signed_shr_behavior = ArithmeticShift | ConservativeShift
  datatype signed_narrowing_behavior = Truncating | Checked

  type profile = {
    char_is_signed: bool,
    signed_shr: signed_shr_behavior,
    signed_narrowing: signed_narrowing_behavior
  }

  (* Default: current behavior (unsigned char, arithmetic shr, truncating narrowing) *)
  val default_profile : profile = {
    char_is_signed = false,
    signed_shr = ArithmeticShift,
    signed_narrowing = Truncating
  }

  fun parse_compiler "gcc-x86_64" = {char_is_signed = true, signed_shr = ArithmeticShift, signed_narrowing = Truncating}
    | parse_compiler "clang-x86_64" = {char_is_signed = true, signed_shr = ArithmeticShift, signed_narrowing = Truncating}
    | parse_compiler "gcc-aarch64" = {char_is_signed = false, signed_shr = ArithmeticShift, signed_narrowing = Truncating}
    | parse_compiler "clang-aarch64" = {char_is_signed = false, signed_shr = ArithmeticShift, signed_narrowing = Truncating}
    | parse_compiler "conservative" = {char_is_signed = false, signed_shr = ConservativeShift, signed_narrowing = Checked}
    | parse_compiler name = error ("micro_c_translate: unknown compiler profile: " ^ name ^
        ". Known profiles: gcc-x86_64, clang-x86_64, gcc-aarch64, clang-aarch64, conservative")

  val current_compiler_profile : profile Unsynchronized.ref = Unsynchronized.ref default_profile
  fun set_compiler_profile p = (current_compiler_profile := p)
  fun get_compiler_profile () = !current_compiler_profile
end
\<close>

end
