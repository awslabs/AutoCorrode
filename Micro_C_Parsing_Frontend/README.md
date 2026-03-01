# Micro C Parsing Frontend

This directory contains the C11-to-Core translation frontend (`micro_c_translate`, `micro_c_file`) and smoke tests.

## Command options

Supported forms:

- `micro_c_translate <c-source>`
- `micro_c_translate prefix: <decl_prefix> <c-source>`
- `micro_c_translate abi: <abi-profile> <c-source>`
- `micro_c_translate addr: <addr-ty> gv: <gv-ty> <c-source>`
- `micro_c_file <c-file>`
- `micro_c_file prefix: <decl_prefix> <c-file>`
- `micro_c_file manifest: <manifest-file> <c-file>`
- `micro_c_file abi: <abi-profile> <c-file>`
- `micro_c_file addr: <addr-ty> gv: <gv-ty> <c-file>`
- `micro_c_file` options may appear before and/or after the file argument.

Rules:

- Option keywords are exact tokens: `prefix:`, `manifest:`, `addr:`, `gv:`, `abi:`.
- Each option may appear at most once.
- `decl_prefix` defaults to `c_`.
- `abi` defaults to `lp64-le`.
- `addr:`/`gv:` default to `'addr`/`'gv`.
- Struct declarations are auto-translated into `datatype_record` declarations when field types are supported.

Supported ABI profiles:

- `lp64-le` (default)
- `ilp32-le`
- `lp64-be`

Endianness note:

- Translation-level ABI selection drives C type resolution and generated core terms.
- For byte-level memory modeling, machine-model locales must bind the matching byte prisms.
  - Little-endian: `c_*_byte_prism`
  - Big-endian: `c_*_byte_prism_be` (from `Shallow_Micro_C/C_Byte_Encoding.thy`)
- Each translation unit now also defines ABI metadata constants under its prefix:
  - `<prefix>abi_pointer_bits :: nat`
  - `<prefix>abi_long_bits :: nat`
  - `<prefix>abi_char_is_signed :: bool`
  - `<prefix>abi_big_endian :: bool`
- Use `c_endianness_of_bool` (from `Shallow_Micro_C/C_Byte_Encoding.thy`) with
  `c_*_byte_prism_of` selectors to derive prism choices from `<prefix>abi_big_endian`.

## Manifest format

The manifest is plain text with optional section headers:

```text
functions:
  mlk_barrett_reduce
  - mlk_poly_add

types:
  mlk_poly
  int16_t
```

Rules:

- Valid headers are exactly `functions:` and `types:`.
- Sections are optional.
- Entries must appear under a section header.
- Leading/trailing whitespace is ignored.
- Leading `-` on entries is optional and ignored.
- `#` starts a line comment.

## Two-phase extraction pattern

When function definitions require C-derived types to exist first, run extraction in two passes:

1. Type pass: `micro_c_file manifest: <types-manifest> ...`
2. Open locale/context with reference assumptions for those types.
3. Function pass: `micro_c_file addr: <addr-ty> gv: <gv-ty> manifest: <functions-manifest> ...`

Note: for a strict type-only pass, include a non-matching `functions:` filter in the
type manifest (for example a sentinel name) so function constants are not generated.

`C_Translation_Smoke_Options.thy` demonstrates this pattern.
