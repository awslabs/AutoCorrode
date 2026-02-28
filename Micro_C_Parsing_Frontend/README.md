# Micro C Parsing Frontend

This directory contains the C11-to-Core translation frontend (`micro_c_translate`, `micro_c_file`) and smoke tests for parser/translation behavior.

## Command options

- `micro_c_translate <c-source>`
- `micro_c_translate prefix: <decl_prefix> <c-source>`
- `micro_c_file <c-file>`
- `micro_c_file prefix: <decl_prefix> <c-file>`
- `micro_c_file prefix: <decl_prefix> manifest: <manifest-file> <c-file>`
- `micro_c_file <c-file> prefix: <decl_prefix>`
- `micro_c_file <c-file> manifest: <manifest-file>`

Rules:

- Option keywords are exact tokens: `prefix:` and `manifest:`.
- For `micro_c_file`, options may appear before and/or after the file argument.
- Each option may appear at most once.
- `decl_prefix` defaults to `c_`.
- Struct declarations are auto-translated into corresponding `datatype_record` declarations when field types are supported.

## Manifest format

The manifest is plain text with section headers:

```text
functions:
  mlk_barrett_reduce
  - mlk_poly_add
  mlk_poly_sub

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
