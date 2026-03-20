# AFP dependencies

AutoCorrode depends on the following AFP entries. Download and unpack them here.
If they are located in a different directory, set the `AFP_COMPONENT_BASE` environment variable accordingly.

- [Word_Lib](https://www.isa-afp.org/entries/Word_Lib.html) — word-level operations and bit manipulation
- [Isabelle_C](https://www.isa-afp.org/entries/Isabelle_C.html) — C11 parser front-end (required for Micro C sessions)

## Required patch: Isabelle_C

The upstream AFP Isabelle_C has a bug in `C_Parser_Language.thy` where
`transformDeclaration` errors on function parameter declarations with 3+
type specifiers (e.g. `unsigned long long`). A patch is provided at
`.github/patches/isabelle_c_parser_language.patch`. Apply it to your
Isabelle_C installation:

```bash
cd path/to/Isabelle_C
git apply path/to/AutoCorrode/.github/patches/isabelle_c_parser_language.patch
```

CI applies this patch automatically via the setup-isabelle-action.