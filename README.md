![CI](https://github.com/awslabs/AutoCorrode/actions/workflows/ci.yml/badge.svg) [![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# AutoCorrode

AutoCorrode provides infrastructure for reasoning about imperative programs in Isabelle/HOL. It supports classical and separation logic and includes configurable and scalable custom automation, written in Standard ML. The core of AutoCorrode is language-agnostic, but particular emphasis placed on a Rust-dialect called µRust.

AutoCorrode gets its name as the little rusty brother of the independent C verification framework [AutoCorres](https://github.com/seL4/l4v/tree/master/tools/autocorres) for Isabelle/HOL.

## Showcase

The [Showcase.thy](Micro_Rust_Examples/Showcase.thy) file provides a small tour of AutoCorrode's basic concepts and features. It defines several (simple) functions in µRust, defines contracts for them, then uses the provided automation to verify that the functions satisfy their contracts.

## Browsing the source

An HTML rendering of the AutoCorrode source code is available [here](https://awslabs.github.io/AutoCorrode/AutoCorrode.html).

## Setup

AutoCorrode requires Isabelle2025, which can be downloaded [here](https://isabelle.in.tum.de/website-Isabelle2025/). Set `ISABELLE_HOME` to the directory containing the `isabelle` binary.

AutoCorrode also requires the [WordLib](https://www.isa-afp.org/entries/Word_Lib.html) AFP entry. Set `AFP_COMPONENT_BASE` to the directory contaning the `Word_Lib` directory. By default, AutoCorrode expects it to be located in [dependencies/afp-2025](dependencies/afp-2025).

## Usage

You can interactively explore AutoCorrode using `make jedit`, which opens the AutoCorrode source in the Isabelle/jEdit GUI.

To non-interactively check all material in AutoCorrode, run `make build`, which starts a batch-build in Isabelle.

## Citing AutoCorrode

If you want to cite AutoCorrode, consider using the following BibTeX entry:

```
@misc{AutoCorrode,
   author = "Becker, Hanno and Chong, Nathan and Dockins, Robert and Grundy, Jim and Hu, Jason Z. S. and Mulder, Ike and Mulligan, Dominic P. and Mure, Paul and Paulson, Lawrence C. and Slind, Konrad",
   title = "{AutoCorrode} software verification framework for {Isabelle/HOL}",
   year = "2025",
   howpublished = "\url{https://github.com/awslabs/autocorrode}"
}
```

## Sessions

The following gives a brief overview over the Isabelle sessions contained in AutoCorrode.

### Shallow_Micro_Rust

This session defines the "µRust monad" for modelling imperative computations in Isabelle/HOL. Despite its name and primary purpose as the target of the shallow embedding of µRust into Isabelle/HOL, the monad is quite generic and likely suitable for the modelling of other imperative languages as well. Concretely, the µRust monad is an inductive monad with support for exceptions, functions, and yields/prompts (similar to interaction trees).

### Shallow_Separation_Logic

This session defines basic notions of separation logic. It also defines Hoare triples for the µRust Monad and derives a weakest precondition calculus. Automatic reasoning within that calculus is the primary purpose of [Crush](Crush).

### Separation_Lenses

Separation lenses facilitate the extension of locale interpretations from smaller to larger separation algebras. They allow for the construction of separation algebras implementing a series of interfaces by constructing individual interface interpretations on minimal separation algebras first, and 'glueing' them together by means of the separation lens formalism. Without separation lenses, a large amount of boilerplate would be required.

Concretely, a separation lens is an axiomatization of the projection of product separation algebra onto one of its factors. The axioms are strong enough to enable the extension of µRust programs and their separation logic specifications and proofs along separation lenses.

### Lenses_And_Other_Optics

This session defines and elaborates the concepts of lenses, prisms and foci. Foci are used in AutoCorrode as an axiomatization of the relation between the 'raw' values in a monomorphic store, and the interpretations of those raw values in concrete types.

In a nutshell, a lens is a quotient type (e.g. a record projection), a prism is a subtype (e.g. a branch of an inductive type), and a focus is a subquotient --- the concept emerging from lenses and prisms when requiring compositionality.

Foci are mainly used in AutoCorrode's model of reference: The value behind a raw/untyped reference is a 'raw' value in some fixed monomorphic store, and typing a reference amounts to providing a focus from that raw 'global value type' to the desired 'local' type. This generality allows for representation-agnostic reasoning about references: References can either be implemented as being backed by an abstract heap, where the global value type is the disjoint union of all local value types; or as being backed by a byte-level memory, where the global value type is the type of byte lists, and foci capture pairs of decoding/encoding functions between byte sequences and concrete types.

### Crush

Crush is a family of highly customizable and scalable tactics for reasoning in separation logic. See [Micro_Rust_Examples/Crush_Examples.thy](Micro_Rust_Examples/Crush_Examples.thy) for an introduction.

### Autogen

Autogen facilitates pure reasoning about functions on records: Users can annotate functions with their footprint -- the set of record fields they depend on -- and have footprint-based commutativity relations derived automatically.

### Byte_Level_Encoding

This session provides encoding/decoding functions for basic types to/from byte lists, expressed in the formalism of Foci/Optics.

### Micro_Rust_Examples

This session contains documentation and examples illustrating how to use AutoCorrode for reasoning about the Rust-like "µRust" language.

### Micro_Rust_Interfaces[_Core]

This session define locales for modelling the verification context. For example, [References.thy](Micro_Rust_Interfaces_Core/References.thy) defines the `Reference` locale which provides axioms for reasoning about references and mutable local variables in µRust. It also defines "transfer locales" which use separation lenses (see Optics, above) to extend interpretations of the interface locales to larger separation algebras.

### Micro_Rust_Parsing_Frontend

A shallow embedding of µRust into Isabelle/HOL. A custom syntax category for µRust is defined together with a 'shallow embedded bracket' mapping this syntax to a the embedding of µRust in HOL defined in [Shallow_Micro_Rust](Shallow_Micro_Rust).

### Micro_Rust_Runtime

This session provides concrete interpretations for the locales defined in [Micro_Rust_Interfaces](Micro_Rust_Interfaces) and [Micro_Rust_Interfaces_Core](Micro_Rust_Interfaces_Core), including abstract and byte-level implementations of the  `Reference` locale.

### Micro_Rust_Std_Lib

Specifications and proofs for common µRust operations.

### Data_Structures

This session contains various efficient data structures.

### Misc

A collection of miscellaneous lemmas about lists, arrays, sets, vectors, and words.
