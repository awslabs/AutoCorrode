theory Tutorial_Preamble
  imports
    Slides
    Micro_Rust_Examples.Linked_List
begin

slide \<open>About these slides\<close>

text_raw \<open>\begin{center}\itshape
These slides are as much a talk as an experimentation ground.
\end{center}\<close>

text \<open>Every slide in this deck is generated from a formally-checked
  Isabelle/HOL theory file. Definitions, types, lemmas, and proofs
  shown here are \<^bold>\<open>live\<close>: they were type-checked at build time and
  the slide will not compile if a referenced fact stops being true.

  The sources live next to this PDF, organised one theory per
  topic (\<open>Tutorial_Glossary.thy\<close>, \<open>Tutorial_Monads.thy\<close>, etc.).

  Open them in jEdit (\<^verbatim>\<open>make jedit\<close>) to step through every
  proof, inspect intermediate goal states, and experiment with
  variants.\<close>

text \<open>\<^bold>\<open>Task for \<^emph>\<open>you\<close>:\<close> open the sources, change a
  definition or a contract, and watch which proofs still go through
  -- and which break, and why. That is the fastest way to build a
  feel for the machinery.\<close>

end_slide

end
