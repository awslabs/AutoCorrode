theory Tutorial_Context
  imports Slides
begin

slide \<open>Context: AutoCorrode\<close>

text \<open>\<^bold>\<open>AutoCorrode\<close> provides verification infrastructure for reasoning
about imperative programs in Isabelle/HOL. Among many other things, it
encompasses:\<close>

text \<open>
\<^item> A formalization of \<^bold>\<open>Separation Logic\<close>
\<^item> A shallow embedding of a Rust dialect, \<open>\<mu>\<close>Rust, as a monad into Isabelle/HOL
\<^item> A \<^bold>\<open>weakest-precondition calculus\<close> for reasoning about \<open>\<mu>\<close>Rust in SL
\<^item> Extensible, scalable proof automation (\<open>crush\<close>)
\<^item> AI \<open>\<leftrightarrow>\<close> Isabelle integration tools (I/Q, I/R, I/P, I/C)
\<^item> Abstract interfaces for references
\<^item> Abstract \<^emph>\<open>and\<close> byte-accurate models of references
\<^item> A ``poor-man's separation logic'' for footprint reasoning in pure HOL
\<^item> \dots
\<close>

text \<open>\<^bold>\<open>This talk covers a small slice\<close> -- enough of the foundations
  (monads, Hoare/WP, separation logic) to read AutoCorrode source.\<close>

end_slide

slide \<open>AutoCorrode at a glance: session structure\<close>

text \<open>Where the pieces live in the upstream tree (arrows = depends on):\<close>

text_raw \<open>
\begin{center}
\begin{tikzpicture}[
  >={Stealth[length=1.6mm]},
  thick,
  every node/.style={font=\tiny\sffamily, draw, rounded corners=1pt,
                     inner sep=2pt, fill=white},
  hi/.style={fill=blue!15},
  arr/.style={->, gray!60!black},
  node distance=2mm and 4mm
]
% Layer 0
\node (DS)    {Data\_Structures};
\node (Misc)  [right=of DS]    {Misc};
\node (Lens)  [right=of Misc]  {Lenses\_And\_Other\_Optics};
\node (PF)    [right=of Lens]  {Micro\_Rust\_Parsing\_Frontend};
% Layer 1
\node (BE)    [above=of Misc]  {Byte\_Level\_Encoding};
\node (Auto)  [above=of Lens, xshift=14mm]  {Autogen};
% Layer 2 — central
\node[hi] (SMR)   [above=of Auto]  {Shallow\_Micro\_Rust};
% Layer 3
\node[hi] (SSL)   [above=of SMR]   {Shallow\_Separation\_Logic};
\node (SLens) [right=of SSL]   {Separation\_Lenses};
\node (MIC)   [left=of SSL]    {Micro\_Rust\_Interfaces\_Core};
% Layer 4
\node[hi] (Crush) [above=of SSL]   {Crush};
\node (Std)   [right=of Crush] {Micro\_Rust\_Std\_Lib};
% Layer 5
\node (MI)    [above=of Std]   {Micro\_Rust\_Interfaces};
% Layer 6
\node (MR)    [above=of MI]    {Micro\_Rust\_Runtime};
% Layer 7
\node (Ex)    [above=of MR]    {Micro\_Rust\_Examples};

% Edges (orthogonal routing only -- no diagonals)
\tikzset{ortho/.style={arr, rounded corners=2pt}}
% Same-row / same-column edges
\draw[arr] (DS)    -- (Misc);
\draw[arr] (Misc)  -- (Lens);
\draw[arr] (Lens)  -- (Auto);
\draw[arr] (Misc)  -- (BE);
\draw[arr] (Auto)  -- (SMR);
\draw[arr] (Lens)  -- (SMR);
\draw[arr] (SMR)   -- (SSL);
\draw[arr] (SSL)   -- (SLens);
\draw[arr] (SSL)   -- (MIC);
\draw[arr] (SSL)   -- (Crush);
\draw[arr] (Crush) -- (Std);
\draw[arr] (Std)   -- (MI);
\draw[arr] (MI)    -- (MR);
\draw[arr] (MR)    -- (Ex);
% Off-grid edges, routed vertical-then-horizontal
\draw[ortho] (Lens.north) |- (BE.east);
\draw[ortho] (PF.north)   |- (SMR.east);
\draw[ortho] (MIC.north)  |- (Crush.west);
\draw[ortho] (Crush.north) |- (MI.west);
% Crush -> Ex: up then right
\draw[ortho] (Crush.north) |- (Ex.west);
% BE -> MR: route well around the LEFT, outside the whole node cluster
\draw[ortho]
  (BE.west) -- ++(-15mm,0) |- (MR.west);
\end{tikzpicture}
\end{center}
\<close>

end_slide

end
