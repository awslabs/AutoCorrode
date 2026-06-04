theory Slides
  imports Pure
  keywords "slide" :: document_raw
       and "end_slide" :: document_raw
       and "interlude" :: document_raw
       and "end_interlude" :: document_raw
begin

text \<open>
  \<^bold>\<open>Slide outer-syntax commands.\<close>

  This theory adds two top-level commands so that an \<^verbatim>\<open>.thy\<close> file can
  drive a beamer slide deck through Isabelle's document preparation system.

  \<^item> \<^verbatim>\<open>slide \<open>Title\<close>\<close> emits a literal \<^verbatim>\<open>\begin{frame}[fragile]{Title}\<close>.

  \<^item> \<^verbatim>\<open>end_slide\<close> emits a literal \<^verbatim>\<open>\end{frame}\<close>.

  Use them as a balanced pair around each slide's content:
  \begin{quote}\<^verbatim>\<open>
    slide \<open>Outline\<close>
      text \<open>...\<close>
    end_slide
  \<close>\end{quote}

  \<^bold>\<open>Why two commands and not one?\<close>  Beamer's \<^verbatim>\<open>frame\<close> environment scans
  for a \<^bold>\<open>literal\<close> \<^verbatim>\<open>\end{frame}\<close> token in the source -- macros are not
  expanded during the scan, so the close cannot be hidden behind an
  \<^verbatim>\<open>\isamarkupslide\<close>-style macro.  Both ends must therefore appear in
  the generated \<^verbatim>\<open>.tex\<close> verbatim.
\<close>

ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>slide\<close> "open a beamer frame"
    (Parse.opt_target -- Parse.document_source --| Scan.option (Parse.$$$ ";") >>
      Document_Output.document_output
        {markdown = false,
         markup = fn body =>
           XML.string "%\n\\begin{frame}[fragile]{" @
           body @
           XML.string "}%\n"});

  Outer_Syntax.command \<^command_keyword>\<open>end_slide\<close> "close a beamer frame"
    (Parse.opt_target -- Scan.succeed Input.empty >>
      Document_Output.document_output
        {markdown = false, markup = fn _ => XML.string "%\n\\end{frame}\n"});

  \<comment> \<open>\<^verbatim>\<open>interlude\<close>/\<^verbatim>\<open>end_interlude\<close> emit a regular \<^verbatim>\<open>\begin{frame}\<close>/\<^verbatim>\<open>\end{frame}\<close> pair
       \<^emph>\<open>at the source level\<close> so beamer's \<^verbatim>\<open>[fragile]\<close> token-scanner finds the literal close,
       and bracket the body with \<^verbatim>\<open>\interludetop\<close>/\<^verbatim>\<open>\interludebottom\<close> dressing macros
       defined in \<^verbatim>\<open>root.tex\<close>.\<close>
  Outer_Syntax.command \<^command_keyword>\<open>interlude\<close> "open an interlude frame"
    (Parse.opt_target -- Parse.document_source --| Scan.option (Parse.$$$ ";") >>
      Document_Output.document_output
        {markdown = false,
         markup = fn body =>
           XML.string "%\n\\begin{frame}[fragile]{" @
           body @
           XML.string "}%\n\\interludetop%\n"});

  Outer_Syntax.command \<^command_keyword>\<open>end_interlude\<close> "close an interlude frame"
    (Parse.opt_target -- Scan.succeed Input.empty >>
      Document_Output.document_output
        {markdown = false, markup = fn _ => XML.string "%\n\\interludebottom%\n\\end{frame}\n"});
\<close>

end
