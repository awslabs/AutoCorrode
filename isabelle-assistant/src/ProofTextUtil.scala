/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Utilities for manipulating proof text: extracting code from LLM responses,
  * tracking/replacing sorry placeholders, and validating proof structure.
  */
object ProofTextUtil {

  // --- Code extraction from LLM responses ---

  /** Extract code from markdown fences. For fill responses, also accept bare
    * single-line methods. Strips goal restatements that LLMs sometimes prepend
    * before `proof`.
    */
  def extractCode(response: String): String = {
    val fromFences =
      SendbackHelper.extractCodeBlocks(response).mkString("\n").trim
    val raw =
      if (fromFences.nonEmpty) stripGoalRestatement(fromFences)
      else {
        val keywords =
          IsabelleKeywords.proofMethods ++ IsabelleKeywords.proofClosers ++
            Set(
              "simp",
              "auto",
              "blast",
              "force",
              "metis",
              "meson",
              "arith",
              "linarith"
            )
        response.linesIterator
          .map(_.trim)
          .find(l =>
            l.nonEmpty && CommandMatcher
              .findMatchingKeyword(l, keywords)
              .isDefined
          )
          .getOrElse("")
      }
    cleanProofText(raw)
  }

  /** Strip goal restatement lines that appear before proof/by/apply keywords.
    * LLMs often prepend "goal_text\nproof -\n..." which is invalid Isabelle
    * syntax.
    */
  def stripGoalRestatement(code: String): String = {
    val proofKeywords =
      IsabelleKeywords.proofMethods ++ IsabelleKeywords.proofSteps ++ IsabelleKeywords.proofClosers ++ Set(
        "next"
      )
    val lines = code.linesIterator.toList
    // Find the first line that starts with a proof keyword
    val startIdx = lines.indexWhere(l => {
      val t = l.trim
      t.nonEmpty && CommandMatcher
        .findMatchingKeyword(t, proofKeywords)
        .isDefined
    })
    if (startIdx > 0) {
      // Check if the lines before it look like a goal restatement
      val prefix = lines.take(startIdx).map(_.trim).mkString(" ")
      val looksLikeGoal = prefix.contains("=") || prefix.contains("⟹") ||
        prefix.contains("⟶") || prefix.contains("\\<Longrightarrow>")
      if (looksLikeGoal) lines.drop(startIdx).mkString("\n")
      else code
    } else code
  }

  /** Remove spurious wrapping that LLMs sometimes add around code.
    */
  def cleanProofText(text: String): String = {
    var s = text.trim
    s = s.replaceAll("""(?s)(qed|done|sorry)\s*[,)\d\s]+$""", "$1")
    if (s.startsWith("(") && !s.startsWith("(* "))
      s = s.stripPrefix("(").trim
    s
  }

  // --- Sorry tracking ---

  /** Match sorry that is NOT already marked as unfilled. */
  val sorryPattern = """\bsorry\b(?!\s*\(\*)""".r

  /** Pattern for sorry marked as unfilled. */
  val unfilledPattern = """sorry\s*\(\*\s*unfilled\s*\*\)""".r

  /** Count unfilled sorries in proof text.
    */
  def countSorries(proof: String): Int =
    sorryPattern.findAllIn(proof).length

  /** Count sorry (* unfilled *) markers.
    */
  def countUnfilled(proof: String): Int =
    unfilledPattern.findAllIn(proof).length

  /** Split proof at the nth sorry position.
    */
  def splitAtSorry(proof: String, n: Int): Option[(String, String)] = {
    val matches = sorryPattern.findAllMatchIn(proof).toList
    if (n >= matches.length) None
    else {
      val m = matches(n)
      Some((proof.substring(0, m.start), proof.substring(m.end)))
    }
  }

  /** Replace the nth sorry with replacement text.
    */
  def replaceSorry(proof: String, n: Int, replacement: String): Option[String] =
    splitAtSorry(proof, n).map { case (before, after) =>
      s"$before$replacement$after"
    }

  /** Mark the nth sorry with <<< sorry >>> markers for display.
    */
  def markSorry(proof: String, n: Int): String =
    splitAtSorry(proof, n)
      .map { case (before, after) =>
        s"$before<<< sorry >>>$after"
      }
      .getOrElse(proof)

  // --- Proof manipulation ---

  /** Replace all by-clauses with sorry to get a pure skeleton for structural
    * verification. Skips "by" that appears inside cartouches or quotes to avoid
    * corrupting strings. Note: This is a heuristic — perfect Isabelle parsing
    * would require a full lexer.
    *
    * Optimized to O(n) by tracking quote state in a single pass with matches.
    */
  def sorryify(proof: String): String = {
    val byPattern = """\bby\b""".r
    val sb = new StringBuilder
    var pos = 0
    var inCartouche = false
    var inString = false
    var quotePos = 0 // Track up to which position quote state is valid

    // Update quote state from quotePos to targetPos in O(n) single pass
    def updateQuoteState(targetPos: Int): Unit = {
      while (quotePos < targetPos && quotePos < proof.length) {
        proof(quotePos) match {
          case '‹' if !inString                => inCartouche = true
          case '›' if inCartouche && !inString => inCartouche = false
          case '"' if !inCartouche             => inString = !inString
          case '\\'
              if (inString || inCartouche) && quotePos + 1 < proof.length =>
            quotePos += 1 // skip escaped char
          case _ =>
        }
        quotePos += 1
      }
    }

    for (m <- byPattern.findAllMatchIn(proof)) {
      // Update state to match position
      updateQuoteState(m.start)

      // Skip this match if we're currently inside quotes/cartouches
      if (!inCartouche && !inString) {
        sb.append(proof.substring(pos, m.start))
        sb.append("sorry")
        var i = m.end
        while (i < proof.length && proof(i).isWhitespace) i += 1
        if (i < proof.length && proof(i) == '(') {
          var depth = 1; i += 1
          while (i < proof.length && depth > 0) {
            if (proof(i) == '(') depth += 1
            else if (proof(i) == ')') depth -= 1
            i += 1
          }
        } else {
          while (i < proof.length && !proof(i).isWhitespace) i += 1
        }
        pos = i
      }
    }
    sb.append(proof.substring(pos))
    sb.toString
  }

  /** Check that a proof looks structurally complete (has a closing keyword).
    */
  def isStructurallyComplete(proof: String): Boolean = {
    val lastLine = proof.trim.linesIterator.toList.reverseIterator
      .map(_.trim)
      .find(_.nonEmpty)
      .getOrElse("")
    lastLine == "qed" || lastLine == "done" || CommandMatcher.startsWithKeyword(
      lastLine,
      "by"
    )
  }

  /** Determine what replacement was made between two proof strings (for
    * display).
    */
  def findReplacement(oldProof: String, newProof: String): String = {
    splitAtSorry(oldProof, 0) match {
      case Some((prefix, suffix)) =>
        val replacement = newProof.stripPrefix(prefix).stripSuffix(suffix).trim
        if (replacement.nonEmpty) replacement else "(unknown method)"
      case None => "(unknown method)"
    }
  }

  // --- Lemma extraction utilities ---

  /** Extract a lemma statement (no proof) from LLM response.
    */
  def extractLemmaStatement(response: String): String = {
    val fromFences =
      SendbackHelper.extractCodeBlocks(response).mkString("\n").trim
    val code = if (fromFences.nonEmpty) fromFences else response.trim
    val lines = code.linesIterator.toList
    // Find line starting with "lemma" and take just the statement
    val lemmaStart = lines.indexWhere(l => {
      CommandMatcher
        .findMatchingKeyword(l.trim, IsabelleKeywords.proofStarters)
        .isDefined
    })
    if (lemmaStart < 0) return ""
    // Take the lemma line and any continuation lines
    val proofStoppers =
      IsabelleKeywords.proofMethods ++ IsabelleKeywords.proofClosers
    val stmtLines = scala.collection.mutable.ListBuffer(lines(lemmaStart))
    var i = lemmaStart + 1
    while (i < lines.length) {
      val t = lines(i).trim
      if (
        t.isEmpty || CommandMatcher
          .findMatchingKeyword(t, proofStoppers)
          .isDefined
      ) {
        i = lines.length
      } else {
        stmtLines += lines(i)
        i += 1
      }
    }
    stmtLines.mkString("\n")
  }

  /** Extract lemma name from code like "lemma foo_bar:" or "lemma foo_bar
    * [simp]:".
    */
  def extractLemmaName(code: String): String = {
    val lemmaLine = code.linesIterator
      .find(l =>
        CommandMatcher
          .findMatchingKeyword(l.trim, IsabelleKeywords.proofStarters)
          .isDefined
      )
      .getOrElse("")
    val parts = lemmaLine.trim.stripPrefix("lemma").stripPrefix("theorem").trim
    val name = parts.takeWhile(c => c.isLetterOrDigit || c == '_' || c == '\'')
    if (name.nonEmpty) name else "speculated_lemma"
  }

  /** Extract variable names from a lemma statement as a fallback when PIDE
    * markup doesn't provide free variables.
    */
  def extractVarsFromStatement(statement: String): List[String] = {
    val quotedContent = """[‹"](.*?)[›"]""".r
    val vars = scala.collection.mutable.LinkedHashSet[String]()
    for (m <- quotedContent.findAllMatchIn(statement)) {
      val content = m.group(1)
      val tokens = content.split("""[\s()=+*,]+""").filter(_.nonEmpty)
      for (t <- tokens) {
        if (
          t.length <= 3 && t.head.isLower && t
            .forall(c => c.isLetterOrDigit || c == '_') &&
          !Set(
            "add",
            "mult",
            "fun",
            "let",
            "in",
            "if",
            "then",
            "else",
            "the",
            "and",
            "not"
          ).contains(t)
        ) {
          vars.add(t)
        }
      }
    }
    vars.toList
  }
}
