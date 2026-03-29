/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/**
 * Standalone tests for IQNormalization.
 * No jEdit or PIDE dependency — only requires isabelle.jar on the classpath.
 */
object IQNormalizationTest {
  private var passed = 0
  private var failed = 0

  private def assert(condition: Boolean, message: String): Unit = {
    if (!condition) {
      failed += 1
      System.err.println(s"  FAIL: $message")
    } else {
      passed += 1
    }
  }

  private def assertEquals[A](actual: A, expected: A, label: String): Unit = {
    if (actual != expected) {
      failed += 1
      System.err.println(s"  FAIL: $label")
      System.err.println(s"    expected: $expected")
      System.err.println(s"    actual:   $actual")
    } else {
      passed += 1
    }
  }

  private def assertRight[L, R](result: Either[L, R], label: String): R = {
    result match {
      case Right(v) =>
        passed += 1
        v
      case Left(err) =>
        failed += 1
        System.err.println(s"  FAIL: $label — expected Right, got Left($err)")
        throw new RuntimeException(s"assertRight failed: $label")
    }
  }

  private def assertLeft[L, R](result: Either[L, R], expectedLeft: L, label: String): Unit = {
    result match {
      case Left(v) =>
        if (v == expectedLeft) passed += 1
        else {
          failed += 1
          System.err.println(s"  FAIL: $label — expected Left($expectedLeft), got Left($v)")
        }
      case Right(v) =>
        failed += 1
        System.err.println(s"  FAIL: $label — expected Left($expectedLeft), got Right($v)")
    }
  }

  // ---- Test groups ----

  private def testNormalize(): Unit = {
    println("  normalize() — canonical form correctness")

    // Identity: already-Unicode text
    assertEquals(
      IQNormalization.normalize("foo \u21d2 bar"),
      "foo \u21d2 bar",
      "identity: Unicode text unchanged")

    // Isabelle decode
    assertEquals(
      IQNormalization.normalize("foo \\<Rightarrow> bar"),
      "foo \u21d2 bar",
      "decode: \\<Rightarrow> to \u21d2")

    // Multiple symbols
    assertEquals(
      IQNormalization.normalize("\\<forall>x. x \\<Rightarrow> x"),
      "\u2200x. x \u21d2 x",
      "decode: multiple symbols")

    // Cartouches
    assertEquals(
      IQNormalization.normalize("\\<open>hello\\<close>"),
      "\u2039hello\u203a",
      "decode: cartouches \\<open>/\\<close>")

    // Whitespace compression
    assertEquals(
      IQNormalization.normalize("A   B"),
      "A B",
      "whitespace: multiple spaces compressed")

    assertEquals(
      IQNormalization.normalize("A \t\n B"),
      "A B",
      "whitespace: mixed whitespace compressed")

    // Combined: symbol + whitespace
    assertEquals(
      IQNormalization.normalize("A  \\<Rightarrow>  B"),
      "A \u21d2 B",
      "combined: symbol decode + whitespace compression")

    // No symbols: pure ASCII
    assertEquals(
      IQNormalization.normalize("hello world"),
      "hello world",
      "identity: pure ASCII unchanged")

    // Empty string
    assertEquals(
      IQNormalization.normalize(""),
      "",
      "identity: empty string")

    // Single whitespace
    assertEquals(
      IQNormalization.normalize(" "),
      " ",
      "identity: single space unchanged")

    // Logic symbols
    assertEquals(
      IQNormalization.normalize("\\<and>"),
      "\u2227",
      "decode: \\<and> to \u2227")

    assertEquals(
      IQNormalization.normalize("\\<or>"),
      "\u2228",
      "decode: \\<or> to \u2228")

    assertEquals(
      IQNormalization.normalize("\\<forall>"),
      "\u2200",
      "decode: \\<forall> to \u2200")

    assertEquals(
      IQNormalization.normalize("\\<exists>"),
      "\u2203",
      "decode: \\<exists> to \u2203")

    // Arrow symbols
    assertEquals(
      IQNormalization.normalize("\\<rightarrow>"),
      "\u2192",
      "decode: \\<rightarrow> to \u2192")

    assertEquals(
      IQNormalization.normalize("\\<Longrightarrow>"),
      "\u27f9",
      "decode: \\<Longrightarrow> to \u27f9")

    // Text with no Isabelle symbols but with backslashes
    assertEquals(
      IQNormalization.normalize("a \\ b"),
      "a \\ b",
      "identity: backslash that is not an Isabelle symbol")

    // Trailing/leading whitespace compression
    assertEquals(
      IQNormalization.normalize("  hello  "),
      " hello ",
      "whitespace: leading/trailing compressed to single spaces")
  }

  private def testNormalizeWithOffsets(): Unit = {
    println("  normalizeWithOffsets() — offset map correctness")

    // Identity: no change
    locally {
      val result = IQNormalization.normalizeWithOffsets("abc")
      assertEquals(result.canonical, "abc", "offsets identity: canonical unchanged")
      assertEquals(result.offsetMap.toList, List(0, 1, 2, 3), "offsets identity: identity map")
    }

    // Single Isabelle symbol: \<Rightarrow> (14 chars) → ⇒ (1 char)
    locally {
      val input = "\\<Rightarrow>"
      val result = IQNormalization.normalizeWithOffsets(input)
      assertEquals(result.canonical, "\u21d2", "offsets single symbol: canonical")
      assertEquals(result.offsetMap.length, 2, "offsets single symbol: map length (1 char + sentinel)")
      assertEquals(result.offsetMap(0), 0, "offsets single symbol: char maps to 0")
      assertEquals(result.offsetMap(1), input.length, "offsets single symbol: sentinel maps to end")
    }

    // Symbol in context: "ab\<Rightarrow>cd" → "ab⇒cd"
    // \<Rightarrow> is 13 chars, so: a=0, b=1, \<Rightarrow>=2..14, c=15, d=16, length=17
    locally {
      val input = "ab\\<Rightarrow>cd"
      val result = IQNormalization.normalizeWithOffsets(input)
      assertEquals(result.canonical, "ab\u21d2cd", "offsets in context: canonical")
      assertEquals(result.offsetMap(0), 0, "offsets in context: 'a' at 0")
      assertEquals(result.offsetMap(1), 1, "offsets in context: 'b' at 1")
      assertEquals(result.offsetMap(2), 2, "offsets in context: '⇒' maps to original 2")
      assertEquals(result.offsetMap(3), 15, "offsets in context: 'c' maps to original 15")
      assertEquals(result.offsetMap(4), 16, "offsets in context: 'd' maps to original 16")
      assertEquals(result.offsetMap(5), 17, "offsets in context: sentinel maps to end")
    }

    // Whitespace compression: "a  b" → "a b"
    locally {
      val result = IQNormalization.normalizeWithOffsets("a  b")
      assertEquals(result.canonical, "a b", "offsets ws: canonical")
      assertEquals(result.offsetMap(0), 0, "offsets ws: 'a' at 0")
      assertEquals(result.offsetMap(1), 1, "offsets ws: space maps to first ws at 1")
      assertEquals(result.offsetMap(2), 3, "offsets ws: 'b' at 3")
      assertEquals(result.offsetMap(3), 4, "offsets ws: sentinel")
    }

    // Combined: "a  \<Rightarrow>  b" → "a ⇒ b"
    // a=0, sp=1, sp=2, \<Rightarrow>=3..15 (13 chars), sp=16, sp=17, b=18, length=19
    locally {
      val input = "a  \\<Rightarrow>  b"
      val result = IQNormalization.normalizeWithOffsets(input)
      assertEquals(result.canonical, "a \u21d2 b", "offsets combined: canonical")
      assertEquals(result.offsetMap(0), 0, "offsets combined: 'a' at 0")
      assertEquals(result.offsetMap(1), 1, "offsets combined: first compressed space at 1")
      assertEquals(result.offsetMap(2), 3, "offsets combined: '⇒' maps to original 3")
      assertEquals(result.offsetMap(3), 16, "offsets combined: second compressed space at 16")
      assertEquals(result.offsetMap(4), 18, "offsets combined: 'b' at 18")
      assertEquals(result.offsetMap(5), 19, "offsets combined: sentinel")
    }

    // Empty string
    locally {
      val result = IQNormalization.normalizeWithOffsets("")
      assertEquals(result.canonical, "", "offsets empty: canonical empty")
      assertEquals(result.offsetMap.toList, List(0), "offsets empty: just sentinel")
    }

    // Multiple consecutive symbols
    // \<forall> is 9 chars, \<exists> is 9 chars
    locally {
      val input = "\\<forall>\\<exists>"
      val result = IQNormalization.normalizeWithOffsets(input)
      assertEquals(result.canonical, "\u2200\u2203", "offsets multi-symbol: canonical")
      assertEquals(result.offsetMap(0), 0, "offsets multi-symbol: ∀ maps to 0")
      assertEquals(result.offsetMap(1), 9, "offsets multi-symbol: ∃ maps to 9")
      assertEquals(result.offsetMap(2), input.length, "offsets multi-symbol: sentinel")
    }
  }

  private def testFindUniqueMatch(): Unit = {
    println("  findUniqueMatch() — matching with offset tracking")

    // Exact match, no normalization needed
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("foo bar", "bar"),
        "exact match")
      assertEquals(start, 4, "exact match: start")
      assertEquals(end, 7, "exact match: end")
    }

    // Pattern has Isabelle escapes, text is Unicode
    // text "foo ⇒ bar": ⇒ is at position 4, length 1
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("foo \u21d2 bar", "\\<Rightarrow>"),
        "pattern Isabelle, text Unicode")
      assertEquals(start, 4, "pattern Isabelle, text Unicode: start")
      assertEquals(end, 5, "pattern Isabelle, text Unicode: end")
    }

    // Text has Isabelle escapes, pattern is Unicode
    // text "foo \<Rightarrow> bar": \<Rightarrow> starts at 4, next char (space) at 17
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("foo \\<Rightarrow> bar", "\u21d2"),
        "text Isabelle, pattern Unicode")
      assertEquals(start, 4, "text Isabelle, pattern Unicode: start")
      assertEquals(end, 17, "text Isabelle, pattern Unicode: end")
    }

    // Both have Isabelle escapes (direct match — Tier 1)
    // \<Rightarrow> is 13 chars
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("\\<Rightarrow>", "\\<Rightarrow>"),
        "both Isabelle")
      assertEquals(start, 0, "both Isabelle: start")
      assertEquals(end, 13, "both Isabelle: end")
    }

    // Both Unicode (direct match — Tier 1)
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("\u21d2", "\u21d2"),
        "both Unicode")
      assertEquals(start, 0, "both Unicode: start")
      assertEquals(end, 1, "both Unicode: end")
    }

    // Whitespace mismatch
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("A   B", "A B"),
        "whitespace mismatch")
      assertEquals(start, 0, "whitespace mismatch: start")
      assertEquals(end, 5, "whitespace mismatch: end")
    }

    // Combined: text has Isabelle + extra whitespace, pattern has Unicode + single space
    // "P  \<Rightarrow>  Q" = P(0) sp(1) sp(2) \<Rightarrow>(3..15) sp(16) sp(17) Q(18) len=19
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("P  \\<Rightarrow>  Q", "P \u21d2 Q"),
        "combined: Isabelle+ws text, Unicode+single-space pattern")
      assertEquals(start, 0, "combined: start")
      assertEquals(end, 19, "combined: end")
    }

    // Not found
    assertLeft(
      IQNormalization.findUniqueMatch("foo bar", "baz"),
      IQNormalization.SubstringNotFound,
      "not found")

    // Not unique (direct match)
    assertLeft(
      IQNormalization.findUniqueMatch("foo bar foo", "foo"),
      IQNormalization.SubstringNotUnique,
      "not unique (direct)")

    // Not unique (normalized match)
    assertLeft(
      IQNormalization.findUniqueMatch("A \\<Rightarrow> B \\<Rightarrow> C", "\u21d2"),
      IQNormalization.SubstringNotUnique,
      "not unique (normalized)")

    // Empty substring
    assertLeft(
      IQNormalization.findUniqueMatch("foo", ""),
      IQNormalization.SubstringEmpty,
      "empty substring")

    // Mixed encoding in pattern
    // text "∀x. x ⇒ x" is 9 chars, pattern decodes to same → full match
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch(
          "\u2200x. x \u21d2 x",
          "\\<forall>x. x \\<Rightarrow> x"),
        "mixed encoding pattern")
      assertEquals(start, 0, "mixed encoding: start")
      assertEquals(end, 9, "mixed encoding: end")
    }

    // Match at end of text
    // "hello \<Rightarrow>" = h(0)e(1)l(2)l(3)o(4)sp(5)\<Rightarrow>(6..18) len=19
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("hello \\<Rightarrow>", "\u21d2"),
        "match at end")
      assertEquals(start, 6, "match at end: start")
      assertEquals(end, 19, "match at end: end")
    }

    // Match at start of text
    // "\<Rightarrow> hello" = \<Rightarrow>(0..12) sp(13) h(14)... len=19
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("\\<Rightarrow> hello", "\u21d2"),
        "match at start")
      assertEquals(start, 0, "match at start: start")
      assertEquals(end, 13, "match at start: end")
    }

    // Multi-symbol pattern
    // "x \<and> y \<Rightarrow> z": x(0)sp(1)\<and>(2..7)sp(8)y(9)sp(10)\<Rightarrow>(11..23)sp(24)z(25)
    // decoded: "x ∧ y ⇒ z" (9 chars), pattern "∧ y ⇒" matches at pos 2, len 5, endIdx=7
    // offsetMap(7) = 24
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch(
          "x \\<and> y \\<Rightarrow> z",
          "\u2227 y \u21d2"),
        "multi-symbol pattern")
      assertEquals(start, 2, "multi-symbol pattern: start")
      assertEquals(end, 24, "multi-symbol pattern: end")
    }

    // Pattern with only whitespace difference
    locally {
      val (start, end) = assertRight(
        IQNormalization.findUniqueMatch("a\t\n b", "a b"),
        "tab+newline compressed")
      assertEquals(start, 0, "tab+newline: start")
      assertEquals(end, 5, "tab+newline: end")
    }
  }

  private def testEdgeCases(): Unit = {
    println("  Edge cases and regression tests")

    // Literal backslash that is NOT an Isabelle symbol
    locally {
      val text = "path\\to\\file"
      assertEquals(
        IQNormalization.normalize(text),
        text,
        "literal backslash: not an Isabelle symbol, unchanged")
    }

    // Malformed symbols: \<> and \<^>
    locally {
      val text1 = "hello \\<> world"
      // Should not crash — malformed symbols pass through
      val norm1 = IQNormalization.normalize(text1)
      assert(norm1.nonEmpty, "malformed \\<>: did not crash")

      val text2 = "hello \\<^> world"
      val norm2 = IQNormalization.normalize(text2)
      assert(norm2.nonEmpty, "malformed \\<^>: did not crash")
    }

    // Single character text
    assertEquals(
      IQNormalization.normalize("x"),
      "x",
      "single char: unchanged")

    // Text that is all whitespace
    assertEquals(
      IQNormalization.normalize("   "),
      " ",
      "all whitespace: compressed to single space")

    // Newlines as whitespace
    assertEquals(
      IQNormalization.normalize("a\n\n\nb"),
      "a b",
      "multiple newlines: compressed")

    // Carriage returns
    assertEquals(
      IQNormalization.normalize("a\r\n\r\nb"),
      "a b",
      "CRLF: compressed")

    // No whitespace compression for single whitespace chars
    assertEquals(
      IQNormalization.normalize("a b"),
      "a b",
      "single space: unchanged")

    assertEquals(
      IQNormalization.normalize("a\tb"),
      "a b",
      "single tab: normalized to space")

    assertEquals(
      IQNormalization.normalize("a\nb"),
      "a b",
      "single newline: normalized to space")

    // Symbol followed immediately by another symbol (no space)
    locally {
      val input = "\\<forall>\\<forall>"
      val norm = IQNormalization.normalize(input)
      assertEquals(norm, "\u2200\u2200", "adjacent symbols: both decoded")
    }

    // findUniqueMatch with text that has no match even after normalization
    assertLeft(
      IQNormalization.findUniqueMatch("\\<Rightarrow>", "\\<Longrightarrow>"),
      IQNormalization.SubstringNotFound,
      "different symbols: not found")

    // findUniqueMatch where direct match exists but is not unique,
    // while normalized form is also not unique
    assertLeft(
      IQNormalization.findUniqueMatch("x x", "x"),
      IQNormalization.SubstringNotUnique,
      "non-unique single char")

    // Performance sanity: normalize a moderately large string
    locally {
      val largeText = "hello \\<Rightarrow> world " * 1000
      val t0 = System.nanoTime()
      val _ = IQNormalization.normalize(largeText)
      val elapsed = (System.nanoTime() - t0) / 1000000
      assert(elapsed < 5000, s"performance: normalize 20KB in <5s (took ${elapsed}ms)")
    }

    // Performance: normalizeWithOffsets on moderately large string
    locally {
      val largeText = "hello \\<Rightarrow> world " * 1000
      val t0 = System.nanoTime()
      val _ = IQNormalization.normalizeWithOffsets(largeText)
      val elapsed = (System.nanoTime() - t0) / 1000000
      assert(elapsed < 5000, s"performance: normalizeWithOffsets 20KB in <5s (took ${elapsed}ms)")
    }
  }

  /**
   * Systematic tests of findUniqueMatch covering:
   *   encoding: {Isabelle sequences, Unicode, mixed}
   *   whitespace: {exact, extra spaces, tabs, mixed ws}
   *   match result: {no match, unique via Tier 1, unique via Tier 2, multiple}
   *
   * Every (startOffset, endOffset) is hardcoded against the ORIGINAL text.
   */
  private def testEncodingWhitespaceMatrix(): Unit = {
    println("  findUniqueMatch() — encoding × whitespace × match-result matrix")

    // ================================================================
    // 1. ENCODING VARIATIONS — unique match, exact whitespace
    // ================================================================

    // 1a. Text=Isabelle, Pattern=Unicode (Tier 2)
    // text: "A \<Rightarrow> B" = A(0) sp(1) \<Rightarrow>(2..14) sp(15) B(16) = 17 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \\<Rightarrow> B", "A \u21d2 B"),
        "1a: text=Isabelle pattern=Unicode")
      assertEquals(s, 0, "1a: start")
      assertEquals(e, 17, "1a: end")
    }

    // 1b. Text=Unicode, Pattern=Isabelle (Tier 2)
    // text: "A ⇒ B" = 5 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A \\<Rightarrow> B"),
        "1b: text=Unicode pattern=Isabelle")
      assertEquals(s, 0, "1b: start")
      assertEquals(e, 5, "1b: end")
    }

    // 1c. Both Isabelle (Tier 1 — direct match)
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \\<Rightarrow> B", "A \\<Rightarrow> B"),
        "1c: both Isabelle")
      assertEquals(s, 0, "1c: start")
      assertEquals(e, 17, "1c: end")
    }

    // 1d. Both Unicode (Tier 1 — direct match)
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A \u21d2 B"),
        "1d: both Unicode")
      assertEquals(s, 0, "1d: start")
      assertEquals(e, 5, "1d: end")
    }

    // 1e. Text=Isabelle cartouches, Pattern=Unicode cartouches
    // \<open> = 7 chars, \<close> = 8 chars
    // text: "f \<open>x\<close>" = f(0) sp(1) \<open>(2..8) x(9) \<close>(10..17) = 18 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("f \\<open>x\\<close>", "f \u2039x\u203a"),
        "1e: Isabelle cartouches vs Unicode cartouches")
      assertEquals(s, 0, "1e: start")
      assertEquals(e, 18, "1e: end")
    }

    // 1f. Reversed: Text=Unicode cartouches, Pattern=Isabelle cartouches
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("f \u2039x\u203a", "f \\<open>x\\<close>"),
        "1f: Unicode cartouches vs Isabelle cartouches")
      assertEquals(s, 0, "1f: start")
      assertEquals(e, 5, "1f: end")
    }

    // 1g. Cross-mixed: text=Isabelle-open + Unicode-close, pattern=Unicode-open + Isabelle-close
    // text: "\<open>x›" = \<open>(0..6) x(7) ›(8) = 9 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("\\<open>x\u203a", "\u2039x\\<close>"),
        "1g: cross-mixed cartouche encodings")
      assertEquals(s, 0, "1g: start")
      assertEquals(e, 9, "1g: end")
    }

    // ================================================================
    // 2. WHITESPACE VARIATIONS — same encoding (Unicode), unique match
    // ================================================================

    // 2a. Pattern has extra spaces, text has single spaces
    // text: "A ⇒ B" = 5 chars
    // endOffset must be 5 (actual match end), NOT 0 + patternLen
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A  \u21d2  B"),
        "2a: pattern extra spaces, text single")
      assertEquals(s, 0, "2a: start")
      assertEquals(e, 5, "2a: end=5, not pattern.length=7")
    }

    // 2b. Text has extra spaces, pattern has single spaces
    // text: "A  ⇒  B" = A(0) sp(1) sp(2) ⇒(3) sp(4) sp(5) B(6) = 7 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A  \u21d2  B", "A \u21d2 B"),
        "2b: text extra spaces, pattern single")
      assertEquals(s, 0, "2b: start")
      assertEquals(e, 7, "2b: end=7, not pattern.length=5")
    }

    // 2c. Tabs in pattern, spaces in text (1:1 char replacement)
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A\t\u21d2\tB"),
        "2c: tabs in pattern, spaces in text")
      assertEquals(s, 0, "2c: start")
      assertEquals(e, 5, "2c: end")
    }

    // 2d. Tabs in text, spaces in pattern
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A\t\u21d2\tB", "A \u21d2 B"),
        "2d: tabs in text, spaces in pattern")
      assertEquals(s, 0, "2d: start")
      assertEquals(e, 5, "2d: end")
    }

    // 2e. Mixed whitespace in pattern (tab + spaces), single space in text
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A \t \u21d2 \t B"),
        "2e: mixed ws in pattern")
      assertEquals(s, 0, "2e: start")
      assertEquals(e, 5, "2e: end=5, not pattern.length=11")
    }

    // 2f. Heavily padded pattern
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A     \u21d2     B"),
        "2f: heavily padded pattern")
      assertEquals(s, 0, "2f: start")
      assertEquals(e, 5, "2f: end=5, not pattern.length=15")
    }

    // ================================================================
    // 3. COMBINED encoding + whitespace, unique match
    // ================================================================

    // 3a. Text=Isabelle+extra ws, Pattern=Unicode+single ws
    // text: "A  \<Rightarrow>  B" = A(0) sp(1) sp(2) \<Rightarrow>(3..15) sp(16) sp(17) B(18) = 19 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A  \\<Rightarrow>  B", "A \u21d2 B"),
        "3a: text=Isabelle+extra-ws, pattern=Unicode+single-ws")
      assertEquals(s, 0, "3a: start")
      assertEquals(e, 19, "3a: end")
    }

    // 3b. Text=Unicode+single ws, Pattern=Isabelle+extra ws
    // text: "A ⇒ B" = 5 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A  \\<Rightarrow>  B"),
        "3b: text=Unicode+single-ws, pattern=Isabelle+extra-ws")
      assertEquals(s, 0, "3b: start")
      assertEquals(e, 5, "3b: end=5, not pattern.length=19")
    }

    // 3c. Substring in context — Isabelle text, Unicode pattern
    // text: "hello A \<Rightarrow> B world"
    //   h(0)e(1)l(2)l(3)o(4) (5)A(6) (7)\<Rightarrow>(8..20) (21)B(22) (23)w(24)o(25)r(26)l(27)d(28) = 29
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("hello A \\<Rightarrow> B world", "A \u21d2 B"),
        "3c: Isabelle in context, Unicode pattern")
      assertEquals(s, 6, "3c: start")
      assertEquals(e, 23, "3c: end")
    }

    // 3d. Substring in context — Isabelle+extra ws text, Unicode pattern
    // text: "hello A  \<Rightarrow>  B world"
    //   h(0)e(1)l(2)l(3)o(4) (5)A(6) (7) (8)\<Rightarrow>(9..21) (22) (23)B(24) (25)w(26)o(27)r(28)l(29)d(30) = 31
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("hello A  \\<Rightarrow>  B world", "A \u21d2 B"),
        "3d: Isabelle+extra-ws in context, Unicode pattern")
      assertEquals(s, 6, "3d: start")
      assertEquals(e, 25, "3d: end")
    }

    // 3e. Same text as 3d, but pattern also has extra whitespace
    // Offsets in original text must be identical to 3d
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("hello A  \\<Rightarrow>  B world", "A   \u21d2   B"),
        "3e: both extra-ws + encoding mismatch")
      assertEquals(s, 6, "3e: start — same as 3d")
      assertEquals(e, 25, "3e: end — same as 3d, not shifted by pattern ws")
    }

    // ================================================================
    // 4. NO MATCH
    // ================================================================

    assertLeft(
      IQNormalization.findUniqueMatch("A \\<Rightarrow> B", "A \\<Longrightarrow> B"),
      IQNormalization.SubstringNotFound,
      "4a: different Isabelle symbols")

    assertLeft(
      IQNormalization.findUniqueMatch("A \u21d2 B", "A \\<Longrightarrow> B"),
      IQNormalization.SubstringNotFound,
      "4b: ⇒ text vs ⟹ pattern, cross-encoding")

    assertLeft(
      IQNormalization.findUniqueMatch("hello world", "\\<Rightarrow>"),
      IQNormalization.SubstringNotFound,
      "4c: no symbol in text")

    assertLeft(
      IQNormalization.findUniqueMatch("AB", "A B"),
      IQNormalization.SubstringNotFound,
      "4d: ws in pattern but not in text — no match")

    // ================================================================
    // 5. MULTIPLE MATCHES — not unique
    // ================================================================

    assertLeft(
      IQNormalization.findUniqueMatch("\u21d2 x \u21d2", "\u21d2"),
      IQNormalization.SubstringNotUnique,
      "5a: two ⇒, direct duplicates")

    assertLeft(
      IQNormalization.findUniqueMatch("A \\<Rightarrow> B \\<Rightarrow> C", "\u21d2"),
      IQNormalization.SubstringNotUnique,
      "5b: two Isabelle arrows, Unicode pattern")

    // ws compression creates duplicates: "A  B  A  B" → "A B A B", pattern "A B" × 2
    assertLeft(
      IQNormalization.findUniqueMatch("A  B  A  B", "A B"),
      IQNormalization.SubstringNotUnique,
      "5c: ws compression creates duplicate matches")

    assertLeft(
      IQNormalization.findUniqueMatch("\\<Rightarrow>  x  \\<Rightarrow>", "\u21d2"),
      IQNormalization.SubstringNotUnique,
      "5d: encoding + ws normalization, two matches")

    // ================================================================
    // 6. OFFSET CONTRACT — endOffset tracks original text, not pattern length
    //    These are the cases that expose the findCommandByPattern bug.
    // ================================================================

    // 6a. Pattern=15 chars (padded), text match=5 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A     \u21d2     B"),
        "6a: long pattern, short text")
      assertEquals(s, 0, "6a: start")
      assertEquals(e, 5, "6a: end=5, NOT pattern.length=15")
    }

    // 6b. Pattern=19 chars (Isabelle+ws), text match=5 chars (Unicode)
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("A \u21d2 B", "A  \\<Rightarrow>  B"),
        "6b: Isabelle+ws pattern, Unicode text")
      assertEquals(s, 0, "6b: start")
      assertEquals(e, 5, "6b: end=5, NOT pattern.length=19")
    }

    // 6c. Pattern=5 chars (Unicode), text match=19 chars (Isabelle+ws), in context
    // text: "X A  \<Rightarrow>  B Y"
    //   X(0) (1)A(2) (3) (4)\<Rightarrow>(5..17) (18) (19)B(20) (21)Y(22) = 23 chars
    locally {
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch("X A  \\<Rightarrow>  B Y", "A \u21d2 B"),
        "6c: Unicode pattern, Isabelle+ws text in context")
      assertEquals(s, 2, "6c: start=2")
      assertEquals(e, 21, "6c: end=21, NOT start+pattern.length=7")
    }

    // 6d. The file_pattern scenario: pattern overshoots into "by simp"
    // text: "lemma foo: \<open>True\<close>\nby simp"
    //   l(0)e(1)m(2)m(3)a(4) (5)f(6)o(7)o(8):(9) (10)\<open>(11..17)T(18)r(19)u(20)e(21)\<close>(22..29)\n(30)b(31)y(32) (33)s(34)i(35)m(36)p(37) = 38 chars
    // pattern (Unicode+extra ws): "lemma  foo:  ‹True›" (20 chars)
    // normalized text: "lemma foo: ‹True› by simp" (25 chars)
    // normalized pattern: "lemma foo: ‹True›" (17 chars)
    // match at norm 0, endIdx=17 → offsetMap(17)=30 (the \n)
    // lastCharOffset should be 30-1=29 (the '>' of \<close>) — within lemma command
    // bug version: 0+20-1=19 — happens to be inside too, but wrong principle
    locally {
      val text = "lemma foo: \\<open>True\\<close>\nby simp"
      val pattern = "lemma  foo:  \u2039True\u203a"
      val (s, e) = assertRight(
        IQNormalization.findUniqueMatch(text, pattern),
        "6d: file_pattern scenario — endOffset at command boundary")
      assertEquals(s, 0, "6d: start=0")
      assertEquals(e, 30, "6d: end=30 (the \\n), NOT 0+pattern.length=20")
    }
  }

  def main(args: Array[String]): Unit = {
    println("IQNormalizationTest")

    testNormalize()
    testNormalizeWithOffsets()
    testFindUniqueMatch()
    testEdgeCases()
    testEncodingWhitespaceMatrix()

    println()
    if (failed > 0) {
      println(s"FAILED: $failed failures, $passed passed")
      sys.exit(1)
    } else {
      println(s"OK: $passed tests passed")
    }
  }
}
