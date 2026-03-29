/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/**
 * Standalone text normalization for Isabelle symbol matching with original-offset tracking.
 *
 * Normalizes text to a canonical Unicode form (Symbol.decode + NFC + whitespace compression)
 * so that Isabelle escape sequences (\<Rightarrow>) match their Unicode equivalents (⇒).
 * When normalization changes the text, an offset map tracks the correspondence between
 * positions in the canonical string and positions in the original.
 *
 * Only depends on isabelle._ (Symbol, from isabelle.jar). No jEdit or PIDE dependency.
 */

import isabelle._

object IQNormalization {

  /** Result of normalizing text with offset tracking. */
  final case class NormalizedText(
    /** The canonical (normalized) string. */
    canonical: String,
    /**
     * offsetMap(i) = position in the original text corresponding to canonical position i.
     * Length = canonical.length + 1 (the sentinel at the end maps to original text length).
     */
    offsetMap: Array[Int]
  )

  sealed trait SubstringSearchError
  case object SubstringNotFound extends SubstringSearchError
  case object SubstringNotUnique extends SubstringSearchError
  case object SubstringEmpty extends SubstringSearchError

  // --- Normalization pipeline ---

  /**
   * Normalize text to canonical Unicode form (string only, no offset tracking).
   * Pipeline: NFC → Symbol.decode → whitespace compression.
   */
  def normalize(text: String): String = {
    if (text.isEmpty) return text
    val afterNfc = java.text.Normalizer.normalize(text, java.text.Normalizer.Form.NFC)
    val afterDecode = Symbol.decode(afterNfc)
    compressWhitespace(afterDecode)
  }

  /**
   * Normalize text with offset map tracking original positions.
   * Pipeline: NFC → Symbol.decode → whitespace compression.
   * offsetMap(i) = position in the original text for canonical position i.
   */
  def normalizeWithOffsets(text: String): NormalizedText = {
    if (text.isEmpty) return NormalizedText("", Array(0))

    // Step 1: NFC normalization with offset tracking
    val (afterNfc, nfcOffsets) = nfcWithOffsets(text)

    // Step 2: Symbol.decode with offset tracking
    val (afterDecode, decodeOffsets) = symbolDecodeWithOffsets(afterNfc, nfcOffsets)

    // Step 3: Whitespace compression with offset tracking
    val (compressed, compressedOffsets) = compressWhitespaceWithOffsets(afterDecode, decodeOffsets)

    NormalizedText(compressed, compressedOffsets)
  }

  /**
   * Find a unique substring match after normalization, returning (startOffset, endOffset)
   * in the original text. endOffset is exclusive (points one past the last matched char).
   *
   * Tier 1: direct indexOf (no normalization).
   * Tier 2: full normalization pipeline with offset mapping.
   */
  def findUniqueMatch(text: String, substring: String): Either[SubstringSearchError, (Int, Int)] = {
    if (substring.isEmpty) return Left(SubstringEmpty)

    // Tier 1: direct match
    val directFirst = text.indexOf(substring)
    if (directFirst != -1) {
      val directSecond = text.indexOf(substring, directFirst + 1)
      if (directSecond == -1) return Right((directFirst, directFirst + substring.length))
      else return Left(SubstringNotUnique)
    }

    // Tier 2: normalized match
    val normalizedPattern = normalize(substring)
    if (normalizedPattern.isEmpty) return Left(SubstringEmpty)

    val normalizedText = normalize(text)
    val normFirst = normalizedText.indexOf(normalizedPattern)
    if (normFirst == -1) return Left(SubstringNotFound)

    val normSecond = normalizedText.indexOf(normalizedPattern, normFirst + 1)
    if (normSecond != -1) return Left(SubstringNotUnique)

    // Map the match position back to the original text
    if (normalizedText == text) {
      // Text didn't change under normalization — offsets are identity
      Right((normFirst, normFirst + normalizedPattern.length))
    } else {
      // Text changed — build the offset map
      val normalized = normalizeWithOffsets(text)
      val startOffset = normalized.offsetMap(normFirst)
      val endIdx = normFirst + normalizedPattern.length
      val endOffset =
        if (endIdx < normalized.offsetMap.length) normalized.offsetMap(endIdx)
        else text.length
      Right((startOffset, endOffset))
    }
  }

  // --- Internal pipeline steps ---

  /**
   * Apply NFC normalization with offset tracking.
   * For each position in the NFC output, records the corresponding position in the original.
   */
  private[this] def nfcWithOffsets(text: String): (String, Array[Int]) = {
    val nfc = java.text.Normalizer.normalize(text, java.text.Normalizer.Form.NFC)
    if (nfc == text) {
      // No change — identity mapping
      val offsets = Array.tabulate(text.length + 1)(i => i)
      (text, offsets)
    } else {
      // NFC changed the text. Build offset map character by character.
      // This handles the (rare) case of combining characters being composed.
      val offsets = new Array[Int](nfc.length + 1)
      var origPos = 0
      var nfcPos = 0
      while (origPos < text.length && nfcPos < nfc.length) {
        val origChar = text.charAt(origPos)
        val origCharNfc = java.text.Normalizer.normalize(origChar.toString, java.text.Normalizer.Form.NFC)
        for (j <- 0 until origCharNfc.length if nfcPos + j < nfc.length) {
          offsets(nfcPos + j) = origPos
        }
        origPos += 1
        nfcPos += origCharNfc.length
      }
      offsets(nfc.length) = text.length
      (nfc, offsets)
    }
  }

  /**
   * Apply Symbol.decode with offset tracking.
   * Walks the input using Symbol.Matcher, decodes each Isabelle symbol to Unicode,
   * and maps each output character back through the base offset map.
   */
  private[this] def symbolDecodeWithOffsets(text: String, baseOffsets: Array[Int]): (String, Array[Int]) = {
    val decoded = Symbol.decode(text)
    if (decoded == text) {
      // No change — pass through base offsets
      (text, baseOffsets)
    } else {
      // Build offset map by iterating over Isabelle symbols
      val result = new java.lang.StringBuilder(text.length)
      val offsets = new java.util.ArrayList[Int](text.length + 1)
      val matcher = new Symbol.Matcher(text)
      var i = 0
      while (i < text.length) {
        val sym = matcher.match_symbol(i)
        val symDecoded = Symbol.decode(sym)
        val origPos = if (i < baseOffsets.length) baseOffsets(i) else baseOffsets(baseOffsets.length - 1)
        var j = 0
        while (j < symDecoded.length) {
          result.append(symDecoded.charAt(j))
          offsets.add(origPos)
          j += 1
        }
        i += sym.length
      }
      // Sentinel: maps end of canonical to end of original
      offsets.add(baseOffsets(baseOffsets.length - 1))

      val offsetArray = new Array[Int](offsets.size)
      var k = 0
      while (k < offsets.size) { offsetArray(k) = offsets.get(k); k += 1 }
      (result.toString, offsetArray)
    }
  }

  /**
   * Normalize whitespace: convert any whitespace character to a space,
   * then compress consecutive spaces into a single space.
   */
  private[this] def compressWhitespace(text: String): String = {
    val n = text.length
    // Fast check: any non-space whitespace or consecutive whitespace?
    var needsWork = false
    var i = 0
    while (i < n && !needsWork) {
      val c = text.charAt(i)
      if (c == '\t' || c == '\n' || c == '\r') needsWork = true
      else if (c == ' ' && i + 1 < n && isWhitespace(text.charAt(i + 1))) needsWork = true
      i += 1
    }
    if (!needsWork) return text

    val sb = new java.lang.StringBuilder(n)
    i = 0
    while (i < n) {
      val c = text.charAt(i)
      if (isWhitespace(c)) {
        sb.append(' ')
        i += 1
        while (i < n && isWhitespace(text.charAt(i))) i += 1
      } else {
        sb.append(c)
        i += 1
      }
    }
    sb.toString
  }

  /**
   * Compress whitespace with offset tracking.
   * Runs of whitespace characters collapse to a single space.
   * The space maps to the original position of the first whitespace character in the run.
   */
  private[this] def compressWhitespaceWithOffsets(text: String, baseOffsets: Array[Int]): (String, Array[Int]) = {
    val n = text.length
    // Fast check: any non-space whitespace or consecutive whitespace?
    var needsWork = false
    var i = 0
    while (i < n && !needsWork) {
      val c = text.charAt(i)
      if (c == '\t' || c == '\n' || c == '\r') needsWork = true
      else if (c == ' ' && i + 1 < n && isWhitespace(text.charAt(i + 1))) needsWork = true
      i += 1
    }
    if (!needsWork) return (text, baseOffsets)

    val sb = new java.lang.StringBuilder(n)
    val offsets = new java.util.ArrayList[Int](n + 1)
    i = 0
    while (i < n) {
      val c = text.charAt(i)
      if (isWhitespace(c)) {
        sb.append(' ')
        offsets.add(baseOffsets(i))
        i += 1
        while (i < n && isWhitespace(text.charAt(i))) i += 1
      } else {
        sb.append(c)
        offsets.add(baseOffsets(i))
        i += 1
      }
    }
    offsets.add(baseOffsets(baseOffsets.length - 1))

    val offsetArray = new Array[Int](offsets.size)
    var k = 0
    while (k < offsets.size) { offsetArray(k) = offsets.get(k); k += 1 }
    (sb.toString, offsetArray)
  }

  private[this] def isWhitespace(c: Char): Boolean =
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}
