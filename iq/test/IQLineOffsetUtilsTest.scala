/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

object IQLineOffsetUtilsTest {
  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def verifyBounds(text: String): Unit = {
    val totalLines = IQLineOffsetUtils.splitLines(text).length
    for (line <- -(totalLines + 5) to (totalLines + 5)) {
      val offsets = List(
        IQLineOffsetUtils.lineNumberToOffset(text, line),
        IQLineOffsetUtils.lineNumberToOffset(text, line, increment = true),
        IQLineOffsetUtils.lineNumberToOffset(text, line, increment = true, withLastNewLine = false)
      )
      offsets.foreach { offset =>
        requireThat(offset >= 0, s"offset must be non-negative (text='$text', line=$line, offset=$offset)")
        requireThat(offset <= text.length, s"offset must be <= text length (text='$text', line=$line, offset=$offset)")
      }
    }
  }

  private def verifyMonotonicity(text: String): Unit = {
    val totalLines = IQLineOffsetUtils.splitLines(text).length
    val positiveLines = (1 to (totalLines + 5)).toList
    val negativeLines = (-(totalLines + 5) to -1).toList

    val positiveOffsets = positiveLines.map(line => IQLineOffsetUtils.lineNumberToOffset(text, line))
    val positiveOffsetsInc = positiveLines.map(line => IQLineOffsetUtils.lineNumberToOffset(text, line, increment = true))
    val positiveOffsetsTrimmed = positiveLines.map(line =>
      IQLineOffsetUtils.lineNumberToOffset(text, line, increment = true, withLastNewLine = false))

    val negativeOffsets = negativeLines.map(line => IQLineOffsetUtils.lineNumberToOffset(text, line))
    val negativeOffsetsInc = negativeLines.map(line => IQLineOffsetUtils.lineNumberToOffset(text, line, increment = true))
    val negativeOffsetsTrimmed = negativeLines.map(line =>
      IQLineOffsetUtils.lineNumberToOffset(text, line, increment = true, withLastNewLine = false))

    requireThat(positiveOffsets == positiveOffsets.sorted, s"positive offsets must be monotonic for text='$text'")
    requireThat(positiveOffsetsInc == positiveOffsetsInc.sorted, s"positive increment offsets must be monotonic for text='$text'")
    requireThat(positiveOffsetsTrimmed == positiveOffsetsTrimmed.sorted, s"positive trimmed offsets must be monotonic for text='$text'")
    requireThat(negativeOffsets == negativeOffsets.sorted, s"negative offsets must be monotonic for text='$text'")
    requireThat(negativeOffsetsInc == negativeOffsetsInc.sorted, s"negative increment offsets must be monotonic for text='$text'")
    requireThat(negativeOffsetsTrimmed == negativeOffsetsTrimmed.sorted, s"negative trimmed offsets must be monotonic for text='$text'")
  }

  private def verifyFormattingSafety(): Unit = {
    val empty = IQLineOffsetUtils.formatLinesWithNumbers(Array.empty[String], 0, 0, None)
    requireThat(empty.isEmpty, "formatting empty lines must return empty string")

    val lines = Array("alpha", "beta", "gamma")
    val inverted = IQLineOffsetUtils.formatLinesWithNumbers(lines, 2, 0, None)
    requireThat(inverted.isEmpty, "inverted range must not throw and should return empty string")

    val clamped = IQLineOffsetUtils.formatLinesWithNumbers(lines, -10, 100, Some(1))
    requireThat(clamped.contains("1:alpha"), "clamped output should include first line")
    requireThat(clamped.contains("2:beta"), "clamped output should include middle line")
    requireThat(clamped.contains("3:gamma"), "clamped output should include last line")
  }

  private def randomText(random: scala.util.Random): String = {
    val length = random.nextInt(120)
    val builder = new StringBuilder()
    for (_ <- 0 until length) {
      val ch =
        if (random.nextInt(6) == 0) '\n'
        else ('a' + random.nextInt(26)).toChar
      builder.append(ch)
    }
    builder.toString()
  }

  def main(args: Array[String]): Unit = {
    val fixedCases = List(
      "",
      "a",
      "\n",
      "a\n",
      "a\nb",
      "a\nb\n",
      "\n\n",
      "alpha\nbeta\ngamma",
      "alpha\nbeta\ngamma\n"
    )

    fixedCases.foreach { text =>
      verifyBounds(text)
      verifyMonotonicity(text)
    }

    val random = new scala.util.Random(0L)
    for (_ <- 1 to 300) {
      val text = randomText(random)
      verifyBounds(text)
      verifyMonotonicity(text)
    }

    verifyFormattingSafety()
    println("IQLineOffsetUtilsTest passed")
  }
}
