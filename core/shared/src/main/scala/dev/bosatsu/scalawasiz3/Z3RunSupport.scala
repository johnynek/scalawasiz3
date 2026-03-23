package dev.bosatsu.scalawasiz3

private[scalawasiz3] object Z3RunSupport {
  def normalizeInput(input: String): String = {
    val withTrailingNewline = if (input.endsWith("\n")) input else s"$input\n"
    if (withTrailingNewline.contains("(exit)")) withTrailingNewline
    else s"$withTrailingNewline(exit)\n"
  }

  def containsStatusLine(output: String): Boolean =
    output.linesIterator.exists { line =>
      val trimmed = line.trim
      trimmed == "sat" || trimmed == "unsat" || trimmed == "unknown"
    }

  def firstSmtLibError(output: String): Option[String] =
    output.linesIterator
      .map(_.trim)
      .find(_.startsWith("(error"))
}
