package dev.bosatsu.scalawasiz3

import scala.quoted.*

private[scalawasiz3] object CompileTimeFileLoader {
  inline def readUtf8(inline pathFromRepoRoot: String): String =
    ${ readUtf8Impl('pathFromRepoRoot) }

  private def readUtf8Impl(pathExpr: Expr[String])(using Quotes): Expr[String] = {
    import quotes.reflect.*

    val relPath = pathExpr.valueOrAbort
    val sourcePath = Position.ofMacroExpansion.sourceFile.path
    val sourceFile = new java.io.File(sourcePath).getAbsoluteFile

    val projectRoot = findProjectRoot(sourceFile.getParentFile).getOrElse {
      report.errorAndAbort(s"unable to locate project root while reading: $relPath")
    }

    val target = new java.io.File(projectRoot, relPath)
    if (!target.isFile) {
      report.errorAndAbort(s"missing compile-time file: ${target.getPath}")
    }

    val src = scala.io.Source.fromFile(target, "UTF-8")
    try Expr(src.mkString)
    finally src.close()
  }

  @annotation.tailrec
  private def findProjectRoot(dir: java.io.File): Option[java.io.File] =
    if (dir == null) None
    else if (new java.io.File(dir, "build.sbt").isFile) Some(dir)
    else findProjectRoot(dir.getParentFile)
}
