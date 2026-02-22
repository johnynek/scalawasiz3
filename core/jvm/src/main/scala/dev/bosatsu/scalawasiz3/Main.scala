package dev.bosatsu.scalawasiz3

import java.nio.charset.StandardCharsets

object Main {
  def main(args: Array[String]): Unit = {
    val input = new String(System.in.readAllBytes(), StandardCharsets.UTF_8)
    val result = Z3Solver.default.runSmt2(input)

    if (result.stdout.nonEmpty) {
      System.out.print(result.stdout)
    }
    if (result.stderr.nonEmpty) {
      System.err.print(result.stderr)
    }

    val exitCode = result match {
      case Z3Result.Success(_, _, code)                 => code
      case Z3Result.Failure(_, Some(code), _, _, _)    => code
      case Z3Result.Failure(message, None, _, _, _) =>
        if (result.stderr.isEmpty && message.nonEmpty) {
          System.err.println(message)
        }
        1
    }

    System.exit(exitCode)
  }
}
