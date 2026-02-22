package dev.bosatsu.scalawasiz3

import scala.scalajs.js
import scala.scalajs.js.annotation.JSImport

@js.native
@JSImport("node:fs", JSImport.Namespace)
private object NodeFs extends js.Object {
  def readFileSync(fd: Int, encoding: String): String = js.native
}

object NodeMain {
  def main(args: Array[String]): Unit = {
    val input = NodeFs.readFileSync(0, "utf8")
    val result = Z3Solver.default.runSmt2(input)

    if (result.stdout.nonEmpty) {
      print(result.stdout)
    }
    if (result.stderr.nonEmpty) {
      System.err.print(result.stderr)
    }

    val exitCode = result match {
      case Z3Result.Success(_, _, code)              => code
      case Z3Result.Failure(_, Some(code), _, _, _) => code
      case Z3Result.Failure(message, None, _, _, _) =>
        if (result.stderr.isEmpty && message.nonEmpty) {
          System.err.println(message)
        }
        1
    }

    js.Dynamic.global.selectDynamic("process").exit(exitCode)
  }
}
