package dev.bosatsu.scalawasiz3

trait Z3Solver {
  def runSmt2(input: String): Z3Result
}

object Z3Solver {
  lazy val default: Z3Solver = Z3Platform.default
}
