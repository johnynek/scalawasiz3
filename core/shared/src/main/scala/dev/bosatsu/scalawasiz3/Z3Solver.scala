package dev.bosatsu.scalawasiz3

trait Z3Solver {
  def runSmt2(input: String): Z3Result
}

object Z3Solver {
  lazy val default: Z3Solver = Z3Platform.default

  /**
   * Create a solver handle suitable for reuse in one thread or worker.
   *
   * `default` remains available for callers that want a singleton handle.
   */
  def create(): Z3Solver = Z3Platform.create()
}
