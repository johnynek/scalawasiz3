package dev.bosatsu.scalawasiz3

import scala.concurrent.Future

trait Z3Solver {
  def runSmt2(input: String): Future[Z3Result]
}

object Z3Solver {
  lazy val default: Z3Solver = Z3Platform.default
}
