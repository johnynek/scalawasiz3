package dev.bosatsu.scalawasiz3

import scala.concurrent.Future

private[scalawasiz3] object JsWasiZ3Solver extends Z3Solver {
  def runSmt2(input: String): Future[Z3Result] =
    Future.successful(
      Z3Result.Failure(
        message =
          "Scala.js runtime implementation not wired yet. Build phases compile scaffolding first, then runtime.",
        exitCode = None,
        stdout = "",
        stderr = ""
      )
    )
}
