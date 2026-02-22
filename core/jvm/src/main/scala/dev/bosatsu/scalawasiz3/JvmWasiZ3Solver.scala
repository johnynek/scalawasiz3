package dev.bosatsu.scalawasiz3

import scala.concurrent.ExecutionContext
import scala.concurrent.Future

private[scalawasiz3] object JvmWasiZ3Solver extends Z3Solver {
  private val ec: ExecutionContext = ExecutionContext.global

  def runSmt2(input: String): Future[Z3Result] =
    Future.successful(
      Z3Result.Failure(
        message =
          "JVM runtime implementation not wired yet. Build phases compile scaffolding first, then runtime.",
        exitCode = None,
        stdout = "",
        stderr = ""
      )
    )
}
