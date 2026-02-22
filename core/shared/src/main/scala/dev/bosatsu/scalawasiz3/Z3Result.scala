package dev.bosatsu.scalawasiz3

sealed trait Z3Result {
  def stdout: String
  def stderr: String
  def isSuccess: Boolean
}

object Z3Result {
  final case class Success(stdout: String, stderr: String, exitCode: Int = 0) extends Z3Result {
    val isSuccess: Boolean = true
  }

  final case class Failure(
      message: String,
      exitCode: Option[Int],
      stdout: String,
      stderr: String,
      cause: Option[Throwable] = None
  ) extends Z3Result {
    val isSuccess: Boolean = false
  }
}
