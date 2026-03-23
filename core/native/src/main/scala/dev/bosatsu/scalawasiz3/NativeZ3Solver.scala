package dev.bosatsu.scalawasiz3

import scala.scalanative.unsafe.*

private[scalawasiz3] object NativeZ3Solver {
  lazy val default: Z3Solver = create()

  def create(): Z3Solver = new NativeZ3Solver()

  private final class NativeZ3Solver extends Z3Solver {
    override def runSmt2(input: String): Z3Result =
      Zone {
        val config = Z3NativeApi.Z3_mk_config()
        if (config == null) {
          Z3Result.Failure(
            message = "Failed creating a libz3 configuration.",
            exitCode = None,
            stdout = "",
            stderr = ""
          )
        } else {
          var context: Z3NativeApi.Z3_context = null

          try {
            context = Z3NativeApi.Z3_mk_context(config)
            if (context == null) {
              Z3Result.Failure(
                message = "Failed creating a libz3 context.",
                exitCode = None,
                stdout = "",
                stderr = ""
              )
            } else {
              // Parser/type errors are reported through the returned output stream; disable
              // libz3's default error handler so those diagnostics do not abort the process.
              Z3NativeApi.Z3_set_error_handler(context, null)
              evaluate(context, Z3RunSupport.normalizeInput(input))
            }
          } finally {
            if (context != null) Z3NativeApi.Z3_del_context(context)
            Z3NativeApi.Z3_del_config(config)
          }
        }
      }
  }

  private def evaluate(
      context: Z3NativeApi.Z3_context,
      input: String
  )(using Zone): Z3Result = {
    val outputPtr = Z3NativeApi.Z3_eval_smtlib2_string(context, toCString(input))
    // Z3 owns the returned buffer, so copy it before any later API call can invalidate it.
    val output = copyCString(outputPtr)
    val errorCode = Z3NativeApi.Z3_get_error_code(context)

    Z3RunSupport.firstSmtLibError(output) match {
      case Some(diagnostic) =>
        Z3Result.Failure(
          message = s"libz3 reported an SMT-LIB error: $diagnostic",
          exitCode = None,
          stdout = output,
          stderr = ""
        )

      case None if outputPtr == null =>
        apiFailure(
          context = context,
          message = "libz3 returned no output while evaluating SMT-LIB input.",
          stdout = output,
          errorCode = errorCode
        )

      case None if errorCode != Z3NativeApiConstants.Z3_OK =>
        apiFailure(
          context = context,
          message = "libz3 reported an API error while evaluating SMT-LIB input.",
          stdout = output,
          errorCode = errorCode
        )

      case None =>
        Z3Result.Success(stdout = output, stderr = "")
    }
  }

  private def apiFailure(
      context: Z3NativeApi.Z3_context,
      message: String,
      stdout: String,
      errorCode: Z3NativeApi.Z3_error_code
  ): Z3Result = {
    val detail = errorDetail(context, errorCode)
    val fullMessage = detail match {
      case Some(err) => s"$message $err"
      case None      => message
    }

    Z3Result.Failure(
      message = fullMessage,
      exitCode = None,
      stdout = stdout,
      stderr = ""
    )
  }

  private def errorDetail(
      context: Z3NativeApi.Z3_context,
      errorCode: Z3NativeApi.Z3_error_code
  ): Option[String] =
    if (errorCode == Z3NativeApiConstants.Z3_OK) None
    else {
      val message = copyCString(Z3NativeApi.Z3_get_error_msg(context, errorCode)).trim
      if (message.nonEmpty) Some(s"(errorCode=$errorCode, detail=$message)")
      else Some(s"(errorCode=$errorCode)")
    }

  private def copyCString(str: CString): String =
    if (str == null) ""
    else fromCString(str)
}
