package dev.bosatsu.scalawasiz3

import com.dylibso.chicory.runtime.ImportFunction
import com.dylibso.chicory.runtime.Store
import com.dylibso.chicory.wasi.WasiExitException
import com.dylibso.chicory.wasi.WasiOptions
import com.dylibso.chicory.wasi.WasiPreview1
import com.dylibso.chicory.wasm.Parser

import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.nio.charset.StandardCharsets
import scala.concurrent.ExecutionContext
import scala.concurrent.Future

private[scalawasiz3] object JvmWasiZ3Solver extends Z3Solver {
  private val ec: ExecutionContext = ExecutionContext.global

  private lazy val wasmBytesEither: Either[String, Array[Byte]] = {
    val stream = Option(getClass.getResourceAsStream(Z3WasmResource.ClasspathResourcePath))
    stream match {
      case Some(in) =>
        try Right(in.readAllBytes())
        catch {
          case t: Throwable =>
            Left(s"Failed reading embedded z3.wasm resource: ${t.getMessage}")
        } finally {
          in.close()
        }
      case None =>
        Left(s"Missing embedded z3.wasm resource at ${Z3WasmResource.ClasspathResourcePath}")
    }
  }

  def runSmt2(input: String): Future[Z3Result] = Future {
    wasmBytesEither match {
      case Left(err) =>
        Z3Result.Failure(
          message = err,
          exitCode = None,
          stdout = "",
          stderr = ""
        )

      case Right(wasmBytes) =>
        val stdin = new ByteArrayInputStream(normalizeInput(input).getBytes(StandardCharsets.UTF_8))
        val stdout = new ByteArrayOutputStream()
        val stderr = new ByteArrayOutputStream()

        val options = WasiOptions
          .builder()
          .withArguments(java.util.List.of("z3", "-smt2", "-in"))
          .withStdin(stdin)
          .withStdout(stdout)
          .withStderr(stderr)
          .build()

        val wasi = WasiPreview1.builder().withOptions(options).build()
        val hostFunctions = wasi.toHostFunctions().map(_.asInstanceOf[ImportFunction])
        val store = new Store().addFunction(hostFunctions*)

        try {
          store.instantiate("z3", Parser.parse(wasmBytes))
          Z3Result.Success(stdout = asUtf8(stdout), stderr = asUtf8(stderr))
        } catch {
          case e: WasiExitException if e.exitCode() == 0 =>
            Z3Result.Success(stdout = asUtf8(stdout), stderr = asUtf8(stderr))

          case e: WasiExitException =>
            Z3Result.Failure(
              message = s"z3 exited with code ${e.exitCode()}",
              exitCode = Some(e.exitCode()),
              stdout = asUtf8(stdout),
              stderr = asUtf8(stderr),
              cause = Some(e)
            )

          case t: Throwable =>
            Z3Result.Failure(
              message = s"Failed executing embedded z3.wasm: ${t.getMessage}",
              exitCode = None,
              stdout = asUtf8(stdout),
              stderr = asUtf8(stderr),
              cause = Some(t)
            )
        } finally {
          wasi.close()
        }
    }
  }(using ec)

  private def normalizeInput(input: String): String = {
    val trimmed = if (input.endsWith("\n")) input else s"$input\n"
    if (trimmed.contains("(exit)")) trimmed else s"$trimmed(exit)\n"
  }

  private def asUtf8(out: ByteArrayOutputStream): String =
    out.toString(StandardCharsets.UTF_8)
}
