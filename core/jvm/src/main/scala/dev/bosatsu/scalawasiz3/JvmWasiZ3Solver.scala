package dev.bosatsu.scalawasiz3

import com.dylibso.chicory.runtime.ByteArrayMemory
import com.dylibso.chicory.runtime.CompiledModule
import com.dylibso.chicory.runtime.ImportFunction
import com.dylibso.chicory.runtime.ImportValues
import com.dylibso.chicory.runtime.Instance
import com.dylibso.chicory.runtime.Machine
import com.dylibso.chicory.runtime.alloc.ExactMemAllocStrategy
import com.dylibso.chicory.wasi.WasiExitException
import com.dylibso.chicory.wasi.WasiOptions
import com.dylibso.chicory.wasi.WasiPreview1
import com.dylibso.chicory.wasm.WasmModule
import com.dylibso.chicory.wasm.types.MemoryLimits

import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.nio.charset.StandardCharsets
import java.util.function.Function

private[scalawasiz3] object JvmWasiZ3Solver {
  private val z3Arguments = java.util.List.of("z3", "-smt2", "-in")
  private val exactAllocator = new ExactMemAllocStrategy()
  private val memoryFactory: Function[MemoryLimits, com.dylibso.chicory.runtime.Memory] =
    (limits: MemoryLimits) => new ByteArrayMemory(limits, exactAllocator)

  lazy val default: Z3Solver = create()

  def create(): Z3Solver = new JvmWasiZ3Solver()

  private lazy val runtimeEither: Either[String, RuntimeState] =
    compiledModuleEither.map { compiledModule =>
      RuntimeState(
        module = compiledModule.wasmModule(),
        machineFactory = compiledModule.machineFactory()
      )
    }

  private lazy val compiledModuleEither: Either[String, CompiledModule] =
    try {
      Right(new dev.bosatsu.scalawasiz3.aot.Z3Module())
    } catch {
      case t: Throwable =>
        Left(s"Failed loading generated Chicory AOT module dev.bosatsu.scalawasiz3.aot.Z3Module: ${t.getMessage}")
    }

  private final case class RuntimeState(
      module: WasmModule,
      machineFactory: Function[Instance, Machine]
  )

  private final class JvmWasiZ3Solver extends Z3Solver {
    override def runSmt2(input: String): Z3Result =
      runtimeEither match {
        case Left(err) =>
          Z3Result.Failure(
            message = err,
            exitCode = None,
            stdout = "",
            stderr = ""
          )

        case Right(runtime) =>
          runWithRuntime(runtime, input)
      }
  }

  private def runWithRuntime(runtime: RuntimeState, input: String): Z3Result = {
    val stdin = new ByteArrayInputStream(normalizeInput(input).getBytes(StandardCharsets.UTF_8))
    val stdout = new ByteArrayOutputStream()
    val stderr = new ByteArrayOutputStream()

    val options = WasiOptions
      .builder()
      .withArguments(z3Arguments)
      .withStdin(stdin)
      .withStdout(stdout)
      .withStderr(stderr)
      .withThrowOnExit0(false)
      .build()

    val wasi = WasiPreview1.builder().withOptions(options).build()

    try {
      val hostFunctions = wasi.toHostFunctions().map(_.asInstanceOf[ImportFunction])
      val importValues = ImportValues.builder().addFunction(hostFunctions*).build()

      val builder = Instance
        .builder(runtime.module)
        .withImportValues(importValues)
        .withMemoryFactory(memoryFactory)
        .withMachineFactory(runtime.machineFactory)

      builder.build()

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
        val out = asUtf8(stdout)
        val err = asUtf8(stderr)
        if (containsStatusLine(out)) {
          // Some WASI builds may trap during teardown after writing a valid result.
          Z3Result.Success(stdout = out, stderr = err)
        } else {
          recoverFromTrap(input, out, err, t).getOrElse {
            Z3Result.Failure(
              message = s"Failed executing embedded Z3 module: ${t.getMessage}",
              exitCode = None,
              stdout = out,
              stderr = err,
              cause = Some(t)
            )
          }
        }
    } finally {
      wasi.close()
    }
  }

  private def recoverFromTrap(
      input: String,
      stdout: String,
      stderr: String,
      cause: Throwable
  ): Option[Z3Result.Failure] = {
    val trapMessage = Option(cause.getMessage).getOrElse("")
    if (!Smt2TrapDiagnostics.isUnreachableTrapMessage(trapMessage)) {
      None
    } else {
      Smt2TrapDiagnostics.fromInput(input) match {
        case Some(diag) =>
          val out = if (stdout.nonEmpty) stdout else diag.stdout
          Some(
            Z3Result.Failure(
              message = s"Failed parsing/type-checking SMT2 input: ${diag.message}",
              exitCode = None,
              stdout = out,
              stderr = stderr,
              cause = Some(cause)
            )
          )
        case None =>
          Some(
            Z3Result.Failure(
              message =
                "Embedded Z3 module trapped while handling SMT2 input, likely due invalid parser/type input.",
              exitCode = None,
              stdout = stdout,
              stderr = stderr,
              cause = Some(cause)
            )
          )
      }
    }
  }

  private def normalizeInput(input: String): String = {
    val withNl = if (input.endsWith("\n")) input else s"$input\n"
    if (withNl.contains("(exit)")) withNl else s"$withNl(exit)\n"
  }

  private def asUtf8(out: ByteArrayOutputStream): String =
    out.toString(StandardCharsets.UTF_8)

  private def containsStatusLine(stdout: String): Boolean =
    stdout.linesIterator.exists { line =>
      val trimmed = line.trim
      trimmed == "sat" || trimmed == "unsat" || trimmed == "unknown"
    }
}
