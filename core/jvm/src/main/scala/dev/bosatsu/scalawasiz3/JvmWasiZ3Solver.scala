package dev.bosatsu.scalawasiz3

import com.dylibso.chicory.compiler.InterpreterFallback
import com.dylibso.chicory.compiler.MachineFactoryCompiler
import com.dylibso.chicory.experimental.dircache.DirectoryCache
import com.dylibso.chicory.runtime.ByteArrayMemory
import com.dylibso.chicory.runtime.ImportFunction
import com.dylibso.chicory.runtime.ImportValues
import com.dylibso.chicory.runtime.Instance
import com.dylibso.chicory.runtime.Machine
import com.dylibso.chicory.runtime.alloc.ExactMemAllocStrategy
import com.dylibso.chicory.wasi.WasiExitException
import com.dylibso.chicory.wasi.WasiOptions
import com.dylibso.chicory.wasi.WasiPreview1
import com.dylibso.chicory.wasm.Parser
import com.dylibso.chicory.wasm.WasmModule
import com.dylibso.chicory.wasm.types.MemoryLimits

import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.nio.charset.StandardCharsets
import java.nio.file.Paths
import java.util.function.Function

private[scalawasiz3] object JvmWasiZ3Solver {
  private val z3Arguments = java.util.List.of("z3", "-smt2", "-in")
  private val runtimeCompilerCacheDirProperty = "scalawasiz3.chicory.runtimeCompilerCacheDir"
  private val exactAllocator = new ExactMemAllocStrategy()
  private val memoryFactory: Function[MemoryLimits, com.dylibso.chicory.runtime.Memory] =
    (limits: MemoryLimits) => new ByteArrayMemory(limits, exactAllocator)

  lazy val default: Z3Solver = create()

  def create(): Z3Solver = new JvmWasiZ3Solver()

  private lazy val runtimeEither: Either[String, RuntimeState] =
    wasmModuleEither.map { module =>
      RuntimeState(module = module, machineFactory = compileMachineFactory(module))
    }

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

  private lazy val wasmModuleEither: Either[String, WasmModule] =
    wasmBytesEither.flatMap { wasmBytes =>
      try Right(Parser.parse(wasmBytes))
      catch {
        case t: Throwable =>
          Left(s"Failed parsing embedded z3.wasm: ${t.getMessage}")
      }
    }

  private def compileMachineFactory(module: WasmModule): Option[Function[Instance, Machine]] = {
    try {
      val builder = MachineFactoryCompiler
        .builder(module)
        .withInterpreterFallback(InterpreterFallback.SILENT)

      runtimeCompilerCacheDir.foreach { cacheDir =>
        try {
          builder.withCache(new DirectoryCache(Paths.get(cacheDir)))
        } catch {
          case _: Throwable =>
            ()
        }
      }

      Some(builder.compile())
    } catch {
      case _: Throwable =>
        None
    }
  }

  private lazy val runtimeCompilerCacheDir: Option[String] =
    Option(System.getProperty(runtimeCompilerCacheDirProperty)).map(_.trim).filter(_.nonEmpty)

  private final case class RuntimeState(
      module: WasmModule,
      machineFactory: Option[Function[Instance, Machine]]
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

      runtime.machineFactory.foreach(factory => builder.withMachineFactory(factory))
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
          Z3Result.Failure(
            message = s"Failed executing embedded z3.wasm: ${t.getMessage}",
            exitCode = None,
            stdout = out,
            stderr = err,
            cause = Some(t)
          )
        }
    } finally {
      wasi.close()
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
