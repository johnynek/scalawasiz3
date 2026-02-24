package dev.bosatsu.scalawasiz3

import scala.collection.mutable.ArrayBuilder
import scala.scalajs.js
import scala.scalajs.js.typedarray.ArrayBuffer
import scala.scalajs.js.typedarray.DataView
import scala.scalajs.js.typedarray.Uint8Array

import java.nio.charset.StandardCharsets

private[scalawasiz3] object JsWasiZ3Solver extends Z3Solver {
  def runSmt2(input: String): Z3Result = {
    val wasmOrError: Either[Throwable, Option[Array[Byte]]] =
      try Right(EmbeddedWasmBytes.wasm)
      catch {
        case t: Throwable => Left(t)
      }

    wasmOrError match {
      case Left(t) =>
        val msg = Option(t.getMessage).getOrElse(t.toString)
        Z3Result.Failure(
          message = s"Failed loading embedded z3.wasm for Scala.js: $msg",
          exitCode = None,
          stdout = "",
          stderr = "",
          cause = Some(t)
        )
      case Right(None) =>
        Z3Result.Failure(
          message =
            "Embedded z3.wasm could not be decoded/decompressed for this Scala.js runtime.",
          exitCode = None,
          stdout = "",
          stderr = ""
        )
      case Right(Some(wasm)) =>
        if (wasm.isEmpty) {
          Z3Result.Failure(
            message =
              "Embedded z3.wasm is empty for Scala.js. Run scripts/build-z3-wasi.sh before publishing or running.",
            exitCode = None,
            stdout = "",
            stderr = ""
          )
        } else {
          val wasi = new MiniWasi(normalizeInput(input))
          try {
            val webAssembly = js.Dynamic.global.selectDynamic("WebAssembly")
            val moduleCtor = webAssembly.selectDynamic("Module")
            val instanceCtor = webAssembly.selectDynamic("Instance")

            val module = js.Dynamic.newInstance(moduleCtor)(toUint8Array(wasm))
            val importObject = js.Dynamic.literal("wasi_snapshot_preview1" -> wasi.importObject)

            val instance = js.Dynamic.newInstance(instanceCtor)(module, importObject)
            wasi.bindInstance(instance)

            val startFn = instance.exports.selectDynamic("_start")
            if (js.isUndefined(startFn) || startFn == null) {
              Z3Result.Failure(
                message = "The embedded z3.wasm does not export _start; expected a WASI command module.",
                exitCode = None,
                stdout = wasi.stdoutString,
                stderr = wasi.stderrString
              )
            } else {
              try {
                startFn.asInstanceOf[js.Function0[Unit]].apply()
                wasi.resultAfterRun()
              } catch {
                case jse: js.JavaScriptException =>
                  wasi.resultFromException(jse)
              }
            }
          } catch {
            case jse: js.JavaScriptException =>
              wasi.resultFromException(jse)
            case t: Throwable =>
              Z3Result.Failure(
                message = s"Failed executing z3.wasm on Scala.js: ${t.getMessage}",
                exitCode = None,
                stdout = wasi.stdoutString,
                stderr = wasi.stderrString,
                cause = Some(t)
              )
          }
        }
    }
  }

  private def normalizeInput(input: String): String = {
    val withNl = if (input.endsWith("\n")) input else s"$input\n"
    if (withNl.contains("(exit)")) withNl else s"$withNl(exit)\n"
  }

  private def toUint8Array(bytes: Array[Byte]): Uint8Array = {
    val out = new Uint8Array(bytes.length)
    var i = 0
    while (i < bytes.length) {
      out(i) = (bytes(i).toInt & 0xff).toShort
      i += 1
    }
    out
  }

  private final class MiniWasi(inputText: String) {
    private val ErrnoSuccess = 0
    private val ErrnoBadf = 8
    private val ErrnoInval = 28
    private val ErrnoNotsup = 58
    private val ErrnoNosys = 52
    private val ErrnoSpipe = 70

    private val FileTypeCharacterDevice = 2

    private val stdinBytes = inputText.getBytes(StandardCharsets.UTF_8)
    private var stdinPos = 0

    private val stdoutBuilder = ArrayBuilder.make[Byte]
    private val stderrBuilder = ArrayBuilder.make[Byte]

    private val args = Array("z3", "-smt2", "-in")
    private val argsBytes = args.map(_.getBytes(StandardCharsets.UTF_8))

    private var instanceDyn: js.UndefOr[js.Dynamic] = js.undefined

    private val ExitCodeField = "__scalawasiz3_exit_code__"

    def bindInstance(instance: js.Dynamic): Unit = {
      instanceDyn = instance
    }

    def stdoutString: String = new String(stdoutBuilder.result(), StandardCharsets.UTF_8)
    def stderrString: String = new String(stderrBuilder.result(), StandardCharsets.UTF_8)

    def resultAfterRun(): Z3Result = {
      Z3Result.Success(stdout = stdoutString, stderr = stderrString)
    }

    def resultFromException(jse: js.JavaScriptException): Z3Result = {
      val exitCode = extractExitCode(jse.exception)
      exitCode match {
        case Some(0) =>
          Z3Result.Success(stdout = stdoutString, stderr = stderrString)
        case Some(code) =>
          Z3Result.Failure(
            message = s"z3 exited with code $code",
            exitCode = Some(code),
            stdout = stdoutString,
            stderr = stderrString,
            cause = Some(jse)
          )
        case None =>
          if (containsStatusLine(stdoutString)) {
            Z3Result.Success(stdout = stdoutString, stderr = stderrString)
          } else {
            Z3Result.Failure(
              message = s"Scala.js runtime exception while running z3.wasm: ${jse.getMessage}",
              exitCode = None,
              stdout = stdoutString,
              stderr = stderrString,
              cause = Some(jse)
            )
          }
      }
    }

    private def containsStatusLine(stdout: String): Boolean =
      stdout.linesIterator.exists { line =>
        val trimmed = line.trim
        trimmed == "sat" || trimmed == "unsat" || trimmed == "unknown"
      }

    private def extractExitCode(value: Any): Option[Int] = {
      val dyn = value.asInstanceOf[js.Dynamic]
      val field = dyn.selectDynamic(ExitCodeField)
      if (js.isUndefined(field) || field == null) None
      else Some(field.asInstanceOf[Int])
    }

    private def memoryBuffer(): ArrayBuffer = {
      if (instanceDyn.isEmpty) {
        throw new IllegalStateException("WASI memory access before wasm instance was bound")
      }
      val mem = instanceDyn.get.exports.selectDynamic("memory")
      if (js.isUndefined(mem) || mem == null) {
        throw new IllegalStateException("wasi module does not export memory")
      }
      mem.selectDynamic("buffer").asInstanceOf[ArrayBuffer]
    }

    private def memoryView(): DataView = new DataView(memoryBuffer())

    private def readU32(ptr: Int): Int =
      memoryView().getUint32(ptr, littleEndian = true).toInt

    private def writeU8(ptr: Int, value: Int): Unit =
      memoryView().setUint8(ptr, value.toShort)

    private def writeU16(ptr: Int, value: Int): Unit =
      memoryView().setUint16(ptr, value, littleEndian = true)

    private def writeU32(ptr: Int, value: Int): Unit =
      memoryView().setUint32(ptr, value, littleEndian = true)

    private def writeU64(ptr: Int, value: Long): Unit = {
      val low = (value & 0xffffffffL).toInt
      val high = ((value >>> 32) & 0xffffffffL).toInt
      writeU32(ptr, low)
      writeU32(ptr + 4, high)
    }

    private def readBytes(ptr: Int, len: Int): Array[Byte] = {
      val mem = new Uint8Array(memoryBuffer())
      val out = new Array[Byte](len)
      var i = 0
      while (i < len) {
        out(i) = mem(ptr + i).toByte
        i += 1
      }
      out
    }

    private def writeBytes(ptr: Int, bytes: Array[Byte], off: Int, len: Int): Unit = {
      val mem = new Uint8Array(memoryBuffer())
      var i = 0
      while (i < len) {
        mem(ptr + i) = (bytes(off + i).toInt & 0xff).toShort
        i += 1
      }
    }

    private def argsSizesGet(argcPtr: Int, argvBufSizePtr: Int): Int = {
      val totalBytes = argsBytes.foldLeft(0)(_ + _.length + 1)
      writeU32(argcPtr, argsBytes.length)
      writeU32(argvBufSizePtr, totalBytes)
      ErrnoSuccess
    }

    private def argsGet(argvPtr: Int, argvBufPtr: Int): Int = {
      var argv = argvPtr
      var buf = argvBufPtr
      var idx = 0
      while (idx < argsBytes.length) {
        val arg = argsBytes(idx)
        writeU32(argv, buf)
        writeBytes(buf, arg, 0, arg.length)
        writeU8(buf + arg.length, 0)
        argv += 4
        buf += arg.length + 1
        idx += 1
      }
      ErrnoSuccess
    }

    private def environSizesGet(environCountPtr: Int, environBufSizePtr: Int): Int = {
      writeU32(environCountPtr, 0)
      writeU32(environBufSizePtr, 0)
      ErrnoSuccess
    }

    private def environGet(environPtr: Int, environBufPtr: Int): Int = ErrnoSuccess

    private def fdRead(fd: Int, iovsPtr: Int, iovsLen: Int, nreadPtr: Int): Int = {
      if (fd != 0) return ErrnoBadf

      var totalRead = 0
      var i = 0
      while (i < iovsLen && stdinPos < stdinBytes.length) {
        val iovBase = iovsPtr + (i * 8)
        val dstPtr = readU32(iovBase)
        val dstLen = readU32(iovBase + 4)
        val available = stdinBytes.length - stdinPos
        val toCopy = math.min(dstLen, available)
        if (toCopy > 0) {
          writeBytes(dstPtr, stdinBytes, stdinPos, toCopy)
          stdinPos += toCopy
          totalRead += toCopy
        }
        i += 1
      }

      writeU32(nreadPtr, totalRead)
      ErrnoSuccess
    }

    private def fdWrite(fd: Int, iovsPtr: Int, iovsLen: Int, nwrittenPtr: Int): Int = {
      val target =
        if (fd == 1) stdoutBuilder
        else if (fd == 2) stderrBuilder
        else return ErrnoBadf

      var total = 0
      var i = 0
      while (i < iovsLen) {
        val iovBase = iovsPtr + (i * 8)
        val srcPtr = readU32(iovBase)
        val srcLen = readU32(iovBase + 4)
        val bytes = readBytes(srcPtr, srcLen)
        target ++= bytes
        total += srcLen
        i += 1
      }

      writeU32(nwrittenPtr, total)
      ErrnoSuccess
    }

    private def fdClose(fd: Int): Int = if (fd >= 0 && fd <= 2) ErrnoSuccess else ErrnoBadf

    private def fdFdstatGet(fd: Int, fdstatPtr: Int): Int = {
      if (fd < 0 || fd > 2) return ErrnoBadf
      writeU8(fdstatPtr, FileTypeCharacterDevice)
      writeU16(fdstatPtr + 2, 0)
      writeU64(fdstatPtr + 8, 0L)
      writeU64(fdstatPtr + 16, 0L)
      ErrnoSuccess
    }

    private def fdSeek(fd: Int, offset: js.Any, whence: Int, newOffsetPtr: Int): Int = {
      if (fd >= 0 && fd <= 2) ErrnoSpipe else ErrnoBadf
    }

    private def fdTell(fd: Int, offsetPtr: Int): Int = {
      if (fd >= 0 && fd <= 2) ErrnoSpipe else ErrnoBadf
    }

    private def clockResGet(clockId: Int, resultPtr: Int): Int = {
      writeU64(resultPtr, 1L)
      ErrnoSuccess
    }

    private def clockTimeGet(clockId: Int, precision: js.Any, resultPtr: Int): Int = {
      val nanos = System.currentTimeMillis() * 1000000L
      writeU64(resultPtr, nanos)
      ErrnoSuccess
    }

    private def randomGet(bufPtr: Int, bufLen: Int): Int = {
      val mem = new Uint8Array(memoryBuffer())
      var i = 0
      while (i < bufLen) {
        mem(bufPtr + i) = ((Math.random() * 256.0).toInt & 0xff).toShort
        i += 1
      }
      ErrnoSuccess
    }

    private def procExit(code: Int): Unit = {
      throw js.JavaScriptException(js.Dynamic.literal(ExitCodeField -> code))
    }

    private def unsupported(name: String): Int = ErrnoNosys

    val importObject: js.Dynamic = {
      val obj = js.Dynamic.literal()

      obj.updateDynamic("args_get")((argvPtr: Int, argvBufPtr: Int) => argsGet(argvPtr, argvBufPtr))
      obj.updateDynamic("args_sizes_get")((argcPtr: Int, argvBufSizePtr: Int) => argsSizesGet(argcPtr, argvBufSizePtr))
      obj.updateDynamic("environ_get")((environPtr: Int, environBufPtr: Int) => environGet(environPtr, environBufPtr))
      obj.updateDynamic("environ_sizes_get")((environCountPtr: Int, environBufSizePtr: Int) => environSizesGet(environCountPtr, environBufSizePtr))

      obj.updateDynamic("fd_read")((fd: Int, iovsPtr: Int, iovsLen: Int, nreadPtr: Int) => fdRead(fd, iovsPtr, iovsLen, nreadPtr))
      obj.updateDynamic("fd_write")((fd: Int, iovsPtr: Int, iovsLen: Int, nwrittenPtr: Int) => fdWrite(fd, iovsPtr, iovsLen, nwrittenPtr))
      obj.updateDynamic("fd_close")((fd: Int) => fdClose(fd))
      obj.updateDynamic("fd_fdstat_get")((fd: Int, fdstatPtr: Int) => fdFdstatGet(fd, fdstatPtr))
      obj.updateDynamic("fd_seek")((fd: Int, offset: js.Any, whence: Int, newOffsetPtr: Int) =>
        fdSeek(fd, offset, whence, newOffsetPtr)
      )
      obj.updateDynamic("fd_tell")((fd: Int, offsetPtr: Int) => fdTell(fd, offsetPtr))

      obj.updateDynamic("clock_res_get")((clockId: Int, resultPtr: Int) => clockResGet(clockId, resultPtr))
      obj.updateDynamic("clock_time_get")((clockId: Int, precision: js.Any, resultPtr: Int) =>
        clockTimeGet(clockId, precision, resultPtr)
      )
      obj.updateDynamic("random_get")((bufPtr: Int, bufLen: Int) => randomGet(bufPtr, bufLen))

      obj.updateDynamic("proc_exit")((code: Int) => procExit(code))
      obj.updateDynamic("sched_yield")(() => ErrnoSuccess)

      obj.updateDynamic("fd_advise")((fd: Int, offset: js.Any, len: js.Any, advice: Int) => unsupported("fd_advise"))
      obj.updateDynamic("fd_allocate")((fd: Int, offset: js.Any, len: js.Any) => unsupported("fd_allocate"))
      obj.updateDynamic("fd_datasync")((fd: Int) => unsupported("fd_datasync"))
      obj.updateDynamic("fd_fdstat_set_flags")((fd: Int, flags: Int) => unsupported("fd_fdstat_set_flags"))
      obj.updateDynamic("fd_fdstat_set_rights")((fd: Int, rightsBase: js.Any, rightsInheriting: js.Any) =>
        unsupported("fd_fdstat_set_rights")
      )
      obj.updateDynamic("fd_filestat_get")((fd: Int, buf: Int) => unsupported("fd_filestat_get"))
      obj.updateDynamic("fd_filestat_set_size")((fd: Int, size: js.Any) => unsupported("fd_filestat_set_size"))
      obj.updateDynamic("fd_filestat_set_times")((fd: Int, atim: js.Any, mtim: js.Any, fstFlags: Int) =>
        unsupported("fd_filestat_set_times")
      )
      obj.updateDynamic("fd_pread")((fd: Int, iovs: Int, iovsLen: Int, offset: js.Any, nread: Int) =>
        unsupported("fd_pread")
      )
      obj.updateDynamic("fd_prestat_dir_name")((fd: Int, path: Int, pathLen: Int) => unsupported("fd_prestat_dir_name"))
      obj.updateDynamic("fd_prestat_get")((fd: Int, prestat: Int) => unsupported("fd_prestat_get"))
      obj.updateDynamic("fd_pwrite")((fd: Int, iovs: Int, iovsLen: Int, offset: js.Any, nwritten: Int) =>
        unsupported("fd_pwrite")
      )
      obj.updateDynamic("fd_readdir")((fd: Int, buf: Int, bufLen: Int, cookie: js.Any, bufUsed: Int) =>
        unsupported("fd_readdir")
      )
      obj.updateDynamic("fd_renumber")((fd: Int, to: Int) => unsupported("fd_renumber"))
      obj.updateDynamic("fd_sync")((fd: Int) => unsupported("fd_sync"))
      obj.updateDynamic("path_create_directory")((fd: Int, path: Int, pathLen: Int) => unsupported("path_create_directory"))
      obj.updateDynamic("path_filestat_get")((fd: Int, flags: Int, path: Int, pathLen: Int, buf: Int) =>
        unsupported("path_filestat_get")
      )
      obj.updateDynamic("path_filestat_set_times")(
        (fd: Int, flags: Int, path: Int, pathLen: Int, atim: js.Any, mtim: js.Any, fstFlags: Int) =>
          unsupported("path_filestat_set_times")
      )
      obj.updateDynamic("path_link")(
        (oldFd: Int, oldFlags: Int, oldPath: Int, oldPathLen: Int, newFd: Int, newPath: Int, newPathLen: Int) =>
          unsupported("path_link")
      )
      obj.updateDynamic("path_open")(
        (
            dirfd: Int,
            dirflags: Int,
            path: Int,
            pathLen: Int,
            oflags: Int,
            fsRightsBase: js.Any,
            fsRightsInheriting: js.Any,
            fdflags: Int,
            openedFdPtr: Int
        ) => unsupported("path_open")
      )
      obj.updateDynamic("path_readlink")((fd: Int, path: Int, pathLen: Int, buf: Int, bufLen: Int, bufUsed: Int) =>
        unsupported("path_readlink")
      )
      obj.updateDynamic("path_remove_directory")((fd: Int, path: Int, pathLen: Int) => unsupported("path_remove_directory"))
      obj.updateDynamic("path_rename")((fd: Int, oldPath: Int, oldPathLen: Int, newFd: Int, newPath: Int, newPathLen: Int) =>
        unsupported("path_rename")
      )
      obj.updateDynamic("path_symlink")((oldPath: Int, oldPathLen: Int, fd: Int, newPath: Int, newPathLen: Int) =>
        unsupported("path_symlink")
      )
      obj.updateDynamic("path_unlink_file")((fd: Int, path: Int, pathLen: Int) => unsupported("path_unlink_file"))
      obj.updateDynamic("poll_oneoff")((in: Int, out: Int, nsubscriptions: Int, nevents: Int) => unsupported("poll_oneoff"))
      obj.updateDynamic("proc_raise")((sig: Int) => unsupported("proc_raise"))
      obj.updateDynamic("sock_accept")((fd: Int, flags: Int, outFd: Int) => unsupported("sock_accept"))
      obj.updateDynamic("sock_recv")((fd: Int, riData: Int, riDataLen: Int, riFlags: Int, roDataLen: Int, roFlags: Int) =>
        unsupported("sock_recv")
      )
      obj.updateDynamic("sock_send")((fd: Int, siData: Int, siDataLen: Int, siFlags: Int, soDataLen: Int) =>
        unsupported("sock_send")
      )
      obj.updateDynamic("sock_shutdown")((fd: Int, how: Int) => unsupported("sock_shutdown"))

      obj
    }
  }
}
