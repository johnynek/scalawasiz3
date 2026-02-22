package dev.bosatsu.scalawasiz3.nativecli

import java.io.InputStream
import java.io.OutputStream

import scala.util.control.NonFatal

object Main {
  private val BaseCommand: Array[String] = Array("z3", "-smt2", "-in")

  def main(args: Array[String]): Unit = {
    val stdinBytes = System.in.readAllBytes()
    val process =
      try new ProcessBuilder((BaseCommand ++ args)*).start()
      catch {
        case NonFatal(t) =>
          System.err.println(s"Failed to start z3: ${t.getMessage}")
          System.exit(127)
          return
      }

    val stdoutThread = pump("z3-stdout", process.getInputStream, System.out)
    val stderrThread = pump("z3-stderr", process.getErrorStream, System.err)
    val stdinThread = new Thread(
      () => {
        val processStdin = process.getOutputStream
        try {
          processStdin.write(stdinBytes)
          processStdin.flush()
        } finally {
          processStdin.close()
        }
      },
      "z3-stdin"
    )

    stdinThread.start()
    val exitCode = process.waitFor()
    stdinThread.join()
    stdoutThread.join()
    stderrThread.join()
    System.exit(exitCode)
  }

  private def pump(threadName: String, input: InputStream, output: OutputStream): Thread = {
    val thread = new Thread(
      () => {
        try {
          input.transferTo(output)
          output.flush()
        } catch {
          case NonFatal(t) =>
            System.err.println(s"Failed to relay process stream $threadName: ${t.getMessage}")
        } finally {
          input.close()
        }
      },
      threadName
    )
    thread.start()
    thread
  }
}
