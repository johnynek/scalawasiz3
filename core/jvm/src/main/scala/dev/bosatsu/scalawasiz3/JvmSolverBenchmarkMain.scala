package dev.bosatsu.scalawasiz3

import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger

/**
 * Simple benchmark harness for measuring runSmt2 throughput on the JVM runtime.
 *
 * Usage:
 *   sbt "project coreJVM" "runMain dev.bosatsu.scalawasiz3.JvmSolverBenchmarkMain --warmup 20 --iterations 200 --threads 1"
 */
object JvmSolverBenchmarkMain {
  private sealed trait SolverMode
  private object SolverMode {
    case object Shared extends SolverMode
    case object Isolated extends SolverMode

    def parse(value: String): SolverMode =
      value.trim.toLowerCase match {
        case "shared" => Shared
        case "isolated" => Isolated
        case other =>
          throw new IllegalArgumentException(
            s"Unknown --mode value: $other (expected: shared|isolated)"
          )
      }
  }

  private final case class Config(
      warmupIterations: Int = 20,
      measuredIterations: Int = 200,
      threads: Int = 1,
      mode: SolverMode = SolverMode.Shared
  )

  private final case class SampleStats(
      count: Int,
      totalWallNanos: Long,
      totalCallNanos: Long,
      minNanos: Long,
      maxNanos: Long,
      p50Nanos: Long,
      p95Nanos: Long
  ) {
    def callsPerSecond: Double = {
      val seconds = totalWallNanos.toDouble / 1e9
      if (seconds == 0d) Double.PositiveInfinity else count.toDouble / seconds
    }

    def averageCallMillis: Double = totalCallNanos.toDouble / count.toDouble / 1e6

    def averageWallMillisPerCall: Double = totalWallNanos.toDouble / count.toDouble / 1e6
  }

  private val BenchmarkInput: String =
    """(set-option :produce-models true)
      |(declare-const x Int)
      |(declare-const y Int)
      |(assert (> x 10))
      |(assert (< x 20))
      |(assert (= y (+ x 4)))
      |(check-sat)
      |(get-model)
      |""".stripMargin

  def main(args: Array[String]): Unit = {
    val cfg = parseConfig(args.toList)
    validateConfig(cfg)

    println(s"Warmup iterations: ${cfg.warmupIterations}")
    println(s"Measured iterations: ${cfg.measuredIterations}")
    println(s"Threads: ${cfg.threads}")
    println(s"Mode: ${modeName(cfg.mode)}")

    val solverFactory = cfg.mode match {
      case SolverMode.Shared =>
        val shared = Z3Solver.default
        () => shared
      case SolverMode.Isolated =>
        () => Z3Solver.create()
    }

    warmup(solverFactory, cfg.warmupIterations)
    val stats = runMeasured(solverFactory, cfg.measuredIterations, cfg.threads)

    println(s"Total calls: ${stats.count}")
    println(f"Total time: ${stats.totalWallNanos.toDouble / 1e9}%.3f s")
    println(f"Throughput: ${stats.callsPerSecond}%.2f calls/s")
    println(f"Avg call latency: ${stats.averageCallMillis}%.3f ms")
    println(f"Avg wall time per call: ${stats.averageWallMillisPerCall}%.3f ms")
    println(f"Min latency: ${toMillis(stats.minNanos)}%.3f ms")
    println(f"P50 latency: ${toMillis(stats.p50Nanos)}%.3f ms")
    println(f"P95 latency: ${toMillis(stats.p95Nanos)}%.3f ms")
    println(f"Max latency: ${toMillis(stats.maxNanos)}%.3f ms")
  }

  private def warmup(solverFactory: () => Z3Solver, iterations: Int): Unit = {
    val solver = solverFactory()
    var i = 0
    while (i < iterations) {
      assertSat(solver.runSmt2(BenchmarkInput), s"warmup[$i]")
      i += 1
    }
  }

  private def runMeasured(
      solverFactory: () => Z3Solver,
      iterations: Int,
      threads: Int
  ): SampleStats = {
    val callsPerThread = iterations / threads
    val remainder = iterations % threads
    val allSamples = Array.ofDim[Long](iterations)
    val nextWrite = new AtomicInteger(0)

    val startLatch = new CountDownLatch(1)
    val doneLatch = new CountDownLatch(threads)
    val errors = new AtomicInteger(0)
    val runStart = System.nanoTime()

    var t = 0
    while (t < threads) {
      val extra = if (t < remainder) 1 else 0
      val thisThreadIterations = callsPerThread + extra
      val thread = new Thread(
        new Runnable {
          override def run(): Unit = {
            val solver = solverFactory()
            try {
              startLatch.await()
              var i = 0
              while (i < thisThreadIterations) {
                val t0 = System.nanoTime()
                val result = solver.runSmt2(BenchmarkInput)
                val dt = System.nanoTime() - t0
                assertSat(result, s"run[$i]")
                val idx = nextWrite.getAndIncrement()
                allSamples(idx) = dt
                i += 1
              }
            } catch {
              case _: Throwable =>
                errors.incrementAndGet()
            } finally {
              doneLatch.countDown()
            }
          }
        },
        s"z3-bench-$t"
      )
      thread.start()
      t += 1
    }

    startLatch.countDown()
    doneLatch.await()
    val runTotalNanos = System.nanoTime() - runStart

    if (errors.get() > 0) {
      throw new RuntimeException(s"Benchmark failed with ${errors.get()} thread errors")
    }

    val sorted = java.util.Arrays.copyOf(allSamples, allSamples.length)
    java.util.Arrays.sort(sorted)
    val min = sorted(0)
    val max = sorted(sorted.length - 1)
    val p50 = percentile(sorted, 50)
    val p95 = percentile(sorted, 95)
    val callTotalNanos = sorted.foldLeft(0L)(_ + _)
    SampleStats(
      count = iterations,
      totalWallNanos = runTotalNanos,
      totalCallNanos = callTotalNanos,
      minNanos = min,
      maxNanos = max,
      p50Nanos = p50,
      p95Nanos = p95
    )
  }

  private def percentile(sorted: Array[Long], p: Int): Long = {
    val idx = math.min(sorted.length - 1, math.max(0, ((sorted.length - 1L) * p / 100L).toInt))
    sorted(idx)
  }

  private def assertSat(result: Z3Result, context: String): Unit =
    result match {
      case Z3Result.Success(stdout, stderr, _) =>
        if (!stdout.linesIterator.exists(_.trim == "sat")) {
          throw new RuntimeException(
            s"Expected sat status in $context\nstdout:\n$stdout\nstderr:\n$stderr"
          )
        }
      case Z3Result.Failure(msg, _, stdout, stderr, _) =>
        throw new RuntimeException(
          s"Solver failed in $context: $msg\nstdout:\n$stdout\nstderr:\n$stderr"
        )
    }

  private def toMillis(nanos: Long): Double = nanos.toDouble / 1e6

  private def parseConfig(args: List[String]): Config = {
    @annotation.tailrec
    def loop(rest: List[String], acc: Config): Config =
      rest match {
        case Nil => acc
        case "--warmup" :: value :: tail =>
          loop(tail, acc.copy(warmupIterations = parsePositiveInt("--warmup", value)))
        case "--iterations" :: value :: tail =>
          loop(tail, acc.copy(measuredIterations = parsePositiveInt("--iterations", value)))
        case "--threads" :: value :: tail =>
          loop(tail, acc.copy(threads = parsePositiveInt("--threads", value)))
        case "--mode" :: value :: tail =>
          loop(tail, acc.copy(mode = SolverMode.parse(value)))
        case "--help" :: _ =>
          printUsageAndExit()
          acc
        case flag :: _ =>
          throw new IllegalArgumentException(s"Unknown argument: $flag")
      }

    loop(args, Config())
  }

  private def parsePositiveInt(flag: String, value: String): Int = {
    val parsed =
      try value.toInt
      catch {
        case _: NumberFormatException =>
          throw new IllegalArgumentException(s"$flag expects an integer, got: $value")
      }
    if (parsed <= 0) {
      throw new IllegalArgumentException(s"$flag must be > 0, got: $parsed")
    }
    parsed
  }

  private def validateConfig(cfg: Config): Unit = {
    if (cfg.threads <= 0) {
      throw new IllegalArgumentException("threads must be > 0")
    }
    if (cfg.measuredIterations < cfg.threads) {
      throw new IllegalArgumentException(
        s"iterations (${cfg.measuredIterations}) must be >= threads (${cfg.threads})"
      )
    }
  }

  private def printUsageAndExit(): Unit = {
    val text =
      """Usage:
        |  runMain dev.bosatsu.scalawasiz3.JvmSolverBenchmarkMain [--warmup N] [--iterations N] [--threads N] [--mode shared|isolated]
        |
        |Defaults:
        |  --warmup 20
        |  --iterations 200
        |  --threads 1
        |  --mode shared
        |""".stripMargin
    Console.out.println(text)
    sys.exit(0)
  }

  private def modeName(mode: SolverMode): String =
    mode match {
      case SolverMode.Shared => "shared"
      case SolverMode.Isolated => "isolated"
    }
}
