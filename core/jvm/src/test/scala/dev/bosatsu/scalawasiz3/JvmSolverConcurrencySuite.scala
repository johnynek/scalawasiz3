package dev.bosatsu.scalawasiz3

import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.CountDownLatch

class JvmSolverConcurrencySuite extends munit.FunSuite {
  test("multiple solver instances can execute concurrently") {
    val threadCount = 4
    val runsPerThread = 4
    val start = new CountDownLatch(1)
    val done = new CountDownLatch(threadCount)
    val failures = new ConcurrentLinkedQueue[String]()

    var t = 0
    while (t < threadCount) {
      val threadIndex = t
      val thread = new Thread(
        new Runnable {
          override def run(): Unit = {
            val solver = Z3Solver.create()
            try {
              start.await()
              var i = 0
              while (i < runsPerThread) {
                solver.runSmt2("(check-sat)") match {
                  case Z3Result.Success(stdout, _, _) =>
                    val hasSat = stdout.linesIterator.exists(_.trim == "sat")
                    if (!hasSat) {
                      failures.add(s"missing sat status on thread=$threadIndex run=$i")
                    }
                  case Z3Result.Failure(message, _, _, _, _) =>
                    failures.add(s"solver failure on thread=$threadIndex run=$i: $message")
                }
                i += 1
              }
            } catch {
              case e: Throwable =>
                failures.add(s"thread failure on thread=$threadIndex: ${e.getMessage}")
            } finally {
              done.countDown()
            }
          }
        },
        s"z3-concurrency-$threadIndex"
      )
      thread.start()
      t += 1
    }

    start.countDown()
    done.await()

    assertEquals(failures.size(), 0, failures.toString)
  }
}
