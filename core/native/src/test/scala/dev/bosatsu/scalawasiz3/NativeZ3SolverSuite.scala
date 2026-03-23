package dev.bosatsu.scalawasiz3

class NativeZ3SolverSuite extends munit.FunSuite {
  test("native backend returns solver output on stdout with empty stderr") {
    Z3Solver.default.runSmt2("(check-sat)") match {
      case Z3Result.Success(stdout, stderr, exitCode) =>
        assertEquals(exitCode, 0)
        assertEquals(stderr, "")
        assertEquals(stdout.linesIterator.map(_.trim).find(_.nonEmpty), Some("sat"))

      case Z3Result.Failure(message, _, stdout, stderr, _) =>
        fail(s"expected success, got failure: $message\nstdout:\n$stdout\nstderr:\n$stderr")
    }
  }

  test("native backend surfaces SMT-LIB diagnostics in the returned output stream") {
    Z3Solver.default.runSmt2(
      """(assert (> y 0))
        |(check-sat)
        |""".stripMargin
    ) match {
      case Z3Result.Failure(message, _, stdout, stderr, _) =>
        assert(message.toLowerCase.contains("smt-lib error"), clues(s"message=[$message]"))
        assert(stdout.contains("(error"), clues(s"stdout=[$stdout]"))
        assertEquals(stderr, "")

      case Z3Result.Success(stdout, stderr, _) =>
        fail(s"expected failure, got success\nstdout:\n$stdout\nstderr:\n$stderr")
    }
  }
}
