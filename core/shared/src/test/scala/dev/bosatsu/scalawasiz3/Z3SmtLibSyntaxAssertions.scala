package dev.bosatsu.scalawasiz3

private[scalawasiz3] trait Z3SmtLibSyntaxAssertions { self: munit.FunSuite =>

  protected final case class SmtRun(stdout: String, stderr: String, statuses: List[String])

  protected final def assertSucceedsWithoutStatuses(source: String, smt2: String): Unit = {
    val run = runSuccess(source, smt2)
    assertEquals(
      run.statuses,
      Nil,
      clues(source, s"stdout=[${
          run.stdout
        }]", s"stderr=[${run.stderr}]")
    )
  }

  protected final def assertStatusesExactly(
      source: String,
      smt2: String,
      expected: List[String]
  ): Unit = {
    val run = runSuccess(source, smt2)
    assertEquals(
      run.statuses,
      expected,
      clues(source, s"stdout=[${
          run.stdout
        }]", s"stderr=[${run.stderr}]")
    )
  }

  protected final def assertStatusesContainInOrder(
      source: String,
      smt2: String,
      expected: List[String]
  ): Unit = {
    val run = runSuccess(source, smt2)
    assert(
      containsSubsequence(run.statuses, expected),
      clues(
        source,
        s"expected subsequence=${expected.mkString(",")}",
        s"statuses=${run.statuses.mkString(",")}",
        s"stdout=[${run.stdout}]",
        s"stderr=[${run.stderr}]"
      )
    )
  }

  protected final def assertFails(source: String, smt2: String): Unit =
    Z3Solver.default.runSmt2(smt2) match {
      case Z3Result.Failure(_, _, _, _, _) =>
        ()

      case Z3Result.Success(stdout, stderr, _) =>
        fail(
          s"expected failure for [$source], but solver succeeded\nstdout:\n$stdout\nstderr:\n$stderr"
        )
    }

  protected final def assertFailsWithTrap(source: String, smt2: String): Unit =
    Z3Solver.default.runSmt2(smt2) match {
      case Z3Result.Failure(message, _, stdout, stderr, _) =>
        val messageLc = Option(message).getOrElse("").toLowerCase
        assert(
          messageLc.contains("unreachable"),
          clues(
            source,
            s"message=[$message]",
            s"stdout=[$stdout]",
            s"stderr=[$stderr]"
          )
        )
      case Z3Result.Success(stdout, stderr, _) =>
        fail(
          s"expected trap failure for [$source], but solver succeeded\nstdout:\n$stdout\nstderr:\n$stderr"
        )
    }

  protected final def withCheckSat(input: String): String =
    s"""$input
       |(check-sat)
       |""".stripMargin

  private def runSuccess(source: String, smt2: String): SmtRun =
    Z3Solver.default.runSmt2(smt2) match {
      case Z3Result.Success(stdout, stderr, _) =>
        SmtRun(stdout = stdout, stderr = stderr, statuses = parseStatuses(stdout))

      case Z3Result.Failure(message, _, stdout, stderr, _) =>
        fail(
          s"expected successful solver run for [$source], got failure: $message\nstdout:\n$stdout\nstderr:\n$stderr"
        )
    }

  private def parseStatuses(stdout: String): List[String] =
    stdout.linesIterator
      .map(_.trim)
      .collect {
        case "sat"     => "sat"
        case "unsat"   => "unsat"
        case "unknown" => "unknown"
      }
      .toList

  private def containsSubsequence(full: List[String], expected: List[String]): Boolean = {
    @annotation.tailrec
    def loop(remainingFull: List[String], remainingExpected: List[String]): Boolean =
      remainingExpected match {
        case Nil => true
        case expectedHead :: expectedTail =>
          remainingFull.dropWhile(_ != expectedHead) match {
            case Nil         => false
            case _ :: tail   => loop(tail, expectedTail)
          }
      }

    loop(full, expected)
  }
}
