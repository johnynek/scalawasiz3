package dev.bosatsu.scalawasiz3

class Z3RealEvaluationSuite extends munit.FunSuite {

  test("Z3 evaluates assert true as sat") {
    if (requireRealWasm()) {
      val result = runSmt2("(assert true)\n(check-sat)\n")
      assertStatus(result, expected = "sat")
    }
  }

  test("Z3 evaluates assert false as unsat") {
    if (requireRealWasm()) {
      val result = runSmt2("(assert false)\n(check-sat)\n")
      assertStatus(result, expected = "unsat")
    }
  }

  private def runSmt2(input: String): Z3Result =
    Z3Solver.default.runSmt2(input)

  private def assertStatus(result: Z3Result, expected: String): Unit =
    result match {
      case Z3Result.Success(stdout, stderr, _) =>
        val parsed = parseStatus(stdout)
        assertEquals(
          parsed,
          Some(expected),
          clues(s"stdout=[$stdout]", s"stderr=[$stderr]")
        )
      case f: Z3Result.Failure =>
        fail(s"Expected successful Z3 run, got failure: ${f.message}; stdout=[${f.stdout}] stderr=[${f.stderr}]")
    }

  private def parseStatus(stdout: String): Option[String] =
    stdout
      .linesIterator
      .map(_.trim)
      .find(line => line == "sat" || line == "unsat" || line == "unknown")

  private def requireRealWasm(): Boolean = {
    val maybeBytes = Option(getClass.getResourceAsStream(Z3WasmResource.ClasspathResourcePath)).map { in =>
      try in.readAllBytes()
      finally in.close()
    }

    val isReal = maybeBytes.exists(_.length > 8)
    if (!isReal) {
      println(
        "Skipping real Z3 assertion checks: placeholder z3.wasm detected. CI builds the real WASI binary first."
      )
    }
    isReal
  }
}
