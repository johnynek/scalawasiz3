package dev.bosatsu.scalawasiz3

class Z3Issue23Suite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  test("issue #23 unknown constant reports non-trap parse failure") {
    assertFailsWithoutTrap(
      "issue23::unknown-constant",
      """(assert (> y 0))
        |(check-sat)
        |""".stripMargin,
      expectedFragments = List("unknown constant", "y")
    )
  }

  test("issue #23 undeclared function reports non-trap type failure") {
    assertFailsWithoutTrap(
      "issue23::undeclared-function",
      """(set-logic QF_LIA)
        |(assert (> (f 1) 0))
        |(check-sat)
        |""".stripMargin,
      expectedFragments = List("unknown", "f")
    )
  }

  test("issue #23 undeclared sort reports non-trap sort failure") {
    assertFailsWithoutTrap(
      "issue23::undeclared-sort",
      """(declare-const x Foo)
        |(check-sat)
        |""".stripMargin,
      expectedFragments = List("unknown sort", "foo")
    )
  }

  test("issue #23 malformed syntax reports non-trap parse failure") {
    Z3Solver.default.runSmt2(
      """(set-logic QF_LIA)
        |(assert true
        |(check-sat)
        |""".stripMargin
    ) match {
      case Z3Result.Failure(message, _, stdout, stderr, _) =>
        val combined = List(message, stdout, stderr).mkString("\n").toLowerCase
        assert(
          !combined.contains("unreachable"),
          clues(
            "issue23::malformed",
            s"message=[$message]",
            s"stdout=[$stdout]",
            s"stderr=[$stderr]"
          )
        )
        assert(
          combined.contains("unexpected end of file") || combined.contains("invalid assert command"),
          clues(
            "issue23::malformed",
            s"message=[$message]",
            s"stdout=[$stdout]",
            s"stderr=[$stderr]"
          )
        )

      case Z3Result.Success(stdout, stderr, _) =>
        fail(
          s"expected non-trap failure for [issue23::malformed], but solver succeeded\nstdout:\n$stdout\nstderr:\n$stderr"
        )
    }
  }

  test("issue #23 recursion script undeclared symbol reports non-trap failure") {
    assertFailsWithoutTrap(
      "issue23::recursion-script",
      """(set-logic QF_LIA)
        |(declare-const idx_0 Int)
        |(declare-const t_1 Int)
        |(assert (and (not (< idx_0 0)) (not (< idx_0 t_1)) (and (not (< idx_0 0)) (not (< idx_0 s_1))) (> t_1 0)))
        |(assert (not (>= (- idx_0 1) 0)))
        |(check-sat)
        |""".stripMargin,
      expectedFragments = List("unknown", "s_1")
    )
  }
}
