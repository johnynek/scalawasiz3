package dev.bosatsu.scalawasiz3

class Z3GoldenResponsesSuite extends munit.FunSuite {
  import CompileTimeFileLoader.readUtf8

  private final case class GoldenCase(
      name: String,
      query: String,
      expectedStdout: String,
      expectedStderr: String
  )

  private val cases = List(
    GoldenCase(
      name = "QF_LIA negation case",
      query = readUtf8("core/shared/src/test/golden/qf_lia_negation_case/query.smt2"),
      expectedStdout = readUtf8("core/shared/src/test/golden/qf_lia_negation_case/expected.stdout"),
      expectedStderr = readUtf8("core/shared/src/test/golden/qf_lia_negation_case/expected.stderr")
    ),
    GoldenCase(
      name = "QF_LIA nested subtraction case",
      query = readUtf8("core/shared/src/test/golden/qf_lia_nested_subtraction_case/query.smt2"),
      expectedStdout = readUtf8("core/shared/src/test/golden/qf_lia_nested_subtraction_case/expected.stdout"),
      expectedStderr = readUtf8("core/shared/src/test/golden/qf_lia_nested_subtraction_case/expected.stderr")
    )
  )

  cases.foreach { c =>
    test(s"${c.name} matches native z3 golden response") {
      Z3Solver.default.runSmt2(c.query) match {
        case Z3Result.Success(stdout, stderr, exitCode) =>
          assertEquals(exitCode, 0)
          assertEquals(stdout, c.expectedStdout)
          assertEquals(stderr, c.expectedStderr)

        case Z3Result.Failure(message, exitCode, stdout, stderr, _) =>
          fail(
            s"expected success, got failure: $message (exitCode=${exitCode.getOrElse(-1)})\\nstdout:\\n$stdout\\nstderr:\\n$stderr"
          )
      }
    }
  }
}
