package dev.bosatsu.scalawasiz3

import java.nio.charset.StandardCharsets

class JvmGoldenResponsesSuite extends munit.FunSuite {
  private final case class GoldenCase(name: String, root: String)

  private val cases = List(
    GoldenCase(
      name = "QF_LIA negation case",
      root = "/dev/bosatsu/scalawasiz3/golden/qf_lia_negation_case"
    ),
    GoldenCase(
      name = "QF_LIA nested subtraction case",
      root = "/dev/bosatsu/scalawasiz3/golden/qf_lia_nested_subtraction_case"
    )
  )

  cases.foreach { c =>
    test(s"${c.name} matches native z3 golden response") {
      val smt2 = readResource(s"${c.root}/query.smt2")
      val expectedStdout = readResource(s"${c.root}/expected.stdout")
      val expectedStderr = readResource(s"${c.root}/expected.stderr")

      Z3Solver.default.runSmt2(smt2) match {
        case Z3Result.Success(stdout, stderr, exitCode) =>
          assertEquals(exitCode, 0)
          assertEquals(stdout, expectedStdout)
          assertEquals(stderr, expectedStderr)

        case Z3Result.Failure(message, exitCode, stdout, stderr, _) =>
          fail(
            s"expected success, got failure: $message (exitCode=${exitCode.getOrElse(-1)})\nstdout:\n$stdout\nstderr:\n$stderr"
          )
      }
    }
  }

  private def readResource(path: String): String = {
    val stream = Option(getClass.getResourceAsStream(path)).getOrElse {
      fail(s"missing test resource: $path")
    }
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }
}
