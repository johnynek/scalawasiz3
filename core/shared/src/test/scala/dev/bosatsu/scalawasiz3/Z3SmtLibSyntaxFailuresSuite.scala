package dev.bosatsu.scalawasiz3

class Z3SmtLibSyntaxFailuresSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  // Source: z3/src/test/smt2print_parse.cpp test_repeated_eval/spec3
  private val RepeatedEvalFailure1 =
    """(push)
      |(declare-const a@ (Array Int Int))
      |(declare-const b (Array (Array Int Int) Bool))
      |(assert (select b a))
      |(check-sat)
      |(pop)
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp test_repeated_eval/spec4
  private val RepeatedEvalFailure2 =
    """(push)
      |(declare-const a (Array Int Int))
      |(declare-const b# (Array (Array Int Int) Bool))
      |(assert (select b a))
      |(check-sat)
      |(pop)
      |""".stripMargin

  // Source: z3/examples/c/test_capi.c parser_example5
  private val ParserExample5Failure =
    """(declare-const x Int) declare-const y Int) (assert (and (> x y) (> x 0)))
      |""".stripMargin

  private def symbolAssertion(symbol: String): String =
    s"""(declare-const $symbol Bool)
       |(assert $symbol)
       |(check-sat)
       |""".stripMargin

  test("smt2print_parse repeated_eval spec3 is rejected") {
    assertFails("src/test/smt2print_parse.cpp::test_repeated_eval/spec3", RepeatedEvalFailure1)
  }

  test("smt2print_parse repeated_eval spec4 is rejected") {
    assertFails("src/test/smt2print_parse.cpp::test_repeated_eval/spec4", RepeatedEvalFailure2)
  }

  test("smt2print_parse symbol escape rejects |a\\|") {
    assertFails(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a\\|)",
      symbolAssertion("|a\\|")
    )
  }

  test("smt2print_parse symbol escape rejects |a\\\\||") {
    assertFails(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a\\\\||)",
      symbolAssertion("|a\\\\||")
    )
  }

  test("smt2print_parse symbol escape rejects |a\\a") {
    assertFails(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a\\a)",
      symbolAssertion("|a\\a")
    )
  }

  test("c parser_example5 malformed declaration is rejected") {
    assertFails("examples/c/test_capi.c::parser_example5", ParserExample5Failure)
  }
}
