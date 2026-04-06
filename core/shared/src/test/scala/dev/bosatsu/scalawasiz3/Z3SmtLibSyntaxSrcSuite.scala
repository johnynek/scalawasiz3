package dev.bosatsu.scalawasiz3

class Z3SmtLibSyntaxSrcSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  // Source: z3/src/test/smt2print_parse.cpp spec4
  private val SpecArithmetic =
    """(declare-const x Real)
      |(declare-const y Int)
      |(assert (= x 0.0))
      |(assert (= y 6))
      |(assert (> (/ x 1.4) (to_real y)))
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp spec6
  private val SpecStrings =
    """(assert (= "abc" "abc"))
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp test_repeated_eval/spec1
  private val RepeatedEvalDatatypeQuery =
    """(push)
      |(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))
      |(declare-const x Int)
      |(declare-const l (list Int))
      |(declare-fun f ((list Int)) Bool)
      |(assert (f (cons x l)))
      |(check-sat)
      |(pop)
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp test_repeated_eval/spec2
  private val RepeatedEvalArrayQuery =
    """(push)
      |(declare-const a (Array Int Int))
      |(declare-const b (Array (Array Int Int) Bool))
      |(assert (select b a))
      |(assert (= b ((as const (Array (Array Int Int) Bool)) true)))
      |(assert (= b (store b a true)))
      |(declare-const b1 (Array Bool Bool))
      |(declare-const b2 (Array Bool Bool))
      |(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))
      |(check-sat)
      |(pop)
      |""".stripMargin

  private def symbolAssertion(symbol: String): String =
    s"""(declare-const $symbol Bool)
       |(assert $symbol)
       |(check-sat)
       |""".stripMargin

  test("smt2print_parse spec4 arithmetic query is unsat") {
    assertStatusesExactly("src/test/smt2print_parse.cpp::spec4", withCheckSat(SpecArithmetic), List("unsat"))
  }

  test("smt2print_parse spec6 string equality is sat") {
    assertStatusesExactly("src/test/smt2print_parse.cpp::spec6", withCheckSat(SpecStrings), List("sat"))
  }

  test("smt2print_parse repeated_eval spec1 remains sat") {
    assertStatusesExactly(
      "src/test/smt2print_parse.cpp::test_repeated_eval/spec1",
      RepeatedEvalDatatypeQuery,
      List("sat")
    )
  }

  test("smt2print_parse repeated_eval spec2 remains sat") {
    assertStatusesExactly(
      "src/test/smt2print_parse.cpp::test_repeated_eval/spec2",
      RepeatedEvalArrayQuery,
      List("sat")
    )
  }

  test("smt2print_parse symbol escape allows |a|") {
    assertStatusesExactly(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a|)",
      symbolAssertion("|a|"),
      List("sat")
    )
  }

  test("smt2print_parse symbol escape allows |a\\||") {
    assertStatusesExactly(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a\\||)",
      symbolAssertion("|a\\||"),
      List("sat")
    )
  }

  test("smt2print_parse symbol escape allows |a\\\\|") {
    assertStatusesExactly(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a\\\\|)",
      symbolAssertion("|a\\\\|"),
      List("sat")
    )
  }

  test("smt2print_parse symbol escape allows |a\\a|") {
    assertStatusesExactly(
      "src/test/smt2print_parse.cpp::test_symbol_escape(|a\\a|)",
      symbolAssertion("|a\\a|"),
      List("sat")
    )
  }
}
