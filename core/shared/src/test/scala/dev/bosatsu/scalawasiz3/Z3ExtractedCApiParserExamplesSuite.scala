package dev.bosatsu.scalawasiz3

class Z3ExtractedCApiParserExamplesSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  private final case class Case(
      id: Int,
      group: String,
      source: String,
      name: String,
      smt2: String,
      nativeExit: Int,
      statuses: List[String]
  )

  // Extracted SMT-LIB parser snippets from z3/examples/c/test_capi.c
  private val cases: List[Case] = List(
    Case(
      id = 93,
      group = "c_api_parser",
      source = "examples/c/test_capi.c",
      name = "assert_comm_axiom",
      smt2 = "(assert (forall ((x T) (y T)) (= (f x y) (f y x))))\n(check-sat)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 94,
      group = "c_api_parser",
      source = "examples/c/test_capi.c",
      name = "parser_example2",
      smt2 = "(assert (> a b))\n(check-sat)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 95,
      group = "c_api_parser",
      source = "examples/c/test_capi.c",
      name = "parser_example3",
      smt2 = "(assert (forall ((x Int) (y Int)) (=> (= x y) (= (g x 0) (g 0 y)))))\n(check-sat)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 96,
      group = "c_api_parser",
      source = "examples/c/test_capi.c",
      name = "parser_example5_invalid",
      smt2 = "(declare-const x Int) declare-const y Int) (assert (and (> x y) (> x 0)))",
      nativeExit = 1,
      statuses = Nil
    ),
    Case(
      id = 97,
      group = "c_api_parser",
      source = "examples/c/test_capi.c",
      name = "smt2parser_example",
      smt2 = "(declare-fun a () (_ BitVec 8)) (assert (bvuge a #x10)) (assert (bvule a #xf0))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    )
  )

  private def sourceRef(c: Case): String =
    s"${c.source}::${c.name} [${c.group}/${c.id}]"

  private def runExtractedCase(c: Case): Unit =
    if (c.nativeExit == 0) {
      if (c.statuses.isEmpty) assertSucceedsWithoutStatuses(sourceRef(c), c.smt2)
      else assertStatusesExactly(sourceRef(c), c.smt2, c.statuses)
    } else {
      assertFails(sourceRef(c), c.smt2)
    }

  cases.foreach { c =>
    test(sourceRef(c)) {
      runExtractedCase(c)
    }
  }
}
