package dev.bosatsu.scalawasiz3

class Z3ExtractedSmt2PrintParseCasesSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  private final case class Case(
      id: Int,
      group: String,
      source: String,
      name: String,
      smt2: String,
      nativeExit: Int,
      statuses: List[String]
  )

  // Extracted SMT-LIB parser/printing examples from z3/src/test/smt2print_parse.cpp
  private val cases: List[Case] = List(
    Case(
      id = 0,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec1",
      smt2 = "(push)\n(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))\n(declare-const x Int)\n(declare-const l (list Int))\n(declare-fun f ((list Int)) Bool)\n(assert (f (cons x l)))\n(check-sat)\n(pop)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 1,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec2",
      smt2 = "(push)\n(declare-const a (Array Int Int))\n(declare-const b (Array (Array Int Int) Bool))\n(assert (select b a))\n(assert (= b ((as const (Array (Array Int Int) Bool)) true)))\n(assert (= b (store b a true)))\n(declare-const b1 (Array Bool Bool))\n(declare-const b2 (Array Bool Bool))\n(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))\n(check-sat)\n(pop)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 2,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec3",
      smt2 = "(push)\n(declare-const a@ (Array Int Int))\n(declare-const b (Array (Array Int Int) Bool))\n(assert (select b a))\n(check-sat)\n(pop)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 3,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec4",
      smt2 = "(push)\n(declare-const a (Array Int Int))\n(declare-const b# (Array (Array Int Int) Bool))\n(assert (select b a))\n(check-sat)\n(pop)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 4,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec1",
      smt2 = "(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))\n(declare-const x Int)\n(declare-const l (list Int))\n(declare-fun f ((list Int)) Bool)\n(assert (f (cons x l)))\n",
      nativeExit = 0,
      statuses = Nil
    ),
    Case(
      id = 5,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec2",
      smt2 = "(declare-const x Int)\n(declare-const a (Array Int Int))\n(declare-const b (Array (Array Int Int) Bool))\n(assert (select b a))\n(assert (= b ((as const (Array (Array Int Int) Bool)) true)))\n(assert (= b (store b a true)))\n(declare-const b1 (Array Bool Bool))\n(declare-const b2 (Array Bool Bool))\n(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))\n",
      nativeExit = 0,
      statuses = Nil
    ),
    Case(
      id = 6,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec3",
      smt2 = "(declare-datatypes () ((list (nil) (cons (car tree) (cdr list))) (tree (leaf) (node (n list)))))\n(declare-const x tree)\n(declare-const l list)\n(declare-fun f (list) Bool)\n(assert (f (cons x l)))\n",
      nativeExit = 0,
      statuses = Nil
    ),
    Case(
      id = 7,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec4",
      smt2 = "(declare-const x Real)\n(declare-const y Int)\n(assert (= x 0.0))\n(assert (= y 6))\n(assert (> (/ x 1.4) (to_real y)))",
      nativeExit = 0,
      statuses = Nil
    ),
    Case(
      id = 8,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec5",
      smt2 = "(declare-const x (_ BitVec 4))\n(declare-const y (_ BitVec 4))\n(assert (bvule x (bvmul y (concat ((_ extract 2 0) x) ((_ extract 3 3) #xf0)))))",
      nativeExit = 0,
      statuses = Nil
    ),
    Case(
      id = 9,
      group = "smt2print_parse",
      source = "src/test/smt2print_parse.cpp",
      name = "spec6",
      smt2 = "(assert (= \"abc\" \"abc\"))",
      nativeExit = 0,
      statuses = Nil
    ),
    Case(
      id = 10,
      group = "smt2print_parse_repeated_eval",
      source = "src/test/smt2print_parse.cpp",
      name = "spec1",
      smt2 = "(push)\n(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))\n(declare-const x Int)\n(declare-const l (list Int))\n(declare-fun f ((list Int)) Bool)\n(assert (f (cons x l)))\n(check-sat)\n(pop)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 11,
      group = "smt2print_parse_repeated_eval",
      source = "src/test/smt2print_parse.cpp",
      name = "spec2",
      smt2 = "(push)\n(declare-const a (Array Int Int))\n(declare-const b (Array (Array Int Int) Bool))\n(assert (select b a))\n(assert (= b ((as const (Array (Array Int Int) Bool)) true)))\n(assert (= b (store b a true)))\n(declare-const b1 (Array Bool Bool))\n(declare-const b2 (Array Bool Bool))\n(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))\n(check-sat)\n(pop)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 12,
      group = "smt2print_parse_repeated_eval",
      source = "src/test/smt2print_parse.cpp",
      name = "spec3",
      smt2 = "(push)\n(declare-const a@ (Array Int Int))\n(declare-const b (Array (Array Int Int) Bool))\n(assert (select b a))\n(check-sat)\n(pop)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 13,
      group = "smt2print_parse_repeated_eval",
      source = "src/test/smt2print_parse.cpp",
      name = "spec4",
      smt2 = "(push)\n(declare-const a (Array Int Int))\n(declare-const b# (Array (Array Int Int) Bool))\n(assert (select b a))\n(check-sat)\n(pop)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 14,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a|",
      smt2 = "(declare-const |a| Bool)\n(assert |a|)\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 15,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a\\|",
      smt2 = "(declare-const |a\\| Bool)\n(assert |a\\|)\n(check-sat)\n",
      nativeExit = 1,
      statuses = Nil
    ),
    Case(
      id = 16,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a\\||",
      smt2 = "(declare-const |a\\|| Bool)\n(assert |a\\||)\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 17,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a\\\\|",
      smt2 = "(declare-const |a\\\\| Bool)\n(assert |a\\\\|)\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 18,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a\\\\||",
      smt2 = "(declare-const |a\\\\|| Bool)\n(assert |a\\\\||)\n(check-sat)\n",
      nativeExit = 1,
      statuses = List("sat")
    ),
    Case(
      id = 19,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a\\a|",
      smt2 = "(declare-const |a\\a| Bool)\n(assert |a\\a|)\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 20,
      group = "smt2print_parse_symbol_escape",
      source = "src/test/smt2print_parse.cpp",
      name = "|a\\a",
      smt2 = "(declare-const |a\\a Bool)\n(assert |a\\a)\n(check-sat)\n",
      nativeExit = 1,
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
