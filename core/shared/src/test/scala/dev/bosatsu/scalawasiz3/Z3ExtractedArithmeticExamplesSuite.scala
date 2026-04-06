package dev.bosatsu.scalawasiz3

class Z3ExtractedArithmeticExamplesSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  private final case class Case(
      id: Int,
      group: String,
      source: String,
      name: String,
      smt2: String,
      nativeExit: Int,
      statuses: List[String]
  )

  // Extracted SMT-LIB arithmetic and rewriting examples from z3/src/test/*
  private val cases: List[Case] = List(
    Case(
      id = 21,
      group = "arith_rewriter",
      source = "src/test/arith_rewriter.cpp",
      name = "example1",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const a Real)\n(declare-const b Real)\n(assert (<= (+ (* 1.3 x y) (* 2.3 y y) (* (- 1.1 x x))) 2.2))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 22,
      group = "arith_rewriter",
      source = "src/test/arith_rewriter.cpp",
      name = "example2",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const a Real)\n(declare-const b Real)\n(assert (= (+ 4 3 (- (* 3 x x) (* 5 y)) y) 0))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 23,
      group = "polynorm",
      source = "src/test/polynorm.cpp",
      name = "example1",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(assert (= (+ (- (* x x) (* 2 y)) y) 0))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 24,
      group = "polynorm",
      source = "src/test/polynorm.cpp",
      name = "example2",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(assert (= (+ 4 3 (- (* x x) (* 2 y)) y) 0))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 25,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example1",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and (<= x 3.0) (<= (* 3.0 x) y) (<= z y)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 26,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example2",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and (<= z x) (<= x 3.0) (<= (* 3.0 x) y) (<= z y)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 27,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example3",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and (<= z x) (<= x 3.0) (< (* 3.0 x) y) (<= z y)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 28,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example4",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and (<= z x) (<= x 3.0) (not (>= (* 3.0 x) y)) (<= z y)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 29,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example5",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and (<= y x) (<= z x) (<= x u) (<= x v) (<= x t)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 30,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example7",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and (<= x y) (<= x z) (<= u x) (< v x)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 31,
      group = "qe_arith",
      source = "src/test/qe_arith.cpp",
      name = "example8",
      smt2 = "(declare-const x Real)\n(declare-const y Real)\n(declare-const z Real)\n(declare-const u Real)\n(declare-const v Real)\n(declare-const t Real)\n(declare-const a Real)\n(declare-const b Real)\n(declare-const i Int)\n(declare-const j Int)\n(declare-const k Int)\n(declare-const l Int)\n(declare-const m Int)\n(assert (and  (<= (* 2 i) k) (<= j (* 3 i))))\n(check-sat)\n",
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
