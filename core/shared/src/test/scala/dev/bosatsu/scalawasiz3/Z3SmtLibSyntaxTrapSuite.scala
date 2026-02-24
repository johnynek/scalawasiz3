package dev.bosatsu.scalawasiz3

class Z3SmtLibSyntaxTrapSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  // Source: z3/src/test/smt2print_parse.cpp spec1
  private val SpecDatatypeDeclarations =
    """(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))
      |(declare-const x Int)
      |(declare-const l (list Int))
      |(declare-fun f ((list Int)) Bool)
      |(assert (f (cons x l)))
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp spec2
  private val SpecArrayDeclarations =
    """(declare-const x Int)
      |(declare-const a (Array Int Int))
      |(declare-const b (Array (Array Int Int) Bool))
      |(assert (select b a))
      |(assert (= b ((as const (Array (Array Int Int) Bool)) true)))
      |(assert (= b (store b a true)))
      |(declare-const b1 (Array Bool Bool))
      |(declare-const b2 (Array Bool Bool))
      |(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp spec3
  private val SpecMutuallyRecursiveDatatypes =
    """(declare-datatypes () ((list (nil) (cons (car tree) (cdr list))) (tree (leaf) (node (n list)))))
      |(declare-const x tree)
      |(declare-const l list)
      |(declare-fun f (list) Bool)
      |(assert (f (cons x l)))
      |""".stripMargin

  // Source: z3/src/test/smt2print_parse.cpp spec5
  private val SpecBitVectors =
    """(declare-const x (_ BitVec 4))
      |(declare-const y (_ BitVec 4))
      |(assert (bvule x (bvmul y (concat ((_ extract 2 0) x) ((_ extract 3 3) #xf0)))))
      |(check-sat)
      |""".stripMargin

  // Source: z3/examples/c/test_capi.c parser_example3 (adapted from symbol-table API wiring)
  private val ParserExample3 =
    """(declare-fun g (Int Int) Int)
      |(assert (forall ((x Int) (y Int)) (= (g x y) (g y x))))
      |(assert (forall ((x Int) (y Int)) (=> (= x y) (= (g x 0) (g 0 y)))))
      |(check-sat)
      |""".stripMargin

  // Source: z3/examples/c/test_capi.c smt2parser_example
  private val Smt2ParserExample =
    """(declare-fun a () (_ BitVec 8))
      |(assert (bvuge a #x10))
      |(assert (bvule a #xf0))
      |(check-sat)
      |""".stripMargin

  test("smt2print_parse spec1 currently traps on wasi") {
    assertFailsWithTrap("src/test/smt2print_parse.cpp::spec1", SpecDatatypeDeclarations)
  }

  test("smt2print_parse spec2 currently traps on wasi") {
    assertFailsWithTrap("src/test/smt2print_parse.cpp::spec2", SpecArrayDeclarations)
  }

  test("smt2print_parse spec3 currently traps on wasi") {
    assertFailsWithTrap("src/test/smt2print_parse.cpp::spec3", SpecMutuallyRecursiveDatatypes)
  }

  test("smt2print_parse spec5 currently traps on wasi") {
    assertFailsWithTrap("src/test/smt2print_parse.cpp::spec5", SpecBitVectors)
  }

  test("c parser_example3 Int logic returns unknown instead of trapping") {
    assertStatusesExactly("examples/c/test_capi.c::parser_example3", ParserExample3, List("unknown"))
  }

  test("c smt2parser_example currently traps on wasi") {
    assertFailsWithTrap("examples/c/test_capi.c::smt2parser_example", Smt2ParserExample)
  }
}
