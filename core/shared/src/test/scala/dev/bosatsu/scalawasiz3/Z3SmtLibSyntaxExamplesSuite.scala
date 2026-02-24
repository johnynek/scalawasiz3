package dev.bosatsu.scalawasiz3

class Z3SmtLibSyntaxExamplesSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  // Source: z3/examples/c/test_capi.c parser_example2 (adapted to direct SMT-LIB declarations)
  private val ParserExample2 =
    """(declare-const a Int)
      |(declare-const b Int)
      |(assert (> a b))
      |(check-sat)
      |""".stripMargin

  // Source: z3/examples/SMT-LIB2/bounded model checking/bubble_sort.smt2
  private val BubbleSortBmc =
    """(declare-const dim Int)
      |(declare-const A0 (Array Int Int))
      |(declare-const A1 (Array Int Int))
      |(declare-const A2 (Array Int Int))
      |(declare-const A3 (Array Int Int))
      |(declare-const i0 Int)
      |(declare-const i1 Int)
      |(declare-const i2 Int)
      |(declare-const i3 Int)
      |(declare-const j0 Int)
      |(declare-const j1 Int)
      |(declare-const j2 Int)
      |(declare-const j3 Int)
      |(declare-const tmp0 Int)
      |(declare-const tmp1 Int)
      |(declare-const tmp2 Int)
      |(declare-const l0 (List Int))
      |(declare-const l1 (List Int))
      |(declare-const l2 (List Int))
      |(declare-const l3 (List Int))
      |(declare-const l4 (List Int))
      |
      |(define-fun init_indexes ((_i Int) (_j Int)) Bool
      |  (and (= _i 0) (= _j 0)))
      |
      |(define-fun inner_loop
      |  ((_A0 (Array Int Int)) (_A1 (Array Int Int)) (tmp Int) (_i0 Int) (_dim Int)) Bool
      |  (ite
      |    (> (select _A0 _i0) (select _A0 (+ _i0 1)))
      |    (and
      |      (= tmp (select _A0 _i0))
      |      (= _A1 (store _A0 _i0 (select _A0 (+ _i0 1))))
      |      (= _A1 (store _A0 (+ _i0 1) tmp)))
      |    (= _A1 _A0)))
      |
      |(define-fun bsort_step
      |  ((_A0 (Array Int Int)) (_A1 (Array Int Int)) (tmp Int)
      |   (_i0 Int) (_j0 Int) (_i1 Int) (_j1 Int) (_dim Int)) Bool
      |  (ite
      |    (< _j0 (- _dim 1))
      |    (and
      |      (ite
      |        (< _i0 (- _dim 1))
      |        (and (inner_loop _A0 _A1 tmp _i0 _dim) (= _i1 (+ _i0 1)))
      |        (= _j1 (+ _j0 1)))
      |      (= _j1 (+ _j0 1)))
      |    (and (= _j1 (+ _j0 1)) (= _A1 _A0))))
      |
      |(define-fun-rec check ((_l (List Int))) Bool
      |  (ite
      |    (= _l nil)
      |    true
      |    (ite
      |      (not (= (tail _l) nil))
      |      (and (>= (head _l) (head (tail _l))) (check (tail _l)))
      |      true)))
      |
      |(assert (= dim 4))
      |(assert (init_indexes i0 j0))
      |(assert (bsort_step A0 A1 tmp0 i0 j0 i1 j1 dim))
      |(assert (bsort_step A1 A2 tmp1 i1 j1 i2 j2 dim))
      |(assert (bsort_step A2 A3 tmp2 i2 j2 i3 j3 dim))
      |(assert
      |  (and
      |    (= l0 nil)
      |    (= l1 (insert (select A3 0) l0))
      |    (= l2 (insert (select A3 1) l1))
      |    (= l3 (insert (select A3 2) l2))
      |    (= l4 (insert (select A3 3) l3))))
      |
      |(push)
      |(assert (not (check l4)))
      |(check-sat)
      |(pop)
      |
      |(assert (check l4))
      |(check-sat)
      |""".stripMargin

  // Source: z3/examples/SMT-LIB2/bounded model checking/loop_unrolling.smt2
  private val LoopUnrollingBmc =
    """(declare-const x Int)
      |(declare-const A (Array Int Int))
      |(declare-const i_0 Int)
      |(declare-const found_0 Int)
      |(declare-const found_1 Int)
      |(declare-const found_2 Int)
      |(declare-const i_1 Int)
      |(declare-const i_2 Int)
      |
      |(assert (and (= i_0 0) (= found_0 0)))
      |
      |(define-fun body ((f_0 Int) (f Int) (i0 Int) (i1 Int) (_A (Array Int Int)) (_x Int)) Bool
      |  (and (= f (ite (= _x (select _A i0)) 1 f_0)) (= i1 (+ i0 1))))
      |
      |(define-fun post ((_f Int) (_i Int) (_x Int) (_A (Array Int Int))) Bool
      |  (= (= _f 1) (= _x (select _A _i))))
      |
      |(assert (body found_0 found_1 i_0 i_1 A x))
      |(assert (body found_1 found_2 i_1 i_2 A x))
      |
      |(push)
      |(assert (not (or (post found_2 i_0 x A) (post found_2 i_1 x A))))
      |(check-sat)
      |(pop)
      |
      |(assert (or (post found_2 i_0 x A) (post found_2 i_1 x A)))
      |(check-sat)
      |""".stripMargin

  // Source: z3/examples/SMT-LIB2/bounded model checking/loop_unrolling_bitvec.smt2
  private val LoopUnrollingBitVecBmc =
    """(define-sort IntValue () (_ BitVec 32))
      |(declare-const x IntValue)
      |(declare-const A (Array IntValue IntValue))
      |(declare-const i_0 IntValue)
      |(declare-const found_0 IntValue)
      |(declare-const found_1 IntValue)
      |(declare-const found_2 IntValue)
      |(declare-const i_1 IntValue)
      |(declare-const i_2 IntValue)
      |
      |(assert (and (= i_0 #x00000000) (= found_0 #x00000000)))
      |
      |(define-fun body
      |  ((f_0 IntValue) (f IntValue) (i0 IntValue) (i1 IntValue) (_A (Array IntValue IntValue)) (_x IntValue)) Bool
      |  (and
      |    (= f (ite (= _x (select _A i0)) #x00000001 f_0))
      |    (= i1 (bvadd i0 #x00000001))))
      |
      |(define-fun post ((_f IntValue) (_i IntValue) (_x IntValue) (_A (Array IntValue IntValue))) Bool
      |  (= (= _f #x00000001) (= _x (select _A _i))))
      |
      |(assert (body found_0 found_1 i_0 i_1 A x))
      |(assert (body found_1 found_2 i_1 i_2 A x))
      |
      |(push)
      |(assert (not (or (post found_2 i_0 x A) (post found_2 i_1 x A))))
      |(check-sat)
      |(pop)
      |
      |(assert (or (post found_2 i_0 x A) (post found_2 i_1 x A)))
      |(check-sat)
      |""".stripMargin

  test("c parser_example2 query is sat") {
    assertStatusesExactly("examples/c/test_capi.c::parser_example2", ParserExample2, List("sat"))
  }

  test("bubble_sort bounded-model-checking example returns unsat then sat") {
    assertStatusesContainInOrder(
      "examples/SMT-LIB2/bounded model checking/bubble_sort.smt2",
      BubbleSortBmc,
      List("unsat", "sat")
    )
  }

  test("loop_unrolling bounded-model-checking example returns unsat then sat") {
    assertStatusesContainInOrder(
      "examples/SMT-LIB2/bounded model checking/loop_unrolling.smt2",
      LoopUnrollingBmc,
      List("unsat", "sat")
    )
  }

  test("loop_unrolling_bitvec bounded-model-checking example returns unsat then sat") {
    assertStatusesContainInOrder(
      "examples/SMT-LIB2/bounded model checking/loop_unrolling_bitvec.smt2",
      LoopUnrollingBitVecBmc,
      List("unsat", "sat")
    )
  }
}
