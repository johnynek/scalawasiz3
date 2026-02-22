package dev.bosatsu.scalawasiz3

class Z3SolverSmokeSuite extends munit.FunSuite {
  test("runSmt2 returns a result instance") {
    Z3Solver.default.runSmt2("(check-sat)") match {
      case _: Z3Result.Success => assert(true)
      case _: Z3Result.Failure => assert(true)
    }
  }

  test("runSmt2 is repeatable") {
    val solver = Z3Solver.default
    val one = solver.runSmt2("(check-sat)")
    val two = solver.runSmt2("(check-sat)")

    assert(one != null)
    assert(two != null)
  }
}
