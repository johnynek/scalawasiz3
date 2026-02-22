package dev.bosatsu.scalawasiz3

class Z3SatDemoSuite extends munit.FunSuite {

  private val demoCases: List[SatDemoCase] = List(
    SatDemoCase(
      name = "propositional tautology",
      expected = "sat",
      smt2 =
        """(declare-const p Bool)
          |(assert (or p (not p)))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "propositional contradiction",
      expected = "unsat",
      smt2 =
        """(declare-const p Bool)
          |(assert p)
          |(assert (not p))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "implication chain contradiction",
      expected = "unsat",
      smt2 =
        """(declare-const a Bool)
          |(declare-const b Bool)
          |(declare-const c Bool)
          |(assert (=> a b))
          |(assert (=> b c))
          |(assert a)
          |(assert (not c))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "exactly one of three booleans",
      expected = "sat",
      smt2 =
        """(declare-const a Bool)
          |(declare-const b Bool)
          |(declare-const c Bool)
          |(assert (or a b c))
          |(assert (not (and a b)))
          |(assert (not (and a c)))
          |(assert (not (and b c)))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "small 2-SAT instance",
      expected = "sat",
      smt2 =
        """(declare-const x Bool)
          |(declare-const y Bool)
          |(declare-const z Bool)
          |(declare-const w Bool)
          |(assert (or x y))
          |(assert (or (not x) z))
          |(assert (or (not y) z))
          |(assert (or (not z) w))
          |(assert (or (not w) x))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "inconsistent linear arithmetic",
      expected = "unsat",
      smt2 =
        """(declare-const x Int)
          |(assert (= (+ x 1) x))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "non-linear real arithmetic",
      expected = "sat",
      smt2 =
        """(set-logic QF_NRA)
          |(declare-const r Real)
          |(assert (= (* r r) 2))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "array store/select consistency",
      expected = "sat",
      smt2 =
        """(declare-const arr (Array Int Int))
          |(assert (= (select (store arr 3 99) 3) 99))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "quantified strict self-ordering",
      expected = "unsat",
      smt2 =
        """(set-logic AUFLIA)
          |(assert (forall ((x Int)) (> x x)))
          |(check-sat)
          |""".stripMargin
    ),
    SatDemoCase(
      name = "pigeonhole principle with 3 pigeons and 2 holes",
      expected = "unsat",
      smt2 =
        """(declare-const p11 Bool)
          |(declare-const p12 Bool)
          |(declare-const p21 Bool)
          |(declare-const p22 Bool)
          |(declare-const p31 Bool)
          |(declare-const p32 Bool)
          |
          |(assert (or p11 p12))
          |(assert (or p21 p22))
          |(assert (or p31 p32))
          |
          |(assert (not (and p11 p12)))
          |(assert (not (and p21 p22)))
          |(assert (not (and p31 p32)))
          |
          |(assert (not (and p11 p21)))
          |(assert (not (and p11 p31)))
          |(assert (not (and p21 p31)))
          |
          |(assert (not (and p12 p22)))
          |(assert (not (and p12 p32)))
          |(assert (not (and p22 p32)))
          |
          |(check-sat)
          |""".stripMargin
    )
  )

  demoCases.zipWithIndex.foreach { case (demoCase, idx) =>
    test(f"demo sat check ${idx + 1}%02d: ${demoCase.name}") {
      val result = Z3Solver.default.runSmt2(demoCase.smt2)
      assertStatus(result, demoCase.expected)
    }
  }

  private def assertStatus(result: Z3Result, expected: String): Unit =
    result match {
      case Z3Result.Success(stdout, stderr, _) =>
        val parsed = parseStatus(stdout)
        assertEquals(
          parsed,
          Some(expected),
          clues(s"stdout=[$stdout]", s"stderr=[$stderr]")
        )
      case f: Z3Result.Failure =>
        fail(s"Expected successful Z3 run, got failure: ${f.message}; stdout=[${f.stdout}] stderr=[${f.stderr}]")
    }

  private def parseStatus(stdout: String): Option[String] =
    stdout
      .linesIterator
      .map(_.trim)
      .find(line => line == "sat" || line == "unsat" || line == "unknown")

  private final case class SatDemoCase(name: String, smt2: String, expected: String)
}
