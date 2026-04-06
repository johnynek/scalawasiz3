package dev.bosatsu.scalawasiz3

class Z3ExtractedQuantSolveExamplesSuite extends munit.FunSuite with Z3SmtLibSyntaxAssertions {

  private final case class Case(
      id: Int,
      group: String,
      source: String,
      name: String,
      smt2: String,
      nativeExit: Int,
      statuses: List[String]
  )

  // Extracted SMT-LIB quantifier-solving examples from z3/src/test/quant_solve.cpp
  private val cases: List[Case] = List(
    Case(
      id = 32,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_01",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 2 x) y) (>= x z) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 33,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_02",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= x y) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 34,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_03",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 2 x) y) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 35,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_04",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (>= x y) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 36,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_05",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (>= (* 2 x) y) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 37,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_06",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 2 x) y) (>= (* 3 x) z) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 38,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_07",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (>= (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 39,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_08",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (<= (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 40,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_09",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (< (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 41,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_10",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (= (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 42,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_11",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (< (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 43,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_12",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (> (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 44,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_13",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= a x) (<= (* 2 x) b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 45,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_14",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= a x) (<= x b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 46,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_15",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 2 a) x) (<= x b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 47,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_16",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 2 a) x) (<= (* 2 x) b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 48,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_17",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= a x) (<= (* 3 x) b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 49,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_18",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 3 a) x) (<= x b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 50,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_19",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 3 a) x) (<= (* 3 x) b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 51,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_20",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (< a (* 3 x)) (< (* 3 x) b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 52,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_21",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (< (* 3 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 53,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_22",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (= (* 3 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 54,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_23",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (< (* 3 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 55,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_24",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (> (* 3 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 56,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_25",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (<= (* 3 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 57,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_26",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (>= (* 3 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 58,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_27",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (<= (* 2 x) a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 59,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_28",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (or (= (* 2 x) y) (= (+ (* 2 x) 1) y)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 60,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_29",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (= x a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 61,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_30",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (< x a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 62,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_31",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (> x a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 63,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_32",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (> x a) (< x b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 64,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_33",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (> x a) (< x b)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 65,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_34",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (<= x a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 66,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_35",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (>= x a))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 67,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_36",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (* 2 x) y) (= (mod x 2) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 68,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_37",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (= (* 2 x) y))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 69,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_38",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (or (< x 0) (> x 1)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 70,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_39",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (or (< x y) (> x y)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 71,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_40",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (= x y))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 72,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_41",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (<= x y))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 73,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_42",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (>= x y))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 74,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_43",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (+ x y) 0) (<= (+ x z) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 75,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_44",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (+ x y) 0) (<= (+ (* 2 x) z) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 76,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_45",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (+ (* 3 x) y) 0) (<= (+ (* 2 x) z) 0)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 77,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_46",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (>= x y) (>= x z)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 78,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_47",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (< x y))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 79,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_48",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (> x y))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 80,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_49",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (and (<= (- (* 2 y) b) (+ (* 3 x) a)) (<= (- (* 2 x) a) (+ (* 4 y) b))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 81,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_50",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((c Cell)) (= c null)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 82,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_51",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((c Cell)) (= c (cell null c1))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 83,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_52",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((c Cell)) (not (= c null))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 84,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_53",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((c Cell)) (= (cell c c) c1)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 85,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_54",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((c Cell)) (= (cell c (cdr c1)) c1)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 86,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_55",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (= (tuple a P r1) t)))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 87,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_56",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (= a (first t))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 88,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_57",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (= P (second t))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 89,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_58",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (= r2 (third t))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 90,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_59",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (not (= a (first t)))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 91,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_60",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (not (= P (second t)))))\n(check-sat)\n",
      nativeExit = 0,
      statuses = List("sat")
    ),
    Case(
      id = 92,
      group = "quant_solve",
      source = "src/test/quant_solve.cpp",
      name = "case_61",
      smt2 = "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(declare-const a Int)\n(declare-const b Int)\n(declare-const P Bool)\n(declare-const Q Bool)\n(declare-const r1 Real)\n(declare-const r2 Real)\n(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n(declare-const l1 IList)\n(declare-const l2 IList)\n(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n(declare-const c1 Cell)\n(declare-const c2 Cell)\n(declare-const c3 Cell)\n(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n(declare-const t1 Tuple)\n(declare-const t2 Tuple)\n(declare-const t3 Tuple)\n(assert (exists ((t Tuple)) (not (= r2 (third t)))))\n(check-sat)\n",
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
