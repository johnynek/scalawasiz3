# WASM No-Exception QF_LIA Regressions

This document records two SMT-LIB reproductions that previously trapped in the WASM build (due to a `tactic_exception` throw inside `pb2bv_tactic`) but return `unsat` on native Z3.

## Example 1

```smt2
(set-logic QF_LIA)
(declare-const y Int)
(declare-const z Int)
(assert (> (+ (- (- 8) 6) z) 2))
(assert (not (< (- y z) y)))
(check-sat)
```

Native `z3` output:

```text
unsat
```

## Example 2

```smt2
(set-logic QF_LIA)
(declare-const u Int)
(declare-const v Int)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= v (+ 8 0)) (< v (- 8))))
(assert (not (<= (- (- y x) x) (- u (- x (- 7))))))
(check-sat)
```

Native `z3` output:

```text
unsat
```

## Regression Coverage

Golden fixtures for both examples are under:

- `core/shared/src/test/golden/qf_lia_negation_case`
- `core/shared/src/test/golden/qf_lia_nested_subtraction_case`

The shared golden suite `Z3GoldenResponsesSuite` runs on both Scala JVM and Scala.js.
It loads fixture contents at compile time using the Scala 3 macro helper `CompileTimeFileLoader.readUtf8` and then asserts exact `stdout`/`stderr` equality.
