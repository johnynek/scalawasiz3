#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <linked-main-js>" >&2
  exit 2
fi

JS_MAIN="$1"
if [[ ! -f "$JS_MAIN" ]]; then
  echo "node main script is missing: $JS_MAIN" >&2
  exit 1
fi

if ! command -v node >/dev/null 2>&1; then
  echo "node is required for this smoke test" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d)"
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

SAT_INPUT=$'(set-option :produce-models true)\n(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n(assert (= (+ x y) 42))\n(assert (> x 10))\n(assert (< y 20))\n(assert (= (- x y) 4))\n(check-sat)\n(get-value (x y))\n'
set +e
printf '%s' "$SAT_INPUT" | node "$JS_MAIN" >"$TMP_DIR/sat.out" 2>"$TMP_DIR/sat.err"
SAT_EXIT=$?
set -e
if [[ "$SAT_EXIT" -ne 0 ]]; then
  echo "SAT example exited non-zero ($SAT_EXIT)" >&2
  cat "$TMP_DIR/sat.out" >&2
  cat "$TMP_DIR/sat.err" >&2
  exit 1
fi
if ! grep -qx 'sat' "$TMP_DIR/sat.out"; then
  echo "expected SAT output to contain a sat status line" >&2
  cat "$TMP_DIR/sat.out" >&2
  cat "$TMP_DIR/sat.err" >&2
  exit 1
fi
if ! grep -q '19' "$TMP_DIR/sat.out" || ! grep -q '23' "$TMP_DIR/sat.out"; then
  echo "expected SAT model output to mention x=23 and y=19" >&2
  cat "$TMP_DIR/sat.out" >&2
  cat "$TMP_DIR/sat.err" >&2
  exit 1
fi

UNSAT_INPUT=$'(set-logic QF_UF)\n(declare-sort A 0)\n(declare-fun f (A) A)\n(declare-const a A)\n(assert (not (= (f a) a)))\n(assert (= (f a) a))\n(check-sat)\n'
set +e
printf '%s' "$UNSAT_INPUT" | node "$JS_MAIN" >"$TMP_DIR/unsat.out" 2>"$TMP_DIR/unsat.err"
UNSAT_EXIT=$?
set -e
if [[ "$UNSAT_EXIT" -ne 0 ]]; then
  echo "UNSAT example exited non-zero ($UNSAT_EXIT)" >&2
  cat "$TMP_DIR/unsat.out" >&2
  cat "$TMP_DIR/unsat.err" >&2
  exit 1
fi
if ! grep -qx 'unsat' "$TMP_DIR/unsat.out"; then
  echo "expected UNSAT output to contain an unsat status line" >&2
  cat "$TMP_DIR/unsat.out" >&2
  cat "$TMP_DIR/unsat.err" >&2
  exit 1
fi

INVALID_INPUT=$'(this is not valid smt2)\n'
set +e
printf '%s' "$INVALID_INPUT" | node "$JS_MAIN" >"$TMP_DIR/invalid.out" 2>"$TMP_DIR/invalid.err"
INVALID_EXIT=$?
set -e
if [[ "$INVALID_EXIT" -eq 0 ]]; then
  echo "invalid SMT-LIB should fail with non-zero exit code" >&2
  cat "$TMP_DIR/invalid.out" >&2
  cat "$TMP_DIR/invalid.err" >&2
  exit 1
fi
if [[ ! -s "$TMP_DIR/invalid.err" ]]; then
  echo "expected invalid SMT-LIB to produce stderr output" >&2
  cat "$TMP_DIR/invalid.out" >&2
  cat "$TMP_DIR/invalid.err" >&2
  exit 1
fi

echo "node main smoke checks passed"
