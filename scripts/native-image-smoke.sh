#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <native-image-binary>" >&2
  exit 2
fi

BIN="$1"
if [[ ! -x "$BIN" ]]; then
  echo "native-image binary is missing or not executable: $BIN" >&2
  exit 1
fi

if ! command -v z3 >/dev/null 2>&1; then
  echo "z3 is required for this smoke test" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d)"
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

printf '(declare-const x Int)\n(assert (= x 42))\n(check-sat)\n' | "$BIN" >"$TMP_DIR/sat.out" 2>"$TMP_DIR/sat.err"
if [[ "$(tr -d '\r' <"$TMP_DIR/sat.out" | tr -d '\n')" != "sat" ]]; then
  echo "expected SAT example to print sat" >&2
  cat "$TMP_DIR/sat.out" >&2
  cat "$TMP_DIR/sat.err" >&2
  exit 1
fi

printf '(declare-const x Int)\n(assert (= x 1))\n(assert (= x 2))\n(check-sat)\n' | "$BIN" >"$TMP_DIR/unsat.out" 2>"$TMP_DIR/unsat.err"
if [[ "$(tr -d '\r' <"$TMP_DIR/unsat.out" | tr -d '\n')" != "unsat" ]]; then
  echo "expected UNSAT example to print unsat" >&2
  cat "$TMP_DIR/unsat.out" >&2
  cat "$TMP_DIR/unsat.err" >&2
  exit 1
fi

BAD_INPUT=$'(this is not valid smt2)\n'
set +e
printf '%s' "$BAD_INPUT" | "$BIN" >"$TMP_DIR/wrapper-bad.out" 2>"$TMP_DIR/wrapper-bad.err"
WRAPPER_EXIT=$?
printf '%s' "$BAD_INPUT" | z3 -smt2 -in >"$TMP_DIR/z3-bad.out" 2>"$TMP_DIR/z3-bad.err"
Z3_EXIT=$?
set -e

if [[ "$WRAPPER_EXIT" -ne "$Z3_EXIT" ]]; then
  echo "wrapper exit code ($WRAPPER_EXIT) does not match z3 exit code ($Z3_EXIT)" >&2
  exit 1
fi

echo "native-image smoke checks passed"
