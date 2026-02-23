#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERSIONS_FILE="$ROOT_DIR/versions.properties"
PATCH_FILE="$ROOT_DIR/scripts/z3-wasi-patches/0001-wasi-noexcept-probe-failif.patch"

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "error: required command '$1' is missing" >&2
    exit 1
  fi
}

prop() {
  local key="$1"
  local value
  value="$(grep -E "^${key}=" "$VERSIONS_FILE" | head -n1 | cut -d'=' -f2-)"
  if [[ -z "$value" ]]; then
    echo "error: missing ${key} in ${VERSIONS_FILE}" >&2
    exit 1
  fi
  echo "$value"
}

require_cmd bash
require_cmd curl
require_cmd tar
require_cmd cmake
require_cmd ninja
require_cmd patch
require_cmd grep
require_cmd awk

if [[ ! -f "$PATCH_FILE" ]]; then
  echo "error: missing patch file at $PATCH_FILE" >&2
  exit 1
fi

Z3_TAG="${Z3_TAG:-$(prop z3.tag)}"
CACHE_DIR="${CACHE_DIR:-$ROOT_DIR/target/z3-wasi-cache}"
SRC_DIR="${SRC_DIR:-$ROOT_DIR/target/z3-cpp-tests-src}"
BUILD_DIR="${BUILD_DIR:-$ROOT_DIR/target/z3-cpp-tests-build}"
TEST_LOG="${TEST_LOG:-$BUILD_DIR/test-z3-a.log}"
TIME_LOG="${TIME_LOG:-$BUILD_DIR/test-z3-a.time}"

mkdir -p "$CACHE_DIR"
Z3_ARCHIVE="$CACHE_DIR/${Z3_TAG}.tar.gz"
Z3_URL="https://github.com/Z3Prover/z3/archive/refs/tags/${Z3_TAG}.tar.gz"

if [[ ! -f "$Z3_ARCHIVE" ]]; then
  echo "Downloading ${Z3_URL}"
  curl -fL "$Z3_URL" -o "$Z3_ARCHIVE"
fi

rm -rf "$SRC_DIR" "$BUILD_DIR"
mkdir -p "$SRC_DIR" "$BUILD_DIR"
tar -xzf "$Z3_ARCHIVE" -C "$SRC_DIR" --strip-components=1

if ! patch -d "$SRC_DIR" -p1 < "$PATCH_FILE"; then
  echo "error: failed to apply $PATCH_FILE to $SRC_DIR" >&2
  exit 1
fi

CMAKE_FLAGS=(
  -G Ninja
  -S "$SRC_DIR"
  -B "$BUILD_DIR"
  -DCMAKE_BUILD_TYPE=Release
  -DZ3_BUILD_TEST_EXECUTABLES=ON
  -DZ3_BUILD_EXECUTABLE=ON
  -DZ3_BUILD_LIBZ3_SHARED=OFF
  -DZ3_BUILD_PYTHON_BINDINGS=OFF
  -DZ3_BUILD_JAVA_BINDINGS=OFF
  -DZ3_BUILD_DOTNET_BINDINGS=OFF
  -DZ3_BUILD_DOCUMENTATION=OFF
  -DZ3_SINGLE_THREADED=ON
  -DZ3_POLLING_TIMER=ON
)

cmake "${CMAKE_FLAGS[@]}"
cmake --build "$BUILD_DIR" --target test-z3 --parallel

TIME_BIN="/usr/bin/time"
if [[ ! -x "$TIME_BIN" ]]; then
  TIME_BIN="time"
fi

set +e
"$TIME_BIN" -p "$BUILD_DIR/test-z3" /a > "$TEST_LOG" 2> "$TIME_LOG"
TEST_EXIT=$?
set -e

PASS_COUNT="$(grep -c '^PASS$' "$TEST_LOG" || true)"
REAL_SECS="$(awk '/^real /{print $2}' "$TIME_LOG" | tail -n1)"
USER_SECS="$(awk '/^user /{print $2}' "$TIME_LOG" | tail -n1)"
SYS_SECS="$(awk '/^sys /{print $2}' "$TIME_LOG" | tail -n1)"

echo "Z3 C/C++ test summary"
echo "  binary      : $BUILD_DIR/test-z3"
echo "  exit code   : $TEST_EXIT"
echo "  PASS lines  : $PASS_COUNT"
echo "  real seconds: ${REAL_SECS:-n/a}"
echo "  user seconds: ${USER_SECS:-n/a}"
echo "  sys seconds : ${SYS_SECS:-n/a}"
echo "  test log    : $TEST_LOG"
echo "  time log    : $TIME_LOG"

if [[ "$TEST_EXIT" -ne 0 ]]; then
  echo "error: test-z3 exited with non-zero status" >&2
  echo "--- test-z3 tail ---" >&2
  tail -n 80 "$TEST_LOG" >&2 || true
  echo "--- time log ---" >&2
  cat "$TIME_LOG" >&2 || true
  exit "$TEST_EXIT"
fi
