#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERSIONS_FILE="$ROOT_DIR/versions.properties"

maybe_add_homebrew_bin() {
  local formula="$1"
  local prefix

  if ! command -v brew >/dev/null 2>&1; then
    return 0
  fi

  prefix="$(brew --prefix "$formula" 2>/dev/null || true)"
  if [[ -n "$prefix" && -d "$prefix/bin" ]]; then
    PATH="$prefix/bin:$PATH"
  fi
}

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

find_shared_library() {
  local root="$1"
  local candidate

  while IFS= read -r candidate; do
    echo "$candidate"
    return 0
  done < <(
    find "$root" \( -type f -o -type l \) \
      \( -name "libz3*.dylib" -o -name "libz3.so" -o -name "libz3.so.*" \) \
      | sort
  )

  echo "error: unable to find libz3 under $root" >&2
  return 1
}

maybe_add_homebrew_bin cmake
maybe_add_homebrew_bin ninja

require_cmd bash
require_cmd curl
require_cmd tar
require_cmd cmake
require_cmd ninja
require_cmd python3

Z3_TAG="${Z3_TAG:-$(prop z3.tag)}"

CACHE_DIR="${CACHE_DIR:-$ROOT_DIR/target/z3-native-cache}"
BUILD_DIR="${BUILD_DIR:-$ROOT_DIR/target/z3-native-build}"
INSTALL_DIR="${INSTALL_DIR:-$ROOT_DIR/target/z3-native-install}"

mkdir -p "$CACHE_DIR" "$BUILD_DIR"

Z3_ARCHIVE="$CACHE_DIR/${Z3_TAG}.tar.gz"
Z3_URL="https://github.com/Z3Prover/z3/archive/refs/tags/${Z3_TAG}.tar.gz"

if [[ ! -f "$Z3_ARCHIVE" ]]; then
  echo "Downloading ${Z3_URL}"
  curl -fL "$Z3_URL" -o "$Z3_ARCHIVE"
fi

Z3_SRC_DIR="$BUILD_DIR/z3-src"
Z3_BUILD_DIR="$BUILD_DIR/z3-build"

rm -rf "$Z3_SRC_DIR" "$Z3_BUILD_DIR" "$INSTALL_DIR"
mkdir -p "$Z3_SRC_DIR" "$Z3_BUILD_DIR" "$INSTALL_DIR"

tar -xzf "$Z3_ARCHIVE" -C "$Z3_SRC_DIR" --strip-components=1

CMAKE_FLAGS=(
  -G Ninja
  -S "$Z3_SRC_DIR"
  -B "$Z3_BUILD_DIR"
  -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR"
  -DZ3_BUILD_LIBZ3_SHARED=ON
  -DZ3_BUILD_EXECUTABLE=OFF
  -DZ3_BUILD_TEST_EXECUTABLES=OFF
  -DZ3_BUILD_PYTHON_BINDINGS=OFF
  -DZ3_BUILD_JAVA_BINDINGS=OFF
  -DZ3_BUILD_DOTNET_BINDINGS=OFF
  -DZ3_BUILD_DOCUMENTATION=OFF
  -DZ3_USE_LIB_GMP=OFF
)

cmake "${CMAKE_FLAGS[@]}"
cmake --build "$Z3_BUILD_DIR" --parallel
cmake --install "$Z3_BUILD_DIR"

LIBZ3_PATH="$(find_shared_library "$INSTALL_DIR")"
LIBZ3_DIR="$(dirname "$LIBZ3_PATH")"

echo "Built Z3 native library"
echo "  libz3  : $LIBZ3_PATH"
echo "  libdir : $LIBZ3_DIR"
echo "  export SCALAWASIZ3_Z3_NATIVE_LIB_DIR=$LIBZ3_DIR"
