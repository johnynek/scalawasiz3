#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERSIONS_FILE="$ROOT_DIR/versions.properties"

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

host_os() {
  case "$(uname -s)" in
    Linux) echo "linux" ;;
    Darwin) echo "macos" ;;
    *)
      echo "error: unsupported host OS $(uname -s)" >&2
      exit 1
      ;;
  esac
}

host_arch() {
  case "$(uname -m)" in
    x86_64|amd64) echo "x86_64" ;;
    arm64|aarch64) echo "arm64" ;;
    *)
      echo "error: unsupported host architecture $(uname -m)" >&2
      exit 1
      ;;
  esac
}

sha256_file() {
  local file="$1"
  local out="$2"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$file" > "$out"
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$file" > "$out"
  else
    echo "error: expected sha256sum or shasum" >&2
    exit 1
  fi
}

find_wasm_binary() {
  local build_dir="$1"
  local candidate
  while IFS= read -r candidate; do
    if file "$candidate" | grep -q "WebAssembly"; then
      echo "$candidate"
      return 0
    fi
  done < <(find "$build_dir" -type f \( -name "z3" -o -name "z3.wasm" \) | sort)

  echo "error: unable to find built z3 wasm executable under $build_dir" >&2
  return 1
}

require_cmd bash
require_cmd curl
require_cmd tar
require_cmd cmake
require_cmd ninja
require_cmd python3
require_cmd file

Z3_TAG="${Z3_TAG:-$(prop z3.tag)}"
WASI_SDK_VERSION="${WASI_SDK_VERSION:-$(prop wasi.sdk.version)}"
WASI_SDK_RELEASE_TAG="${WASI_SDK_RELEASE_TAG:-wasi-sdk-${WASI_SDK_VERSION%%.*}}"

WASI_OS="$(host_os)"
WASI_ARCH="$(host_arch)"

CACHE_DIR="${CACHE_DIR:-$ROOT_DIR/target/z3-wasi-cache}"
BUILD_DIR="${BUILD_DIR:-$ROOT_DIR/target/z3-wasi-build}"
OUT_WASM="${OUT_WASM:-$ROOT_DIR/core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm}"
OUT_SHA="${OUT_SHA:-$ROOT_DIR/core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm.sha256}"
OUT_IMPORTS="${OUT_IMPORTS:-$ROOT_DIR/core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.imports.json}"

mkdir -p "$CACHE_DIR" "$BUILD_DIR"

Z3_ARCHIVE="$CACHE_DIR/${Z3_TAG}.tar.gz"
WASI_ARCHIVE="$CACHE_DIR/wasi-sdk-${WASI_SDK_VERSION}-${WASI_ARCH}-${WASI_OS}.tar.gz"

Z3_URL="https://github.com/Z3Prover/z3/archive/refs/tags/${Z3_TAG}.tar.gz"
WASI_URL="https://github.com/WebAssembly/wasi-sdk/releases/download/${WASI_SDK_RELEASE_TAG}/wasi-sdk-${WASI_SDK_VERSION}-${WASI_ARCH}-${WASI_OS}.tar.gz"

if [[ ! -f "$Z3_ARCHIVE" ]]; then
  echo "Downloading ${Z3_URL}"
  curl -fL "$Z3_URL" -o "$Z3_ARCHIVE"
fi

if [[ ! -f "$WASI_ARCHIVE" ]]; then
  echo "Downloading ${WASI_URL}"
  curl -fL "$WASI_URL" -o "$WASI_ARCHIVE"
fi

Z3_SRC_DIR="$BUILD_DIR/z3-src"
WASI_DIR="$BUILD_DIR/wasi-sdk"
Z3_BUILD_DIR="$BUILD_DIR/z3-build"

rm -rf "$Z3_SRC_DIR" "$WASI_DIR" "$Z3_BUILD_DIR"
mkdir -p "$Z3_SRC_DIR" "$WASI_DIR" "$Z3_BUILD_DIR"

tar -xzf "$Z3_ARCHIVE" -C "$Z3_SRC_DIR" --strip-components=1
tar -xzf "$WASI_ARCHIVE" -C "$WASI_DIR" --strip-components=1

CMAKE_TOOLCHAIN_FILE="$WASI_DIR/share/cmake/wasi-sdk.cmake"
if [[ ! -f "$CMAKE_TOOLCHAIN_FILE" ]]; then
  echo "error: could not find wasi-sdk toolchain file at $CMAKE_TOOLCHAIN_FILE" >&2
  exit 1
fi

CMAKE_FLAGS=(
  -G Ninja
  -S "$Z3_SRC_DIR"
  -B "$Z3_BUILD_DIR"
  -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_TOOLCHAIN_FILE="$CMAKE_TOOLCHAIN_FILE"
  -DZ3_BUILD_LIBZ3_SHARED=OFF
  -DZ3_BUILD_EXECUTABLE=ON
  -DZ3_BUILD_TEST_EXECUTABLES=OFF
  -DZ3_BUILD_PYTHON_BINDINGS=OFF
  -DZ3_BUILD_JAVA_BINDINGS=OFF
  -DZ3_BUILD_DOTNET_BINDINGS=OFF
  -DZ3_BUILD_DOCUMENTATION=OFF
  -DZ3_SINGLE_THREADED=ON
  -DZ3_POLLING_TIMER=ON
)

cmake "${CMAKE_FLAGS[@]}"
cmake --build "$Z3_BUILD_DIR" --target shell --parallel

BUILT_WASM="$(find_wasm_binary "$Z3_BUILD_DIR")"
mkdir -p "$(dirname "$OUT_WASM")"
cp "$BUILT_WASM" "$OUT_WASM"
sha256_file "$OUT_WASM" "$OUT_SHA"

if command -v node >/dev/null 2>&1; then
  "$ROOT_DIR/scripts/inspect-wasm-imports.js" "$OUT_WASM" "$OUT_IMPORTS"
fi

echo "Built Z3 WASI binary"
echo "  source : $BUILT_WASM"
echo "  wasm   : $OUT_WASM"
echo "  sha256 : $OUT_SHA"
if [[ -f "$OUT_IMPORTS" ]]; then
  echo "  imports: $OUT_IMPORTS"
fi
