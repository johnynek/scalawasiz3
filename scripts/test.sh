#!/usr/bin/env bash
# Full local cross-platform check described in README.md.
set -euo pipefail
cd "$(dirname "$0")/.."

# Keep source builds bounded on shared worker hosts; callers can choose another cap.
export CMAKE_BUILD_PARALLEL_LEVEL="${CMAKE_BUILD_PARALLEL_LEVEL:-2}"
./tests/release-workflow-trigger.sh
./scripts/build-z3-wasi.sh
./scripts/build-z3-native.sh
./scripts/check-js-wasi-coverage.js core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm
exec sbt -batch 'coreJVM/test' 'coreJS/test' 'coreNative/test'
