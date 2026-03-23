# dev.bosatsu.scalawasiz3

A Scala 3.8.1 cross-platform library that exposes a string-in/string-out Z3 API on JVM, Scala.js, and Scala Native.

## Goals

- Single published Scala library (`dev.bosatsu.scalawasiz3`) for JVM, Scala.js, and Scala Native.
- Publish Maven coordinates under `dev.bosatsu:scalawasiz3` (with platform/cross suffixes where applicable).
- Z3 built from source in CI/release and used as the single source input for Scala.js embedding and JVM AOT generation.
- JVM execution via [Chicory](https://github.com/dylibso/chicory) build-time AOT compilation.
- Scala.js execution via an internal WASI Preview1 host (Node and browser-oriented runtime path).
- Scala Native execution via direct dynamic linking to `libz3` through the Z3 C API.

## WASM/WASI challenges addressed here

This project focuses on making Z3 run reliably as a WASI WebAssembly module:

- avoid relying on Z3 threaded/future execution paths in the wasm build;
- avoid using C++ exceptions as normal control flow on key solver paths (especially integer-heavy/tactic paths we have seen trap under WASM).

How we do this today:

- `scripts/build-z3-wasi.sh` builds Z3 with `-DZ3_SINGLE_THREADED=ON` (and `-DZ3_POLLING_TIMER=ON`) for the WASI target.
- We apply targeted patches from `scripts/z3-wasi-patches/*.patch` that replace throw/catch control-flow patterns with explicit checks on paths we have hit in practice (including `pb2bv`/QF_LIA-related regressions).

This improves parity for the SMT-LIB programs covered by our tests, but it does not guarantee all possible SMT-LIB shapes are trap-free in WASM/WASI.
You can still hit traps (for example `unreachable`) with differently shaped inputs than the ones currently covered.
If you find one, please open an issue with a minimal reproducer and expected behavior: <https://github.com/bosatsu/dev.bosatsu.scalawasiz3/issues/new>.

References:

- WebAssembly explainer: [MDN WebAssembly overview](https://developer.mozilla.org/en-US/docs/WebAssembly)
- WASI explainer: [wasi.dev](https://wasi.dev/)
- Canonical Z3 repository: [Z3Prover/z3](https://github.com/Z3Prover/z3)

## Layout

- `core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm`: source WASI module used by Scala.js embedding and JVM AOT generation.
- `core/shared/src/main/scala/dev/bosatsu/scalawasiz3`: shared API.
- `core/jvm/src/main/scala/dev/bosatsu/scalawasiz3`: JVM runtime.
- `core/js/src/main/scala/dev/bosatsu/scalawasiz3`: Scala.js runtime.
- `core/native/src/main/scala/dev/bosatsu/scalawasiz3`: Scala Native runtime.
- `scripts/build-z3-wasi.sh`: fetch + build Z3 WASI artifact.
- `scripts/build-z3-native.sh`: fetch + build `libz3` for Scala Native development/CI.
- `scripts/inspect-wasm-imports.js`: dump wasm imports.
- `scripts/check-js-wasi-coverage.js`: ensure JS WASI host covers required imports.

## Build and test

```bash
./scripts/build-z3-wasi.sh
sbt 'coreJVM/test' 'coreJS/test'
```

This repository includes a `.jvmopts` with a 4G heap because Scala.js linking for the embedded wasm payload is memory-intensive.

To run the Scala Native suite, first build `libz3` and then run:

```bash
./scripts/build-z3-native.sh
sbt 'coreNative/test'
```

For a full local check:

```bash
./scripts/build-z3-wasi.sh
./scripts/build-z3-native.sh
sbt 'coreJVM/test' 'coreJS/test' 'coreNative/test'
```

## Build embedded Z3 WASI

```bash
./scripts/build-z3-wasi.sh
```

By default this builds the full Z3 `shell` WASI command entrypoint (packaged as `z3.wasm`) and links with `--strip-all --compress-relocations` for smaller wasm output.

Expected local tools:

- `bash`
- `curl`
- `tar`
- `cmake`
- `ninja`
- `python3`
- `file`

After build, these generated (gitignored) files are updated:

- `core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm`
- `core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm.sha256`
- `core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.imports.json`

## Scala Native direct-libz3 path

Scala Native does not use `z3.wasm`. It links directly against `libz3` using the Z3 C API.

Build the repo-local dynamic library with:

```bash
./scripts/build-z3-native.sh
```

By default the script installs `libz3` under `target/z3-native-install`. Repo-local `coreNative/test` uses `target/z3-native-install/lib` automatically, or you can override the search path with `SCALAWASIZ3_Z3_NATIVE_LIB_DIR`.

Expected local tools:

- `bash`
- `curl`
- `tar`
- `cmake`
- `ninja`
- `python3`
- `clang`

On macOS with Homebrew, a typical setup is:

```bash
brew install cmake ninja llvm
export PATH="$(brew --prefix cmake)/bin:$(brew --prefix ninja)/bin:$(brew --prefix llvm)/bin:$PATH"
```

Downstream Scala Native applications also need `libz3` available at native link time and runtime. A typical app-level sbt configuration looks like:

```scala
import scala.scalanative.sbtplugin.ScalaNativePlugin.autoImport.*

nativeConfig ~= { cfg =>
  cfg.withLinkingOptions(
    cfg.linkingOptions ++ Seq(
      "-L/path/to/libz3",
      "-Wl,-rpath,/path/to/libz3"
    )
  )
}
```

Dynamic linking is the supported path for the first release. Static linking is not bundled into the published artifact.

## Scala.js wasm embedding path

Scala.js cannot load classpath resources at runtime like JVM. For JS, this project generates a managed Scala source that embeds the wasm bytes as chunked base64 literals, then decodes and reconstructs one contiguous byte array at runtime.

This keeps a single source of truth (`z3.wasm`) while producing a JS-friendly runtime representation.

## JVM Chicory AOT path

The JVM build runs Chicory's build-time compiler from `sbt` and emits generated `.class` files plus a stripped `.meta` resource under the JVM compile output. The JVM artifact excludes raw `z3.wasm` resources and does not use Chicory runtime compiler caching.

## API

```scala
import dev.bosatsu.scalawasiz3.Z3Solver

val solver = Z3Solver.default
val result = solver.runSmt2("(check-sat)")

// Optional: create an isolated reusable solver handle (useful per worker/thread)
val threadLocalSolver = Z3Solver.create()
```

`runSmt2` returns `Z3Result`, with:

- `Z3Result.Success(stdout, stderr, exitCode = 0)`
- `Z3Result.Failure(message, exitCode, stdout, stderr, cause)`

On Scala Native, `Z3_eval_smtlib2_string` returns one combined output stream, so `stdout` contains solver statuses and SMT-LIB diagnostics, while `stderr` is usually empty.

## JVM benchmark

Run the JVM benchmark harness:

```bash
sbt "project coreJVM" "runMain dev.bosatsu.scalawasiz3.JvmSolverBenchmarkMain --warmup 20 --iterations 200 --threads 4 --mode shared"
```

Modes:

- `shared`: all benchmark threads share `Z3Solver.default`
- `isolated`: each thread uses its own `Z3Solver.create()`

## CI and release

- `CI`: `.github/workflows/ci.yml`
  - builds `z3.wasm` from source
  - builds `libz3` from source for Scala Native
  - validates JS WASI import coverage
  - runs JVM, Scala.js, and Scala Native tests
- `Release`: `.github/workflows/release.yml`
  - validates tag/version
  - builds `z3.wasm` from source
  - validates coverage
  - runs `sbt ci-release`
  - uploads generated `z3.wasm` and built JVM/Scala.js/Scala Native jars to the GitHub release page on tag pushes
  - does not upload `libz3` shared/static binaries as release assets

Required GitHub secrets for release:

- `PGP_PASSPHRASE`
- `PGP_SECRET`
- `SONATYPE_USERNAME`
- `SONATYPE_PASSWORD`

## Upgrade playbook

1. Update `versions.properties` (`z3.tag`, `wasi.sdk.version`, `chicory.version` as needed).
2. Run `./scripts/build-z3-wasi.sh`.
3. Run `./scripts/build-z3-native.sh`.
4. Run `./scripts/check-js-wasi-coverage.js core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm`.
5. Run `sbt 'coreJVM/test' 'coreJS/test' 'coreNative/test'`.
6. Tag/release once CI passes; no Z3 binary artifacts are checked in.

## Current caveat

JVM/Scala.js compilation requires generated `z3.wasm` resources. If `sbt` reports missing `z3.wasm` or `z3.wasm.sha256`, run `./scripts/build-z3-wasi.sh` and rerun the build.

Scala Native compile/test does not require `z3.wasm`, but native test/link runs do require `libz3`. If `coreNative/test` reports missing `libz3`, run `./scripts/build-z3-native.sh` and rerun the build.
