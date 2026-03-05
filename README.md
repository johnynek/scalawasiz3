# dev.bosatsu.scalawasiz3

A Scala 3.8.1 cross-platform library that embeds a WASI build of Z3 and exposes a string-in/string-out API.

## Goals

- Single published Scala library (`dev.bosatsu.scalawasiz3`) for JVM and Scala.js.
- Publish Maven coordinates under `dev.bosatsu:scalawasiz3` (with platform/cross suffixes where applicable).
- Z3 built from source in CI/release and used as the single source input for Scala.js embedding and JVM AOT generation.
- JVM execution via [Chicory](https://github.com/dylibso/chicory) build-time AOT compilation.
- Scala.js execution via an internal WASI Preview1 host (Node and browser-oriented runtime path).

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
- `scripts/build-z3-wasi.sh`: fetch + build Z3 WASI artifact.
- `scripts/inspect-wasm-imports.js`: dump wasm imports.
- `scripts/check-js-wasi-coverage.js`: ensure JS WASI host covers required imports.

## Build and test

```bash
sbt 'coreJVM/test' 'coreJS/test'
```

This repository includes a `.jvmopts` with a 4G heap because Scala.js linking for the embedded wasm payload is memory-intensive.

## Build embedded Z3 WASI

```bash
./scripts/build-z3-wasi.sh
```

By default this builds Z3's reduced `smt2_main` WASI command entrypoint (packaged as `z3.wasm`) and links with `--strip-all --compress-relocations` for smaller wasm output.

Set `WASM_BUILD_TARGET=shell` to build the full `z3 -smt2 -in` command entrypoint instead.

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
  - validates JS WASI import coverage
  - runs JVM and JS tests
- `Release`: `.github/workflows/release.yml`
  - validates tag/version
  - builds `z3.wasm` from source
  - validates coverage
  - runs `sbt ci-release`
  - uploads generated `z3.wasm` and built jars to the GitHub release page on tag pushes

Required GitHub secrets for release:

- `PGP_PASSPHRASE`
- `PGP_SECRET`
- `SONATYPE_USERNAME`
- `SONATYPE_PASSWORD`

## Upgrade playbook

1. Update `versions.properties` (`z3.tag`, `wasi.sdk.version`, `chicory.version` as needed).
2. Run `./scripts/build-z3-wasi.sh`.
3. Run `./scripts/check-js-wasi-coverage.js core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm`.
4. Run `sbt 'coreJVM/test' 'coreJS/test'`.
5. Tag/release once CI passes; no Z3 binary artifacts are checked in.

## Current caveat

Generated Z3 resources are required for compilation. If `sbt` reports missing `z3.wasm` or `z3.wasm.sha256`, run `./scripts/build-z3-wasi.sh` and rerun the build.
