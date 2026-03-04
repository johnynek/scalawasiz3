# dev.bosatsu.scalawasiz3

A Scala 3.8.1 cross-platform library that embeds a WASI build of Z3 and exposes a string-in/string-out API.

## Goals

- Single published Scala library (`dev.bosatsu.scalawasiz3`) for JVM and Scala.js.
- Publish Maven coordinates under `dev.bosatsu:scalawasiz3` (with platform/cross suffixes where applicable).
- Z3 built from source in CI/release and distributed as an embedded `z3.wasm` resource in published artifacts.
- JVM execution via [Chicory](https://github.com/dylibso/chicory).
- Scala.js execution via an internal WASI Preview1 host (Node and browser-oriented runtime path).

## Layout

- `core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm`: embedded WASI module.
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

### Chicory runtime-compiler directory cache

Set the JVM system property `scalawasiz3.chicory.runtimeCompilerCacheDir` to enable Chicory's on-disk cache:

```bash
mkdir -p /tmp/scalawasiz3-chicory-cache
sbt -Dscalawasiz3.chicory.runtimeCompilerCacheDir=/tmp/scalawasiz3-chicory-cache "project coreJVM" "runMain dev.bosatsu.scalawasiz3.JvmSolverBenchmarkMain --warmup 20 --iterations 200 --threads 4 --mode shared"
```

- If the property is unset, runtime-compiled bytecode is reused in-memory for the current process only.
- If the property is set, runtime-compiled bytecode is also persisted to disk and can be reused across process restarts.
- In this benchmark harness, steady-state throughput is usually similar either way; the cache is mainly useful for startup compile reuse.

## Recent benchmark runs (M3 MacBook Air)

These point-in-time runs (March 2026) used:

```bash
sbt "project coreJVM" "runMain dev.bosatsu.scalawasiz3.JvmSolverBenchmarkMain --warmup 20 --iterations 200 --threads N --mode shared"
```

Before runtime compiler path (pre-PR #20):

- 1 thread: `2.51 calls/s` (200 calls in `79.794s`)
- 4 threads: `4.50 calls/s` (200 calls in `44.478s`)

After runtime compiler path (no cache dir):

- 1 thread: `50.68 calls/s` (200 calls in `3.946s`)
- 4 threads: `125.56 calls/s` (200 calls in `1.593s`)

After runtime compiler path (cache dir set):

- 1 thread (first cached run): `47.43 calls/s` (200 calls in `4.217s`)
- 1 thread (warm cached run): `50.29 calls/s` (200 calls in `3.977s`)
- 4 threads (first cached run): `135.35 calls/s` (200 calls in `1.478s`)
- 4 threads (warm cached run): `115.56 calls/s` (200 calls in `1.731s`)

Expect run-to-run variance; cache-dir benefit is primarily across fresh JVM process starts.

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
