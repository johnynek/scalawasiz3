# dev.bosatsu.scalawasiz3

A Scala 3.8.1 cross-platform library that embeds a WASI build of Z3 and exposes a string-in/string-out API.

## Goals

- Single published Scala library (`dev.bosatsu.scalawasiz3`) for JVM and Scala.js.
- Publish Maven coordinates under `dev.bosatsu:scalawasiz3` (with platform/cross suffixes where applicable).
- Z3 distributed as an embedded `z3.wasm` resource in published artifacts.
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

After build, these files are updated:

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
```

`runSmt2` returns `Z3Result`, with:

- `Z3Result.Success(stdout, stderr, exitCode = 0)`
- `Z3Result.Failure(message, exitCode, stdout, stderr, cause)`

## CI and release

- `CI`: `.github/workflows/ci.yml`
  - builds `z3.wasm`
  - validates JS WASI import coverage
  - runs JVM and JS tests
- `Release`: `.github/workflows/release.yml`
  - rebuilds wasm
  - validates coverage
  - runs `sbt ci-release`
  - uploads `z3.wasm` and built jars to the GitHub release page on tag pushes

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
5. Commit updated wasm resource + metadata.

## Current caveat

Repository bootstrap currently includes a tiny placeholder wasm module so the project compiles before first real Z3 build. Run `./scripts/build-z3-wasi.sh` to replace it with the actual Z3 artifact.
