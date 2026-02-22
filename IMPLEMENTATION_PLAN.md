# Scala Z3 WASI Library Plan

## Scope and constraints

- [x] Target Scala version: `3.8.1` only (no cross-Scala matrix for now).
- [x] Use package namespace `dev.bosatsu.scalawasiz3`.
- [x] Place source/resource files under `dev/bosatsu/scalawasiz3` paths.
- [ ] Build and publish a Scala library that exposes a simple string-in/string-out Z3 API.
- [x] Keep runtime dependencies minimal: users depend on this library only.
- [ ] Build Z3 as a WASI module locally in this repo, and embed that `.wasm` in published jars.
- [x] Support JVM (via Chicory) and Scala.js (Node + browser) behind one consistent Scala API.

## Phase 1: Repository and sbt scaffolding

- [x] Initialize sbt multi-platform structure:
  - `project/plugins.sbt` with Scala.js + crossproject plugins.
  - root aggregate project.
  - `core` crossProject (`JVMPlatform`, `JSPlatform`) with shared sources.
- [x] Add baseline settings:
  - organization/name/version scheme
  - Scala `3.8.1`
  - publishing metadata (homepage/licenses/scm/developers)
  - test framework setup
- [x] Configure Scala.js module output for JS module interop (`ModuleKind.ESModule`).
- [x] Add a reproducible versions file (`versions.properties` or `project/Versions.scala`) for:
  - Z3 version/tag
  - WASI SDK version
  - Chicory version

## Phase 2: Z3 WASI build pipeline (scripted)

- [x] Add `scripts/build-z3-wasi.sh` that:
  - validates required host tools (`bash`, `curl`, `tar`, `cmake`, `ninja`, `python3`)
  - downloads pinned Z3 source tarball/tag
  - downloads pinned WASI SDK release (host-specific archive)
  - verifies checksums when provided
  - configures CMake with WASI toolchain
  - builds the Z3 CLI executable as WebAssembly
  - copies final artifact to project resources
- [x] Start with this CMake configuration (adjust only if build proves otherwise):
  - `-DCMAKE_TOOLCHAIN_FILE=<wasi-sdk>/share/cmake/wasi-sdk.cmake`
  - `-DCMAKE_BUILD_TYPE=Release`
  - `-DZ3_BUILD_LIBZ3_SHARED=OFF`
  - `-DZ3_BUILD_EXECUTABLE=ON`
  - `-DZ3_BUILD_TEST_EXECUTABLES=OFF`
  - `-DZ3_BUILD_PYTHON_BINDINGS=OFF`
  - `-DZ3_BUILD_JAVA_BINDINGS=OFF`
  - `-DZ3_BUILD_DOTNET_BINDINGS=OFF`
  - `-DZ3_BUILD_DOCUMENTATION=OFF`
  - `-DZ3_SINGLE_THREADED=ON`
  - `-DZ3_POLLING_TIMER=ON`
- [x] Ensure script output is deterministic and CI-friendly:
  - build dir under `target/` (or `.cache/`)
  - explicit output path for wasm (e.g. `core/shared/src/main/resources/dev/bosatsu/scalawasiz3/z3/z3.wasm`)
  - emit artifact SHA256 to a small metadata file next to wasm

## Phase 3: Resource embedding strategy

- [x] Treat `z3.wasm` as a first-class packaged resource in shared module jars.
- [x] JVM access path:
  - load bytes from classpath resource (`getResourceAsStream`)
  - feed bytes directly to Chicory parser
- [x] Scala.js access path:
  - do not rely on JVM classloader APIs (not available in Scala.js runtime)
  - generate Scala source at build time that embeds chunked literal byte arrays from `z3.wasm`
  - reconstruct one contiguous `Array[Byte]` at runtime from generated chunks
  - keep source of truth as the packaged resource file so the published jar still contains wasm

## Phase 4: Runtime API and execution wrappers

- [x] Define shared API (simple at first):
  - input: SMT-LIB string
  - output: stdout string (or structured success/error ADT)
- [x] JVM implementation (`coreJVM`):
  - use Chicory `WasiPreview1`
  - wire stdin/stdout/stderr with byte array streams
  - instantiate module and execute command-style `_start`
  - return stdout, map non-zero/proc_exit to library error type
- [x] JS implementation (`coreJS`) with two execution environments:
  - Node: use WASI-compatible import wiring suited for Node runtime.
  - Browser: provide a minimal Preview1 import object for the exact imports required by built `z3.wasm`.
- [x] Keep the same Scala API for both targets and hide environment-specific details.

## Phase 5: Import-surface validation for JS/browser

- [x] Add a script/check to inspect wasm imports after build (store import list artifact in CI).
- [x] Use that import list to drive browser host implementation scope.
- [x] If import surface grows unexpectedly, fail CI with actionable message.

## Phase 6: Tests

- [x] Shared behavior tests for the facade API.
- [x] JVM integration tests:
  - smoke test `(check-sat)` request through stdin/stdout path.
- [x] Scala.js Node tests:
  - same smoke test under Node JS env.
- [x] Browser smoke test:
  - run minimal browser execution test in CI (headless) to prove web support.
- [ ] Regression tests:
  - resource presence check in packaged artifacts
  - stable output for a small set of canned inputs.

## Phase 7: GitHub Actions CI/CD

- [x] `ci.yml` workflow:
  - checkout
  - setup Java + sbt
  - setup build dependencies for WASI/Z3 script
  - run `scripts/build-z3-wasi.sh`
  - run JVM + JS tests
  - run browser smoke test
  - upload wasm/import-manifest/test artifacts
- [x] Cache strategy:
  - cache Coursier/Ivy/sbt
  - cache downloaded WASI SDK and Z3 source tarballs by version key
- [x] `release.yml` workflow:
  - based on `sbt-ci-release` flow
  - add pre-release step that rebuilds/verifies `z3.wasm`
  - run `sbt ci-release` for Maven Central publishing

## Phase 8: Maven Central publishing setup

- [x] Use `sbt-ci-release` with Central Portal credentials.
- [x] Publish module as `dev.bosatsu:scalawasiz3` (module name `scalawasiz3`).
- [x] Configure required GitHub secrets:
  - `PGP_SECRET`
  - `PGP_PASSPHRASE`
  - `SONATYPE_USERNAME`
  - `SONATYPE_PASSWORD`
- [ ] Verify signed artifacts include:
  - JVM jar + sources + javadoc
  - Scala.js artifacts
  - embedded `z3.wasm` resource

## Release asset publishing

- [x] Attach `z3.wasm` and built jars to GitHub release assets on tag pushes.

## Phase 9: Hardening and documentation

- [x] Add README sections:
  - architecture overview
  - how wasm is built/updated
  - JVM/JS runtime behavior
  - supported environments and caveats
- [x] Document upgrade playbook:
  - bump Z3
  - bump WASI SDK
  - rebuild wasm
  - re-run import-surface validation/tests

## Proposed execution order (strict)

- [x] 1. sbt scaffold + cross-project layout
- [ ] 2. `build-z3-wasi.sh` end-to-end producing `z3.wasm`
- [x] 3. resource embedding + JVM loading path
- [x] 4. JVM Chicory wrapper + JVM tests
- [x] 5. Scala.js byte-embedding + Node wrapper + Node tests
- [x] 6. browser wrapper + browser smoke test
- [x] 7. CI workflows
- [x] 8. release/publishing wiring
- [x] 9. docs + upgrade playbook

## Notes to validate early (high risk)

- [ ] Confirm Z3 compiles cleanly with current WASI SDK in single-threaded mode.
- [ ] Confirm chosen wasm imports are implementable in browser without third-party runtime dependencies.
- [ ] Confirm packaged-resource strategy works for both published JVM and Scala.js artifacts.

## References consulted for this plan

- [ ] Z3 CMake options and executable build switches:  
      `https://github.com/Z3Prover/z3/blob/master/CMakeLists.txt`  
      `https://github.com/Z3Prover/z3/blob/master/src/CMakeLists.txt`
- [ ] Z3 CLI stdin option (`-in`) and shell behavior:  
      `https://github.com/Z3Prover/z3/blob/master/src/shell/main.cpp`
- [ ] WASI SDK toolchain usage and constraints:  
      `https://github.com/WebAssembly/wasi-sdk/blob/main/README.md`
- [ ] WASI libc target notes (`wasm32-wasip1`, threads caveat):  
      `https://github.com/WebAssembly/wasi-libc/blob/main/README.md`
- [ ] Chicory WASI Preview1 usage and stdin/stdout wiring:  
      `https://github.com/dylibso/chicory/blob/main/docs/docs/usage/wasi.md`
- [ ] Chicory parser byte-array parsing API:  
      `https://github.com/dylibso/chicory/blob/main/wasm/src/main/java/com/dylibso/chicory/wasm/Parser.java`
- [ ] Scala.js module and `@JSImport` behavior:  
      `https://www.scala-js.org/doc/project/module.html`  
      `https://www.scala-js.org/doc/interoperability/facade-types.html`
- [ ] Scala.js + Vite asset pseudo-module pattern (for browser asset path approach):  
      `https://www.scala-js.org/doc/tutorial/scalajs-vite.html`
- [ ] Node WASI API (`version: "preview1"`, import object model):  
      `https://nodejs.org/api/wasi.html`
- [ ] `WebAssembly.instantiateStreaming` browser loading model:  
      `https://developer.mozilla.org/en-US/docs/WebAssembly/Reference/JavaScript_interface/instantiateStreaming_static`
- [ ] sbt-ci-release + Central Portal migration/secrets/workflow:  
      `https://github.com/sbt/sbt-ci-release/blob/main/readme.md`  
      `https://central.sonatype.org/publish/publish-portal-ossrh-staging-api/`
