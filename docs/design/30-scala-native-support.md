---
issue: 30
priority: 3
touch_paths:
  - build.sbt
  - project/plugins.sbt
  - versions.properties
  - core/native/src/main/scala/dev/bosatsu/scalawasiz3/Z3Platform.scala
  - core/native/src/main/scala/dev/bosatsu/scalawasiz3/NativeZ3Solver.scala
  - core/native/src/main/scala/dev/bosatsu/scalawasiz3/Z3NativeApi.scala
  - core/native/src/test/scala/dev/bosatsu/scalawasiz3/NativeZ3SolverSuite.scala
  - scripts/build-z3-native.sh
  - .github/workflows/ci.yml
  - .github/workflows/release.yml
  - README.md
depends_on: []
estimated_size: M
generated_at: 2026-03-23T19:10:59Z
---

# Scala Native support via direct libz3 integration

_Issue: #30 (https://github.com/johnynek/scalawasiz3/issues/30)_

## Summary

Add Scala Native as a third platform by calling `libz3` through the Z3 C API, keep the existing `Z3Solver` surface unchanged, ship dynamic linking first, and explicitly defer bundled/prelinked static Z3 binaries.

## Context

Today the repository is a JVM/Scala.js `crossProject` with one shared API, `Z3Solver`, and two platform-specific runtimes:

- JVM runs the checked/generated `z3.wasm` through Chicory AOT.
- Scala.js embeds the same `z3.wasm` and executes it through the in-repo WASI host.
- The build currently assumes the WASM artifact exists before compilation.

Issue #30 asks whether Scala Native support should be added, whether it should link directly to Z3, and whether users would need Z3 installed locally or whether a statically linked artifact could be published instead.

## Goals

- Publish a Scala Native artifact for the same library and package namespace.
- Preserve the existing public API shape: `Z3Solver.default`, `Z3Solver.create()`, and `runSmt2(input: String): Z3Result`.
- Avoid requiring an external `z3` executable process.
- Keep JVM and Scala.js behavior unchanged.
- Provide a clear build, CI, and release story for Linux and macOS.

## Non-goals

- Do not add a typed Z3 AST API in this change.
- Do not replace the JVM/Scala.js WASM-based implementation.
- Do not make Windows a day-one support target.
- Do not promise a bundled, portable, prelinked `libz3` inside the published Maven artifact.

## Decision

Scala Native support should be implemented as a third platform that calls `libz3` through the Z3 C API, not by reusing the WASI module.

This is the preferred design for three reasons:

- Scala Native can link directly against a C ABI, so the WASM runtime layer is unnecessary overhead on this platform.
- The current public API is already string-in/string-out, and Z3 exposes `Z3_eval_smtlib2_string`, which maps well to that model.
- Native `libz3` avoids the specific WASI trap and embedding constraints that the current JVM/JS implementations are working around.

The initial release should use dynamic linking against `libz3`. Static linking may be supported later as an opt-in consumer build mode, but it should not be the default or the publishing model for the library.

## Proposed Architecture

### Build topology

- Add the Scala Native sbt plugin and the Scala Native crossproject plugin.
- Expand `core` from `crossProject(JSPlatform, JVMPlatform)` to `crossProject(JSPlatform, JVMPlatform, NativePlatform)`.
- Add `coreNative` to the root aggregate and release flow.
- Refactor the existing WASM resource checks and source generators so they apply only to JVM and Scala.js. Native-only compile/test must not depend on `z3.wasm` or `scripts/build-z3-wasi.sh`.

This keeps the current shared API and tests in `core/shared`, while allowing a native runtime in `core/native`.

### Native runtime

Add a Scala Native implementation with three files:

- `Z3Platform.scala` for native platform wiring.
- `NativeZ3Solver.scala` for runtime behavior.
- `Z3NativeApi.scala` for the minimal extern bindings to the Z3 C API.

The initial binding surface should stay intentionally small:

- `Z3_mk_config`
- `Z3_set_param_value` if needed for parity settings
- `Z3_mk_context` or `Z3_mk_context_rc`
- `Z3_del_context`
- `Z3_del_config`
- `Z3_eval_smtlib2_string`
- `Z3_get_error_code`
- `Z3_get_error_msg`

`NativeZ3Solver.runSmt2` should follow this flow:

1. Normalize input the same way current backends do, including appending `(exit)` when missing.
2. Create a fresh Z3 config and context.
3. Call `Z3_eval_smtlib2_string`.
4. Copy the returned C string into a Scala `String` immediately.
5. Inspect the Z3 error code and message.
6. Return `Z3Result.Success` when evaluation completed without Z3 errors, otherwise return `Z3Result.Failure` with the copied output and error text.
7. Always destroy the native context/config in a `finally` path.

The native implementation should create a fresh context per `runSmt2` call.

That is the safest default because:

- `Z3_eval_smtlib2_string` is stateful across calls on the same context.
- Z3 contexts are not thread-safe.
- The current JVM/JS implementations already behave like isolated per-call solver executions.

This means `Z3Solver.default` can remain a singleton without shared native mutable state. `Z3Solver.create()` can still return a separate lightweight handle for API consistency, but it does not need to own a long-lived native context in the first iteration.

If later benchmarks show context creation dominates runtime, a follow-up can add per-handle reuse behind internal reset/synchronization logic.

### Linking model

The native bindings should use `@link("z3")`, so Scala Native links against `libz3` at native link time.

Phase 1 support model:

- Dynamic link against `libz3` on Linux and macOS.
- Provide a repo-local helper script, `scripts/build-z3-native.sh`, that downloads the pinned Z3 version and builds `libz3` for CI/local development.
- CI should set the appropriate linker and loader search paths when running `coreNative/test`.

This means the first shipped Scala Native artifact assumes `libz3` is available to the native linker/loader when a downstream application is built and run.

## Why not publish a statically linked Z3 inside the library?

The answer to the issue question is: not as the default packaging model for this project.

Reasons:

- Scala Native publishes jars containing Scala/NIR artifacts. Final native linking happens in the downstream application build, not when this library is published.
- A single Maven artifact cannot realistically carry one portable prelinked Z3 binary across Linux/macOS, x86_64/arm64, and differing C++ runtime/ABI combinations.
- Scala Native explicitly positions bundled native sources/resources as glue code support, not as a general-purpose way to distribute large third-party C/C++ libraries.
- Static linking of Z3 is materially more platform-specific than dynamic linking because it also drags in C++ runtime/linker concerns.

So the design should be:

- Dynamic `libz3` is the default supported path.
- Static linking is an optional later enhancement for consumers who explicitly provide a matching `libz3.a` and required linker flags in their app build.
- The repository may build `libz3.a` in local tooling for experiments, but the published Scala artifact should not embed or promise it.

## Testing and CI

Shared tests should run on Native wherever they already express backend-agnostic behavior:

- smoke suite
- golden response suite
- syntax and regression suites

Add at least one native-specific suite to cover the direct-link backend and its assumptions.

CI changes should include:

- build or install `libz3` on Linux and macOS
- run `sbt 'coreNative/test'`
- optionally add a native smoke executable once a native `Main` path exists

Release changes should include publishing the Scala Native artifact alongside the existing JVM and JS artifacts, but should not upload `libz3` shared/static binaries as release assets.

## Alternatives Considered

### Reuse `z3.wasm` on Scala Native

Rejected.

It would keep the extra WASM runtime layer on a platform that can already call the solver natively, and it would preserve many of the same failure modes and build constraints the current WASM path already has.

### Shell out to a `z3` executable

Rejected.

This would require an installed executable, add process-management overhead, and weaken the library’s current embedded-runtime story.

### Vendor Z3 source or archives inside the Scala artifact

Rejected for the first rollout.

It would increase compile/link cost substantially, complicate publishing, and create platform-specific ABI and toolchain problems that are not justified for the initial Native target.

## Implementation Plan

1. Build plumbing
- Add Scala Native plugins.
- Expand the crossproject to include `NativePlatform`.
- Scope WASM checks/generation to JVM/JS only.

2. Native runtime
- Add the minimal Z3 C API extern bindings.
- Implement `NativeZ3Solver` and native `Z3Platform`.
- Keep `Z3Solver` public API unchanged.

3. Native library workflow
- Add `scripts/build-z3-native.sh` that builds the pinned Z3 release into a repo-local output directory.
- Wire CI to use that output directory during native compile/test.
- Document the required env vars or library path setup for local runs.

4. Release/docs
- Update README with Scala Native prerequisites and the dynamic-vs-static linking story.
- Publish the native cross artifact in the normal release job.
- Explicitly document that bundled/prelinked `libz3` is out of scope for the first release.

## Acceptance Criteria

- `coreNative` compiles and its test suite passes on Linux and macOS CI.
- Native consumers can compile unchanged code that uses `Z3Solver.default` and `Z3Solver.create()`.
- Native `runSmt2` passes the existing shared smoke, golden, and syntax regression suites with semantic parity for success/failure behavior.
- Native-only compile/test does not require `z3.wasm` or `scripts/build-z3-wasi.sh`.
- The README explains how `libz3` is provided for local development and downstream Scala Native builds.
- Release automation publishes a Scala Native artifact in addition to the existing JVM and Scala.js artifacts.
- The first release notes clearly state that dynamic `libz3` is the supported path and that static linking is opt-in and not bundled.

## Risks

- Dynamic library discovery differs between Linux and macOS, so missing loader-path configuration can create flaky or confusing failures.
- `Z3_eval_smtlib2_string` may not match the CLI/WASI stderr formatting byte-for-byte on every error path; tests should prefer semantic assertions over exact formatting where necessary.
- If context reuse is attempted too early, thread-safety and state-leak bugs are likely.
- If users strongly require default static linking, additional work will be needed around C++ runtime selection, archive distribution, and per-platform linker flags.

## Rollout Notes

- Start with Linux and macOS only.
- Ship dynamic linking first.
- Treat static linking as a follow-up experiment after the basic Scala Native artifact is stable in CI and release.
- If native publishing destabilizes the release flow, keep the code path merged but gate artifact publication until CI is reliable on both supported host OSes.
