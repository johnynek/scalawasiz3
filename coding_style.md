# Coding Style

This project prioritizes a small, predictable API and minimal runtime footprint across JVM and Scala.js.

## Design principles

1. Public APIs are immutable.
   - Do not expose mutable collections or mutable state in public signatures.
   - Method-local mutation (`var`, mutable builders, arrays) is allowed when it materially improves performance.
   - Keep mutation tightly scoped and never return mutable references.

2. Encode invariants in types.
   - Prefer typed states over ad-hoc runtime assertions.
   - Use Scala 3 features (`opaque type`, enums, ADTs, extension methods) to model validated values.
   - Follow parse-don't-verify: parse once into validated types, then operate on those types.

3. Keep dependencies minimal.
   - Production dependency target:
     - JVM: only Chicory modules needed to run WASI Z3.
     - Scala.js: zero external runtime dependencies.
   - Test-only dependencies are acceptable if they do not leak into published artifacts.

4. Keep a thin Z3-like surface first.
   - Maintain a direct string-in/string-out SMT-LIB API (`runSmt2`-style).
   - Any higher-level structured SMT API should be layered on top of the thin API.
   - The minimal API must stay usable with minimal setup and dependencies.

## Iteration style guide

- Default (clarity first): prefer `map`, `flatMap`, `foldLeft`, `collect`, and iterator pipelines.
- Non-hot-path collection traversal: prefer immutable transformations over manual mutation.
- Hot paths (byte-level work, WASI/JS interop, tight loops): `while` with method-local `var` is preferred when it clearly reduces allocation/overhead.
- Keep imperative loops local to implementation internals; avoid exposing mutable iteration state in public APIs.
- If choosing imperative iteration for performance, add a short comment when the reason is not obvious.

## Repo alignment snapshot (2026-02-22)

Aligned:
- Shared public API is small and immutable (`Z3Solver`, `Z3Result`).
- String-in/string-out entrypoint already exists (`runSmt2(input: String)`).
- Dependency policy is mostly met: JVM uses Chicory; Scala.js has no external runtime deps; `munit` is test-only.

Needs improvement:
- Some invariants are still conventions enforced at runtime (for example, normalized SMT input handling); these can be moved into typed wrappers over time.
- Imperative loops and local mutation are used in JS runtime and build-time byte handling; this is consistent with the performance-oriented exception above.
