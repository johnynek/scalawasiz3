# Pre-PR Review Guidance

Review in this order:
1. Correctness and robustness.
2. Performance.
3. Idiomatic code in the style of this repo.

This repo aims for a very small, predictable surface over Z3. Be conservative about widening the API, adding dependencies, or introducing hidden runtime behavior.

Please watch for:
- Cross-backend semantic parity matters. JVM, Scala.js, and native implementations may differ internally, but `runSmt2`-level results, errors, and edge-case behavior should stay aligned unless a PR makes the divergence explicit and tests it.
- Do not accept unsafe casts. Keep methods parametric. Avoid dynamic dispatch based on runtime type except normal idiomatic pattern matches on sealed ADTs or enums.
- Prefer type classes such as `Hash`, `Order`, `Eq`, and `Show` over JVM `hashCode`, `compareTo`, `equals`, and `toString`.
- FFI and resource ownership must be exact. Buffers, handles, and backend-specific resources need correct lifetime management, explicit failure handling, and no leaks.
- Do not paper over backend faults with hacks or best-effort fallbacks that make unsupported cases look handled. If a case is not actually supported, the behavior should stay explicit and tested.
- Preserve the thin API and canonical resource/build layout. Avoid extra environment-specific file or resource fallback paths, duplicated build logic, or surprising alternate execution paths. Factor shared helpers instead of copying backend or build code.
- Prefer parse-don't-verify and encoding invariants in types. Use small ADTs, `opaque type`, enums, and explicit result types instead of sentinel values or ad hoc conventions.
- Performance is important. Extra allocation, async machinery, and abstraction overhead in hot paths need justification. Local mutation and `while` loops are acceptable only when they materially improve throughput and stay tightly scoped.
- Keep dependencies minimal, especially in published runtime artifacts. Build-only or test-only dependencies are preferred when possible.
- Release and workflow correctness count as correctness. Catch tag and version mistakes early, fail fast before long builds, avoid dirty-worktree assumptions, and preserve the checked-in wasm/resource invariants.
- Require focused regression tests for backend parity, failure modes, trap behavior, codec and FFI changes, and release workflow invariants. For semantic fixes, prefer exact SMT2 cases that previously failed.
- If a change is intentionally less idiomatic for performance, that tradeoff should be rare and justified in the code or PR.
