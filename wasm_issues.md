# WASM Issues Checklist (Commit `213561d1369994c52cf62c69b84a3c194fea3337`)

This tracks WASM trap issues introduced as explicit coverage in:
`core/shared/src/test/scala/dev/bosatsu/scalawasiz3/Z3SmtLibSyntaxTrapSuite.scala`.

Goal: for each failing SMT-LIB example, find the smallest Z3 patch that makes WASM execute the input the same way native Z3 does (same solver outcome/behavior for the same SMT-LIB program).
Any discovered native-vs-WASM SMT-LIB disagreement should become a regression test that runs in our `sbt` test suite.
Our objective is to drive these differences down to a minimum.

## Failing examples checklist

- [x] `src/test/smt2print_parse.cpp::spec1` (`smt2print_parse spec1 currently traps on wasi`)
- [x] `src/test/smt2print_parse.cpp::spec2` (`smt2print_parse spec2 currently traps on wasi`)
- [x] `src/test/smt2print_parse.cpp::spec3` (`smt2print_parse spec3 currently traps on wasi`)
- [x] `src/test/smt2print_parse.cpp::spec5` (`smt2print_parse spec5 currently traps on wasi`)
- [x] `examples/c/test_capi.c::parser_example3` (`c parser_example3 currently traps on wasi`)
- [x] `examples/c/test_capi.c::smt2parser_example` (`c smt2parser_example currently traps on wasi`)

## Methodology

For each item above:

1. Reproduce on both targets:
   - Native Z3 run (expected baseline behavior).
   - WASM Z3 run (current trap/failure behavior).
2. Capture evidence:
   - Input SMT-LIB, stdout/stderr, trap message, and any stack/backtrace available.
3. Minimize the reproducer:
   - Reduce the SMT-LIB script to the smallest form that still shows native-vs-WASM divergence.
4. Classify likely root cause:
   - Thread/atomic dependency.
   - Exception/throw path not supported in current WASM build/runtime.
   - Other WASM/runtime limitation (memory, ABI, syscall, UB surfaced by WASM).
5. Locate code path in Z3:
   - Identify exact module/function where divergence or trap originates.
6. Apply a minimal patch:
   - Prefer the narrowest targeted fix that restores behavior for the reproducer.
7. Validate parity:
   - Confirm WASM now matches native Z3 for solver status and observable behavior for that SMT-LIB input.
8. Lock in regression coverage:
   - Keep/add tests that prove the issue stays fixed.
   - If we find a native-vs-WASM disagreement, add a regression test for it in the `sbt` test suite.
9. After each item:
   - Re-read this document, update checkboxes/status, and then move to the next unresolved item.

As we work through issues, if we find a better investigation/fix workflow, update this Methodology section so the process improves over time.
We do not need to minimize commits while working; make checkpoint commits after any significant progress so each step is recoverable and reviewable.
Implementation rule: commit only our patch artifacts and build integration changes (for example `scripts/z3-wasi-patches/*.patch` and build script updates), not direct edits to downloaded Z3 source trees.

## Execution strategy

We will take issues one at a time in the checklist order, driving each to closure before moving on:

1. Reproduce and minimize.
2. Implement the smallest viable Z3 patch.
3. Verify WASM output matches direct/native Z3 behavior on the same SMT-LIB input.
4. Mark the checklist item complete only after parity and regression coverage are in place.

Overall target: minimize behavioral differences between WASM and native Z3 on SMT-LIB inputs, and keep each resolved difference covered by `sbt` regression tests.

## Resolution notes

- Patch artifact used for these six items: `scripts/z3-wasi-patches/0002-wasi-noexcept-syntax-traps.patch`.
- Build/test integration now applies all patch files in `scripts/z3-wasi-patches/*.patch` in sorted order.
- Regression coverage:
  - `core/shared/src/test/scala/dev/bosatsu/scalawasiz3/Z3SmtLibSyntaxTrapSuite.scala` now asserts successful/parity behavior for the six formerly trapping SMT-LIB programs.
