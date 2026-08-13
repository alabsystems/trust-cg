# trust-cg replacement-readiness ledger

Version: v0.1.0 publication audit, 2026-07-22.

## Decision

trust-cg is **not** ready to replace LLVM, rustc's production codegen backends,
or another general-purpose compiler backend. v0.1.0 is a source-only research
preview with useful fail-closed slices and verification infrastructure.

“Implemented” in this ledger means that a bounded path exists and has targeted
tests. It does not mean complete language, target, ABI, object, or proof
coverage.

## Replacement gates

| Area | v0.1.0 state | What blocks replacement |
| --- | --- | --- |
| trust-ir input | Partial | Complete type, constant, instruction, dialect, global, metadata, lifetime, parser/binary, and semantic coverage. |
| Rust frontend bridge | Experimental and partial | Full stable rustc MIR, layout, mono-item, ABI, runtime, panic/unwind, drop, trait-object, TLS, static/vtable, and ecosystem coverage. |
| AArch64 backend | Useful partial path | Complete ABI/aggregate handling, relocations, TLS, atomics, unwind/debug, SIMD, OS/object variants, and proof coverage. |
| x86-64 backend | Useful partial path | Full SysV/Win64 parity, aggregates, relocations, TLS, atomics, unwind/debug, vector/AVX, OS/object variants, and proof coverage. |
| RISC-V 64 backend | Experimental | Product ABI/object support, broad ISA semantics, proof emission, and execution validation. |
| Optimizations | Mixed maturity | A transformation-by-transformation authority policy and complete proof or validation coverage across targets and widths. |
| Register allocation | Implemented with validators on selected paths | Complete spill/pair/vector/debug/unwind interactions and compositional correctness evidence. |
| Object and linker boundary | Partial | Faithful relocation/linker/runtime models and independently checked authority for every published artifact path. |
| JIT publication | Experimental | Complete memory-protection, relocation, code-install, cache/provenance, target, and concurrency guarantees. |
| Proof chain | Partial | Production binding from source semantics through every transformation and emitted byte, plus independent replay for every claimed certificate. |
| Lean development | Conditional and incomplete | Remove classified `sorry`/axiom dependencies, close call/control/concurrency gaps, and connect the model to the Rust emitter. |
| Validation matrix | Local, host-dependent gates | Reproducible multi-host and multi-target validation with pinned toolchains and non-vacuous runtime/object checks. |

## Rust bridge boundary

The nightly `rustc_codegen_trust_cg` bridge is an evaluation surface, not a
drop-in Rust backend. It admits selected scalar functions and bounded MIR/ABI
shapes and rejects many unsupported variants with named diagnostics. The
detailed conservative inventory is
[`rustc-mir-coverage-inventory.md`](rustc-mir-coverage-inventory.md).

Replacement remains blocked on at least:

- rustc `TyAndLayout`, aggregate/scalar-pair/indirect ABI classification, and
  target call attributes;
- complete places, projections, allocation/provenance, drops, unwinding,
  coroutines, inline/global assembly, statics, vtables, and TLS;
- runtime, panic strategy, allocator, linkage, LTO/codegen-unit, debuginfo, and
  ecosystem behavior;
- differential execution of a broad Rust corpus on every claimed target.

Fail-closed rejection is valuable safety behavior, but it is not feature
parity.

## Backend boundary

The primary AArch64 and x86-64 paths implement real instruction selection,
register allocation, encoding, object emission, and JIT machinery. Their
supported surfaces are not symmetrical and do not cover all ABI, vector,
atomic, relocation, unwind, debug, or runtime cases.

Opcode-coverage percentages refer only to the classifier's current emittable
denominator and its evidence rules. They must not be read as percentages of an
ISA, a language, a whole compiler, or emitted-byte correctness.

Any replacement claim would require, for each target and object format:

- a complete, explicit ABI and data-layout contract;
- full relocation and linker-visible symbol behavior;
- unwind/exception, TLS, atomics, memory ordering, debug, and runtime behavior;
- faithful semantic models tied to the actual encoder and object writer;
- negative tests proving unsupported cases remain rejected;
- execution/differential coverage on the target, without vacuous skips.

## Evidence boundary

v0.1.0 distinguishes exhaustive, statistical, external-SMT, and independently
replayed evidence. These labels are not interchangeable.

- Statistical 32/64-bit evaluator runs are regression tests, not proofs.
- An SMT `Verified` verdict is only about the represented obligation and trusts
  its encoding, bridge, and solver unless independently replayed.
- A coverage row can establish that an obligation is wired without proving the
  full instruction, pass, object, or program semantics.
- The Lean capstone is conditional and does not establish the production
  compiler premise for arbitrary input.
- A serialized or unsigned certificate is not automatically an independent
  proof chain.

Replacement requires a compositional argument covering validation, lowering,
optimization, register allocation, encoding, object/link behavior, and runtime
execution for every admitted program. That argument does not exist today.

## v0.1.0 release gates

The publication candidate is expected to satisfy the committed, documented
local gates, including:

- locked workspace compilation and focused CLI tests;
- the exact README quick start;
- verification, coverage, certificate, transform, vendored-source, secret, and
  forbidden-content checks listed by the publication workflow;
- the pinned cross-repository soundness gate against clean candidate
  worktrees;
- a clean, immutable commit exported and rechecked from an anonymous clone.

These gates establish release hygiene and named regression floors. They do not
change the replacement decision above.

## Criteria for changing the decision

This ledger can move from **blocked** only after all of the following are true:

1. The admitted source and trust-ir semantics are complete for the proposed
   replacement scope.
2. The Rust/MIR or other frontend boundary has complete layout, ABI, runtime,
   and language coverage for that scope.
3. Every target/object path has complete modeled behavior and non-vacuous
   execution validation.
4. Unsupported behavior is absent from the proposed scope or provably
   fail-closed before artifact publication.
5. The proof/evidence chain composes through every transformation and emitted
   byte, with its trusted base explicitly bounded.
6. The result is reproduced from clean, pinned source on the supported host and
   target matrix.

Until then, describe trust-cg as a **proof-oriented research backend**, not a
verified replacement compiler.
