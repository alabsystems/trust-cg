# Linux AArch64 zero-sized tuple carriers

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Nonempty tuples whose complete frontend layout has zero size now use the Unit
value carrier on Linux AArch64. Their MIR field types, projections, drop glue
and alignment requirements remain intact. This fixes generic `FnOnce`/`FnMut`
calls whose argument tuple contains only zero-sized values, including the
`ControlFlow::map_break` constructor-function case found in std.

Source commit: `63296774e`. Remote AArch64 sealed-JIT-link changes are merged at
`b84eea509`. The combined compiler is rebuilt and independently qualified.

## Native qualification

The baseline rejects the small generic-call reproducer at O0/O2 while LLVM
executes it correctly. The repaired backend passes both. The expanded permanent
fixture passes **589,824 checks in 16 executions** across LLVM/CG, O0–O3 and
abort/unwind panic modes. Its eight functions cover ordinary and nested
zero-sized argument tuples, function items, function pointers, mutable closures,
mixed scalar/ZST parameters, tuple returns, 16-byte-aligned borrows and observable
destructor ordering. The driver checks both the scalar result and the exact
two-destructor event sequence.

The new fixture plus the zero-sized-drop and union/array-transmute controls pass
**1,180,920 checks in 48 executions** on the first backend. Four compilation
lanes deliberately refuse 64-byte-aligned zero-sized borrows; all four LLVM
controls compile. The permanent negative fixture now includes both the existing
standalone guard and a tuple containing it. The merged rebuild repeats the new
fixture and zero-sized-drop controls: 591,096 checks in 32 executions, plus the
same four alignment refusals.

The first expanded exploratory corpus used 64-byte alignment and correctly
remained refused after the tuple-carrier repair. Version 2 uses supported
16-byte alignment for native qualification. Both original failure logs and
separately named sources are retained; the alignment gate was not weakened.

## Libraries, integration and unfinished work

A fresh mixed library with CG-built core and alloc at O2 and LLVM-built remaining
std crates passes exact-library dynamic consumers: 21,504 network/escape-format
checks, 81,097 UTF-8/character checks with each consumer backend, and 112 caught
panic/destructor cases. Invocation records, sysroot hashes and loader logs
identify the artifacts. These library runs use the first backend, before the
JIT-only merge. They are correctness checks, not controlled performance results.

The merged workspace runs the incoming `aarch64_compiler_jit_sealed_link` test
and the existing `aarch64_checked_functions` tests. Their frozen executable
hashes, build commands and results are retained. The sealed-link change is
attributed to the upstream commit and its own performance report; this report
makes no new JIT timing claim.

The previously completed isolated O2 std census has 233 failed roots. A separate
full-std census for this tuple repair is ongoing and is not evidence in this
report. Full CG std, complete machine proof, self-hosting and strict compile-time
and runtime wins over LLVM and Clang remain unfinished.

## Proof boundaries and provenance

Strict bridge coverage passes O0/O2 before and after the merge: 34/29 MIR
functions, 14/17 refined scalar obligations, 2/6 memo hits, zero skips and zero
unmodeled shapes. Layout queries, memory, operand wiring and control flow remain
trusted. Machine-proof-required probes retain `TCG-PROOF-465` refusals. Native
runs use diagnostic `no-proof-certs`; frontend verification is off.

Frozen backend SHA256 identities:

- Minimal baseline: `e7c28938cf451256377e7a1b23d91be4f58ddd94222585619199345672b4a3b8`
- Expanded baseline: `9d81f8d89e51c32e7e2b58a5d93553c5ed9180cc5f8411f8850340c5b31b7cbd`
- First repair: `1a6cc67befb08366c2523a3c09e71cd4ea73564fbe71ac10ca6432dc055f8e13`
- Merged repair: `354ccf877d504a9a77c0583dd4806cb440b6383de30703bea135a12f0a0b43ab`

The first repair is built from `8b3e15d8a` plus the recorded ten-line production
patch. The merged backend is built from `b84eea509`. Trust frontend:
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`; TrustIR:
`824174a164de10dba2053e387dfc4b1140960885`. Source snapshots, patches, harness
input hashes, receipts, commands, compressed logs and evidence hashes accompany
this report. Frozen binaries and complete ELF inventories remain local under
`target/zst-tuple-investigation/`; independent binary publication remains open.
