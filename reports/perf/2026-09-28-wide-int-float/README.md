# Linux AArch64 128-bit integer-to-float conversion — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now lowers i128/u128 casts to f32/f64 on Linux AArch64. The frozen
compiler-builtins diagnostic census falls from 14 failing roots to 10; alloc
retains the same 148 roots. This is progress toward the sysroot, not a completed
CG-built compiler-builtins library or sysroot.

## Change

The bridge preserves the full 128-bit integer in `SIToFP`/`UIToFP`. The existing
AArch64 backend passes its low and high halves in x0:x1 to `__floattisf`,
`__floattidf`, `__floatuntisf` or `__floatuntidf`, and reads s0/d0. The source's
Rust signedness selects the conversion. Converting directly to the destination
precision avoids double rounding through f64 when the destination is f32.
Other bridge targets retain their previous 128-bit cast refusal.

The former Linux negative test is replaced by a native rounding/ABI regression.
Refinement obligations retain the full source width and signedness. No proof
requirement or unsupported-root handling is weakened.

## Evidence

| Check | Result |
| --- | --- |
| LLVM/CG Rust callers with system conversion runtime | O0–O3, 8 executions, 18,349,448 checks |
| Same callers with CG-compiled conversion runtime | O0–O3, 8 executions, 18,349,448 checks |
| Combined new native checks | 36,698,896 |
| Values per execution | 152,912 |
| Previous backend, four isolated cast directions | All four refuse at the old cast guard |
| Compiler-builtins diagnostic census | 14 → 10 roots; batch and legacy agree |
| Alloc diagnostic census | 148 roots, identical to baseline |
| Existing linkage and wide checked-return controls | 3 tests pass |
| Mandatory machine-proof control | Fails with the existing `TCG-PROOF-465` |
| All-targets compile check | Pass |

The C driver computes IEEE round-to-nearest, ties-to-even bits using integer
arithmetic only. It does not use integer-to-float casts or floating arithmetic
as its oracle. Inputs cover small positive and negative integers, every power
of two with neighboring values, midpoint neighbors at both precisions, integer
extrema, f32 overflow to infinity, and deterministic full-width random values.
Each value exercises direct calls, volatile indirect calls, four conversions
inside a function with GPR and FPR values live across calls, stack arguments,
and a subsequent C callback. The driver checks every float's exact bits and
the preserved integer/float values. All four runtime references are required
in the CG caller objects.

For the second matrix, a diagnostic compiler-builtins build uses per-function
emission. Its ten remaining failures prevent a complete crate, but it emits
1,881 objects. These are archived into a **partial diagnostic archive** so the
linker can select the conversion dependency closure. Link maps and ELF symbols
verify that all four conversion entry points come from those CG-built objects.
The C compiler is the host GCC (`cc`), not Clang. The compiler-builtins source
and matching core metadata are pinned; the core dependency is LLVM-built.

The selected linkage controls again pass 4,349,964 native checks, including
independent libraries, multiple CGUs, private callbacks and executable
reachability. The wide checked-return control passes another 1,671,168 checks.

## Proof boundaries

The ordinary mandatory proof test still fails on 14 uncovered instructions
across 12 opcode kinds, first `aliased_f32_read[13]`, `AArch64::StpPreIndex`.
The four isolated new casts also fail machine-proof admission, each with six
uncovered instructions across five opcode kinds, first `StpPreIndex`.

With scalar refinement enabled, each of the four new conversion obligations
is actually submitted, then refuses with `TCG-REFINE-068`, `INCONCLUSIVE`,
`incomplete proof-trusted`. The equivalent i64/u64 conversions have the same
refinement failure with both the previous and current backend. These are
recorded failures, not successful proofs. Native matrices explicitly disable
machine certificates and Trust verification; scalar refinement is off there.

## Reproduction and identities

The pinned compiler is Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with
its matching rustc-private sysroot and LLVM SDK. The backend is copied from
the completed build to an immutable test path and checked by SHA256. Test
binaries are copied and compared with the compiler-artifact hash before use.
The source receipt extends the prior function-linkage report over base revision
`e0ac540a363e36c0f28bea7a4831aca10345c313`.

The archive retains exact commands, fixtures, compiler/source identities,
objects, native executables, link maps and raw failures. Use
`records/build.py test --test aarch64_c_fnabi_aggregate_linux --no-run --message-format=json`
with the recorded environment, then `records/runtime-qualified.py wide_int_float`.
`records/builtins-qualified.py` and `records/builtins-legacy.py` reproduce the
census; `records/runtime-builtins.py` links and runs the partial runtime probe.
`records/cast-controls.py` and `records/cast64-controls.py` retain the negative
baseline and both proof boundaries. Large rebuildable libraries, backend and
test executables are identified by hashes rather than embedded in the archive.

results.json records the results; assets.json
inventories every member of evidence.tar.gz, identified by
archive.json. Every archive member is independently rehashed.

All Linux completion rows remain open. Self-hosting and strict compile-time
and execution-time wins over LLVM and Clang remain unproved.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
