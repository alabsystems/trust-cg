# 128-bit loop validation — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The loop validator now models i128/u128 arithmetic, constants and complements
without discarding the high 64 bits. Source checked arithmetic uses exact
carry, sign and guarded division identities; the implementation model follows
the ordinary operations emitted by the bridge. The two sides share constant
representation, not checked-arithmetic results. Canonical unsigned constants
above `i128::MAX` are modeled explicitly. Both ordinary operation refinement
and loop refinement now model a 128-bit complement correctly. Wide wrapping
add/sub/mul calls lower directly at O0; the existing constant-division and
remainder admission boundary remains at 64 bits.

The native corpus passes **344,064 checks** in eight LLVM/trust-cg executions
at O0–O3, using `panic=abort`. It covers exponentiation by squaring with normal
and early exits, signed and unsigned overflowing updates, signed multiplication,
rotation of loop-carried values, high-bit constants, a 128-bit switch and
complements. A full 256-bit product built from 32-bit limbs supplies the
multiplication oracle, with repeated multiplication for exponentiation.
Carry/borrow across 64-bit limbs and signed bounds supply the other overflow
oracles. All eight corpus functions require an observed semantic back-edge
validation success at O0.

The prior backend refuses all eight roots of this same final corpus; LLVM
accepts it. The frozen full-core diagnostic drops from **three to two failing
roots**. Only u128 `overflowing_pow` disappears. The two remaining diagnostics
are byte-for-byte unchanged: `TwoWaySearcher::maximal_suffix` still needs a
model for its slice access and branching, and `Request::fmt` still needs support
for a struct ending in a dynamically aligned trait object. Both core runs exit
1 and retain 44 partial objects. This is not a complete core or self-host build.

Qualification on the final backend:

| Check | Result |
| --- | --- |
| New native regression | Passed, 344,064 checks at O0–O3 |
| New model tests | 3 passed, including 7,320 signed/unsigned arithmetic comparisons, both complement models and high-bit switch mutations |
| Existing triangle and anti-swap integration tests | 10 passed |
| Selected loop-model unit tests | Harness reports 26 passed; 8 return early without Z3, so 18 actually execute |
| Aggregate captures, scalar-cell returns, closure wrappers, overflow loops, caller locations and carrying multiplication | 6 native regressions passed |
| Overflow-loop refusal controls | Passed |
| Mandatory ABI proof admission | Failed with `TCG-PROOF-465`: 14 uncovered instructions across 12 opcode kinds; first `StpPreIndex` |
| Bridge all-targets, formatting, diff and documentation checks | Passed |

The full control invocation reports 7 passed and 1 failed, with no ignored tests.
The eight Z3 early returns receive no proof credit. The final corpus uses
arm-local checked tuples, within the existing branch model; tuples escaping a
branch join and other unsupported paths have not been newly admitted.

The backend SHA-256 is
`7a4b6fb03a2c7ef1730bbd6a3f7d821cb1ac2987746dd8ddcaed12b743b3126c`.
It was built with Trust-authored `trustc` 1.99.0-dev,
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, using LLVM 22.1.2 for this
development bootstrap. The base checkout is
`e0ac540a363e36c0f28bea7a4831aca10345c313` plus the archived changes.
The previous backend is identified in the
[caller-location report](../2026-09-27-track-caller/README.md).
All 721 frozen core files were rehashed and matched their manifest.

results.json records the final outcomes.
evidence.tar.gz contains 1,251 files: source snapshots,
patches, commands, logs, all frozen core sources, the primary native executables
and libraries, and both censuses' partial core objects. Large rebuildable
backend libraries and other control executables are recorded by hash.
assets.json hashes every tar member; each member was independently
rehashed after archiving. The stored archive SHA-256 is
`31c1fe1357c118e5b8514c88bf7ca5e013e4efa1d85b00f83291dedfa12a6064`.
inventory.json includes stored and decoded archive identities.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-wide-loop-threading
```

Trust/Targo verification is disabled in this development lane, and native
codegen uses `no-proof-certs`. Native correctness and loop refinement do not
establish complete machine proofs. No qualifying performance comparison was
made. Linux completion, mandatory proof admission, and compile/runtime
dominance over LLVM and Clang remain open.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
