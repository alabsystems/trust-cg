# Unconditional loop-path validation — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The frozen Linux AArch64 core diagnostic build now exits **0 with no failing
roots**. The previous backend exits 1 with the single `TwoWaySearcher::maximal_suffix`
threading refusal. Both runs retain 44 objects; all final objects were checked
as ELF64 little-endian AArch64 relocatables. The formerly refused function is
present as a defined function with 928 bytes of code.

The new fallback proves a stronger, unconditional scalar-threading equation:
every source path to a particular back-edge must produce the same expressions
over loop-header scalars, and every emitted-IR path must independently agree.
Those two results then pass the existing refinement check. It adds no branch
assumptions and includes infeasible paths. Reads and supported pure slice
lookups may be abstracted only when their unknown values cannot affect the
threaded results. Source and implementation unknowns are never equated.
Memory forwarding is disabled in this emitted-IR walk. Typed uses may supply
an unknown producer's width; that value remains explicitly opaque. The
existing interpreter retains its earlier immediate-refusal behavior.

This resolves the scalar updates in `maximal_suffix` without claiming to prove
its reads or branch predicates. Source locals whose addresses are taken remain
outside the fallback. It also refuses projected writes, unsupported calls,
path disagreement, residual unknowns, nested cycles and traversal-budget
exhaustion. Each side allows at most 256 completed paths, depth 128 and 4,096
visits. Bindings must name distinct, width-matched header parameters. Existing
refutation verdicts are preserved; the fallback is reached only when source
model construction fails. Disabling diamond modeling also disables it.
Wrapping-call recognition now requires a core/std associated method, so a
user function named `wrapping_add` cannot acquire intrinsic semantics.

The native fixture passes **239,440 tuple comparisons** in eight LLVM/trust-cg
executions at O0–O3 with `panic=abort`. The independent oracle compares whole
suffixes, then searches naively for the suffix's least period. Each execution
checks both byte orderings for every string of length 0–8 over a three-byte
alphabet, 4,096 generated strings, and 1,028 constant, ascending and alternating
patterns. The CG O0 run must record semantic threading proofs for the function.
The previous backend rejects this same fixture; LLVM accepts it.

Qualification on the final backend:

| Check | Result |
| --- | --- |
| Suffix-search native regression | Passed, 239,440 comparisons at O0–O3 |
| Maintained refusal controls | LLVM accepts and CG refuses all 3: disabled modeling, read-dependent threaded values, and a shadow wrapping function |
| Additional source-path disagreement probe | LLVM accepts; CG refuses because source paths produce different threaded values |
| New verifier mutation/boundary tests | 8 passed; wrong common values, one wrong edge, opaque results, cycles, incomplete/aliased/invalid bindings, typed unknowns and traversal limits |
| Existing triangle, anti-swap and wide-loop model tests | 13 passed; no skipped tests |
| Closure wrappers, trait-object tails, overflow loops, thin-pointer loops, caller locations and wide loops | 6 native regressions passed |
| Existing overflow-loop refusal controls | Passed |
| Mandatory ABI proof admission | Failed with `TCG-PROOF-465`: 14 uncovered instructions across 12 opcode kinds; first `StpPreIndex` |
| Bridge all-targets, formatting, diff and documentation checks | Passed |

The new native/refusal invocation reports 2 passed and 0 failed. The selected
control invocation reports 7 passed and 1 failed, with no ignored tests. The
model invocation reports 21 passed, with no skipped or ignored tests.

The backend SHA-256 is
`20f0c33513ec4396574d8f501e79e563cfcc002aaa8989303fe4725c6dfe8aa1`.
It was built with Trust-authored `trustc` 1.99.0-dev,
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, using LLVM 22.1.2 for this
development bootstrap. The base checkout is
`e0ac540a363e36c0f28bea7a4831aca10345c313` plus the archived changes.
The previous backend is identified in the
[trait-object-tail report](../2026-09-27-dyn-tail/README.md).
All 721 frozen core files were rehashed and matched their manifest.

results.json records the outcomes.
evidence.tar.gz contains source snapshots, patches, commands,
logs, all frozen core sources, the primary native executables/libraries, and
both core runs' objects. Large rebuildable backend libraries and other control
executables are recorded by hash. assets.json hashes every tar
member; each was independently rehashed after archiving.
archive.json records the stored archive identity and member
count. inventory.json includes stored and decoded identities.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-maximal-suffix
```

This is a successful frozen-core **diagnostic object build**, not a sysroot or
compiler rebuild. Trust/Targo verification is disabled in this development
lane, and native codegen uses `no-proof-certs`. Neither the native comparisons
nor the bounded threading proof establishes the complete source-to-machine
proof chain. Linux completion, mandatory proof admission, self-hosting, and
compile/runtime dominance over LLVM and Clang remain open. No qualifying
performance comparison was made.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
