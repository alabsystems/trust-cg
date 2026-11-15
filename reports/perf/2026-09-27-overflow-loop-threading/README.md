# Overflow loop threading — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Linux AArch64 bridge's loop back-edge model now handles core's inherent
`overflowing_add/sub/mul` calls up to 64 bits, their tuple field reads inside
branches, empty branch arms, and an arm with one continuing path after a
conditional exit. It checks the source MIR against symbolic execution of the
emitted TrustIR. A conditional exit adds no assumptions: the value equality
must hold even on inputs that would leave the loop there. Nested branching
arms and nested back-edges still fail closed.

Packed overflow fields project the known `flag :: value` concatenation
directly. Flags retain the existing uninterpreted-function model, which checks
threading but does not prove the arithmetic flag implementation. A local
equality rule also checks `unsigned x / 2^k == x >> k`, with identical input
trees, equal widths, a representable nonzero power-of-two divisor, and the
exact shift count. Signed division, arithmetic shifts, wrong operands/counts
and mismatched widths cannot use that rule. The existing structural-lane
kill switch disables it. No sampled equality is promoted to a proof.

The frozen full-core diagnostic build has **four failing roots, down from
five** after the [scalar-return repair](../2026-09-27-scalar-cell-returns/README.md).
Only u64 `overflowing_pow` disappears. Remaining roots are `Location::caller`,
u128 `overflowing_pow`, `TwoWaySearcher::maximal_suffix` and `Request::fmt`.
This remains a partial build, not a complete core or self-hosted compiler.

The intermediate evidence retains the original out-of-model refusals, a
solver `unknown` for division versus shift, and the second exponentiation
loop's conditional-exit refusal. The full-core experiment with a private
solver cache exceeded its 180-second process deadline; it is not counted as
a successful build. The final census uses the original diagnostic environment.

The maintained native corpus covers exponentiation by squaring, its early
return form, conditional scalar rotation, and alternating overflowing add/sub.
LLVM-built drivers compare both backends with independent calculations. All
eight executions at O0–O3 pass, totaling **131,072 checks**. Before the repair,
LLVM accepts this corpus and trust-cg refuses all four roots. Two negative
controls remain refused by trust-cg and accepted by LLVM: disabling diamond
modeling, and a user trait method named `overflowing_add` with different
semantics. The native harness also requires all four functions to reach the
semantic back-edge check at O0.

Qualification on the final source and backend:

| Check | Result |
| --- | --- |
| New native and refusal regressions | 2 passed |
| New model tests: empty edges, boolean/integer exits, overflow fields and mutations | 3 passed |
| Existing SSA anti-swap controls | 7 passed |
| Focused model unit suite | Harness reports 26 passed; 8 returned early because Z3 was unavailable, leaving 18 executed without that skip |
| Earlier aggregate-capture and scalar-return native regressions | 2 passed; 327,680 and 589,824 checks respectively |
| Mandatory ABI proof admission | Failed with `TCG-PROOF-465`: 14 uncovered instructions across 12 opcode kinds, first `StpPreIndex` |
| Bridge all-targets check, changed-file formatting, diff and documentation checks | Passed |

The division rule's unit checks cover all 2,080 valid width/shift pairs,
exhaustive values through 8 bits, wider boundary values and invalid mutations.
These checks support the implementation; they are not the justification for
admitting sampled equalities. The rule admits only the exact bit-vector identity
described above. Existing solver tests that returned early receive no proof
credit. The old negative diamond fixture represented a now-supported empty
arm; it was replaced with a branch that actually takes a nested back-edge.

The archive retains unsuccessful intermediate runs, including the O1 integer
exit refusal before its model was added, a refusal test with the wrong expected
diagnostic text, and the initial Switch test missing a required TrustIR field.
Final qualification uses the corrected source. Both core censuses emit 44
partial objects and exit 1; the four remaining root diagnostics are unchanged.

The backend SHA-256 is
`c9d3aaac504d148b93372adf7df9c2ab7167d8d3361165d10d63e27d31f44159`.
It was built with Trust-authored `trustc` 1.99.0-dev,
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, using LLVM 22.1.2 for this
development bootstrap. The base checkout is
`e0ac540a363e36c0f28bea7a4831aca10345c313` plus the archived source changes.
The frozen core manifest's 721 files were rehashed and all matched.

results.json records the complete final outcomes.
evidence.tar.gz contains 2,489 files: exact source snapshots,
incremental and working-tree patches, commands and logs, all frozen core
sources, primary native executables/objects and partial core objects.
assets.json hashes every tar member; each was independently
rehashed after archiving. Large rebuildable backend libraries and other control
executables are represented by their hashes. The archive's stored SHA-256 is
`43e6deda5a8889a4f3c09d188cf945365e29681f3184605ded99431be553c1fc`.
inventory.json also records its stored and decoded identities.
Verify the archive directory with:

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-overflow-loop-threading
```

Trust/Targo verification is explicitly disabled in this development lane,
and native diagnostic codegen uses `no-proof-certs`. Semantic threading
acceptance provides no complete source-to-machine proof credit. Linux
completion, mandatory instruction proofs, and compile/runtime dominance over
LLVM and Clang remain open. No qualifying performance comparison was made.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
