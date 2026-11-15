# Canonical runtime bounds assertions — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Rust bridge now lowers a trapping MIR bounds assertion using its original
Boolean condition, followed by the original success edge. It no longer rebuilds
the index from inferred ranges or publishes `Discharged`/`ProofRef` claims from
an AY Boolean verdict without transporting the required certificate and site.
The obsolete constant, dominance and narrow-index producer paths are removed.
Bounds checks with an observable unwind/cleanup edge retain their panic path.

The adapter recognizes an adjacent, single-use 64-bit unsigned comparison and
assertion against a preceding typed constant. It emits the equivalent runtime
bounds guard, with no obligation or discharge authority. Other widths, predicates,
consumers, nonconstant/oversized bounds, duplicate definitions, comparison debug
spans and proof metadata prevent fusion. This change
retains checks; it does not authorize eliminating them.

## Qualification

- **278 adapter tests** pass, including six new groups covering the fusion's
  constraints, malformed SSA, additional consumers and metadata.
- **Two frontend fixture tests** pass. All ten actual panic-abort O0/O1 captures
  validate with canonical TrustIR and contain no synthetic bounds claims.
  The O0 writer now has five comparisons consumed by five assertions. The two
  unwind captures retain the conditional failure edge and panic call. They still
  have three exact `ConstTypeMismatch` errors for panic-message aggregates
  declared as `Ptr`; the test preserves those refusals and does not call these
  two modules well-formed.
- The native canonical-IR regression passes at **O0–O3**, producing sixteen
  AArch64 objects across bounds 0, 8, 4096 and `i32::MAX`. **36 valid calls**
  return/store the index. **80 invalid calls** trap with SIGTRAP before changing
  shared memory, including high-bit and 32-bit truncation controls. This test
  explicitly disables proof promotion; it establishes bounded execution behavior.
- The same native oracle accepts one independent assembly control and rejects
  five mutations: missing check, W-width comparison, store before check,
  missing store and an off-by-one comparison.
- All **twelve guard-authority regressions** and **53 source-bound frame tests**
  pass. Public proof statuses continue to supply no guard-deletion authority.

The complete target `canonical_bounds_assert_linux` is added to the maintained
Linux gate denominator. This focused qualification is not a new full Linux gate
run. Historical results are not added together into a completion verdict.

## Actual compiler endpoints

The genuine Trust-pinned private backend builds with the explicit unverified
frontend lane. Its diagnostic capture and normal uninstrumented rebuild agree
on all twelve compilation outcomes and produce byte-identical objects for the
admitted cases. Backend proof enforcement remains enabled.

The constant-index O1 program and five-word O1 writer compile successfully.
Each passes **257 fresh native calls** checking all sixteen arena words,
eight buffer placements, callee-saved registers and SP. Ten cases still refuse
proof promotion. The O0 writer's CSet failures are resolved; its remaining
uncovered instructions are `StpPreIndex` and `LdpPostIndex`. Dominated and
unwinding control flow still exposes a CSet coverage gap. No refused case is
credited as a successful required program, and the installed package is unchanged.

## Failed attempts and evidence boundary

The first private build failed because comment cleanup accidentally removed two
helper definitions; the corrected intermediate capture passed. The final design
then removed that eligibility machinery entirely and passed a fresh third capture.
The final root qualification initially found a wrong test import, then an absent
JSON test dependency (the test was moved to the existing verifier test package),
and then the three panic-global validation errors described above. All failed
attempts are retained separately; only the final successful run receives credit.

Records retain exact commands, input hashes, captured original modules, runtime
objects/oracles, complete logs, guard results and tool identities. The temporary
capture instrumentation was removed. Heavy commands ran serially with an anchored
16 GiB process-group RSS ceiling, zero grace and two Cargo jobs. No successful
qualification breached the ceiling or truncated its output. Large compiler/test
binaries are identified by hash rather than duplicated in the archive.

This is a frontend well-formedness and runtime-check repair, not a proof of MIR
translation, reference validity, the full ABI, memory ownership, native execution
or publication. All L01–L14 remain open. Reproduce the retained tests with the
pinned toolchains and the commands in `records/`; the harnesses also record their
original machine-local paths. Check retained bytes with:

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-canonical-bounds-assertions
```
