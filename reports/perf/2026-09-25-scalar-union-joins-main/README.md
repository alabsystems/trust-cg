# Scalar union repair after incoming main integration

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Clean merge source `0be78896de7d681effc0bb02071587abd4dc7a2b` combines union repair `8bcbde3b6`
with incoming main `a25a4bbc332bab7876d79cf4c8002dde6cc9eb51`.
The incoming changes type diagnostics by their producing layer and withdraw
registry-name and statistical proof credit. They also add bridge test-only
dependencies and proof/refinement regression controls; no dependency revision
pin moved. The original repair qualification remains archived separately in
[the original report](../2026-09-25-scalar-union-joins/README.md).

The maintained root format gate passes on the merge.
The clean merged source passes the private bridge all-targets check, fresh
backend build, three-test discovery and selected union regression. All thirteen
functions pass 31,200 native bit checks across LLVM/CG and O0–O3. The selected
test reports one pass, zero failed/ignored and two other tests filtered out.
The compiler is genuine immutable Trust `ae9c2c1da`, with matching private SDK;
the backend is bound to its exact bytes before and after the tests.

The fifth full-core diagnostic uses the same entire original source and LLVM
control retained in the original report, then compiles with this merged
backend. It still reports sixty failed roots, without the repaired
`select_unpredictable<MaybeUninit<usize>>` mismatch. The complete current
diagnostics and emitted objects are retained, without treating partial object
emission as a whole-library pass.

Both native and core runs explicitly disable frontend verification and
codegen proof certificates. No proof-required gate, full Linux floor, self-host
or whole-system completion is claimed. Ongoing qualification of earlier frozen
revisions does not qualify this merge. The original report retains the
reproducer failures, formatting comparison and source/LLVM control; this
supplement binds the new measurement rather than relabeling those old results.

Every retained tar member is hash/size bound in `assets.json`, and compressed
and raw record hashes are in `manifest.json` and `inventory.json`.
`excluded.json` identifies rebuildable backend/runtime archives; all generated
native objects, executables and command logs remain lossless.

The publication preflight caught a stale generated diagnostic census and an
obsolete link-integrity code citation inherited from incoming main. The table
now names the actual MIR-lowering code, and the maintained generator refreshes
the census. This documentation correction changes no compiler behavior. The
failed preflight log and result are retained alongside the successful compiler
qualification.
