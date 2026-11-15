# Linux TC stitching fixture qualification

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The exact Trust compiler `ae9c2c1da` previously failed to compile
`e2e_tc_stitching`: the compiler gate had no matching fixtures, and the newer
projection fixture declared `aarch64-apple-darwin`. This repair supplies both
closures generated for `aarch64-unknown-linux-gnu` and selects them only for
their exact compiler and target. It leaves every existing test and negative
control enabled.

The actual run passes all seven fixture-selection tests and all five TC
stitching tests. Each test executes in its own process with exact list/start/
completion matching, no ignored test, and no failed test. Filtering selects
one named case per process; all twelve listed cases execute. The projection
tests compare error identities and successful results against native Rust,
including the deliberately corrupted error-propagation oracle; the WHNF
tests exercise cache routing, unfolding discipline and the call-argument
load regression.

Both fixtures were emitted twice with identical bytes by TrustIR
`be4018498bc33a9416c4e9ebec317b762f0d7751`, built against immutable Trust
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb` and its matching private metadata.
The projection closure has 136 members and 1,006,902 bytes; WHNF has 89 members
and 456,682 bytes. Both validate with zero errors and reparse successfully.
See the [fixture reproduction instructions](../../../crates/trust-cg-codegen/tests/fixtures/ae9-linux/README.md)
and [artifact provenance](../../../crates/trust-cg-codegen/tests/fixtures/ae9-linux/provenance.json).

The qualification base is trust-cg `463b2fc09634337d72f82b47a24a7b6ffb4c9bb5`
plus the four-file code patch and two generated fixtures. The retained result
binds all six files by SHA-256. Subsequent source edits only explain the new
fixture lane in comments and format its two `cfg` attributes; reports and
provenance files were added after the run. No tested behavior changed. The maintained whole-workspace formatting gate and
documentation check pass. The first formatting check found one attribute
layout; its failure and the successful correction are both retained.

manifest.json binds the losslessly compressed records:
the generator build, both repeated emissions, exact test runs, their runners,
the tested code patch and the preceding main-alignment receipt. It records
both compressed and original hashes. The source fixture bytes themselves
are committed under the test directory.

This is an unverified development build and a native/JIT differential result.
The other ten layout-sensitive kernel targets still refuse ae9; the earlier
full all-targets failure remains a failure. The 167-target Linux floor and
private compiler/ABI bridge have not been rerun or qualified by this result.
No G1–G8 or L01–L14 completion claim follows.

## Incoming-main integration

Merged `8297196d8f91be5edea02c13d805189ea7fe183b` into the fixture repair,
producing clean source `847fa6071c7a460d16d25299f877d0c284a42496`. The incoming
change stamps the private backend's aggregate classification and extends the
lowering refusal to indirect aggregate call signatures. No fixture or
dependency pin changed during integration.

All 23 merged-tree qualification commands passed: the lower all-targets check,
1,906 complete lower library tests, all ten `pin_move_floor` cases, both
codegen corpus tests, the CLI corpus test, seven fixture-selection tests and
five individually executed TC stitching tests. That is 1,931 test executions.
Every target was enumerated first, and every listed case started and passed;
complete-target runs had no filtered or ignored cases. The twelve fixture
tests were repeated because the incoming admission change affects their path.
The 25 added `merged-second` records retain the full logs, result and runner.
This documentation follow-up changes no tested source. The separate private
backend native ABI qualification is not included in this result.
