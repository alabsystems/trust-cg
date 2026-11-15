# Linux AArch64 integration with main, 2026-09-29

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Linux AArch64 compiler work is committed and merged with upstream main.
Local main, remote main and the working branch were verified at
`ed777a6dfaf7883474dc242245c85bb1a674c7bc` after a normal atomic fast-forward push.
The first push raced an upstream report commit; that commit was merged before
retrying. No remote history was replaced.

## Repairs

The integration preserves upstream crate-identity checks and indirect argument
planning while retaining the Linux AArch64 storage, pointer, drop and unwind
paths. It reconciles dynamic-tail metadata, wide-pointer carrier layouts and
caller-location arguments. A now-supported union tuple is covered by a positive
native oracle. Nested splat constants retain private symbol renaming.

Loop joins use upstream's CFG triangle classification. The 128-bit multiply
threading model now matches the canonical overflow instruction; composed wide
add/sub retain concrete flag expressions. Mutation tests reject a wrong opcode,
wrong operand and stale flag. Multi-input sampling reuses the bounded carrier
edge cases, fixing a shift-overflow crash for 128-bit inputs.

## Measured validation

The frozen backend is
`a14faffaea193f0ae7e1c1b47617d55841ef4d1f4f09da36d589316285332d1b`.
Nine native test groups pass (11 tests): **47,515,808 counted checks across
96 executions**, plus the private-function-linkage test. These include pointer
byte images, wide overflow returns and pair arguments, dynamic tails, projected
aggregates, virtual caller locations, aggregate-return cleanup, and termination
pads. Termination checks include 80 required aborts and four expected refusals;
the projected aggregate suite retains three named refusals.

Core at O0 completes successfully. Core at O2 completes with **seven unsupported
functions**, down from the pre-integration census of eleven. Its 373.9-second
run does not time out; the earlier 360-second attempt had timed out and is not
counted as a successful census. The remaining functions concern scalar-union
storage, borrowed iterator storage, and formatted network-address references.

All four wide-loop tests, the multi-input sampler regression, three array
lowering tests, and the coverage disclosure test pass. The loop-symbolic suite
passes 34 of 35 tests: Euclid rotation remains inconclusive because AY reports
`incomplete self-check-rejected`. This assertion remains strict; it was not
changed into a skip or success.

The later MIR-semantics run passes 100 of 105 tests. Three signed-division or
remainder obligations retain the same solver self-check refusal. Two fake-solver
sequence tests initially assumed a single query per obligation; the new array
lowering tries an array-free query before the exact query. Their fixtures now
place the first obligation's hole on both forms, pin both forms, and retain the
requirement to surface later rejections and counterexamples. Both updated tests
pass; no solver assertion was relaxed.

## Provenance and limits

The frozen backend's exact source hashes are in `merged-source-3.json`; it was
built after the integration of upstream `29b42282c` and the overflow-threading
repair, before the sampler repair and the subsequent array-query change.
The later verifier binary (SHA-256
`55cdd188a19017c7a72ff2189489190ad01735a3b4357438be057f31cf31c6ad`)
checks the sampler repair and merged upstream array-query change. Native tests
used the separately frozen test executable identified by its receipt. Their
results are not a claim that every later revision was rerun with that backend.

Builds use the Trust-authored ae9c2c1d toolchain on Linux AArch64. Native fixtures
select diagnostic `no-proof-certs` code generation. Passing those executions is
runtime evidence, not machine-code certification. Proof tests use the existing
private cache; the default group-writable cache was refused by AY identity
admission. The cache refusal was not bypassed.

Included logs and receipts are thin evidence. Full binaries, compiler outputs
and runtime artifact directories remain local under
`target/main-alignment-20260929/`; they are not independently published here.
Full Linux completion, complete machine proof, and strict compile-time and
runtime wins over LLVM and Clang remain open. Scalar-union work resumed after
this synchronized checkpoint and is not included in its validation.
