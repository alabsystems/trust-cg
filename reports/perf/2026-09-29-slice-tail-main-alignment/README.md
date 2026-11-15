# Linux AArch64: slice-tail fix reconciled with remote main

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The slice-tail from-end repair and its [paired std census](../2026-09-29-slice-tail-from-end/README.md)
are retained while merging remote main through `69bae79aa` as `02c8fca4c`.
The generated inventory was the only merge conflict; it was regenerated from
the combined source. No source change was needed for the merge.

## Incoming compiler changes

The coordinated dependency update moves TrustIR from `7917c172...` to
`8e81e98aa92d78934548ec435218ce530294f2c5`. The retained source diff changes
manifest evidence and its tests plus the refusal corpus; it does not change
the interpreter, instruction/type definitions or ABI classification. The four
unsigned byte-vector comparison cells and their consumer expectations adopt
the upstream measured evidence; this run checks query bindings, not fresh
external certificate replay. Clean and AY revisions are unchanged.

Incoming x86 work tracks exchange/CAS secondary writes and register-width
aliases in LICM, shares conservative may-definition accounting with peephole,
and adds an optional CSE relaxation across plain loads. The new CSE option is
off by default. The opcode-inventory environment fallback now treats `0` as
off, preserving installed option precedence. This Linux AArch64 run qualifies
host optimizer behavior; it does not claim native x86 execution or a speedup.

## Frozen compiler and native qualification

The merged backend is built from `02c8fca4c`, SHA-256
`ad7549be00258ad24d4c10c6badfb34ec0dcf1be165bfe6db1199cd8cffcd9ea`.
Its source head, patch, complete source hashes, build transcript and artifact
receipt are attached. The permanent native harness is unchanged from the
preceding report, SHA-256
`053126d865d52c1cb16819879d2fca2c7371e564df15e31ffb35f498a70e9cc0`.

The five native groups pass **72 executions, 9,622,400 checks, 9,216 caught
panics and six named refusals**. They cover the new from-end tests, existing
slice-tail, dynamic Fn arguments, borrowed slices and dynamic-tail cases.
LLVM/CG comparisons span O0–O3 and abort/unwind policies. Counts exclude
support setup and exploratory runs. Full transcripts retain backend hashes.

Strict expanded-corpus runs at O0/O2 pass: 10/9 functions, 14/14 refinements,
nine/nine memo hits, zero skipped obligations and zero unmodeled shapes.
Proof-required runs retain the exact `TCG-PROOF-465` refusal at both levels.
Native behavior and strict bridge refinement are not complete machine proofs.

## Dependency and integration checks

The first merge passes **468 root test executions** (466 distinct names;
two CSE safety negatives also run with the new opt-in enabled). Selections
include 240 peephole, 59 LICM, 74 effect, 31 default CSE, one option-policy,
five diagnostic, 13 UB-map, two comparison-cell, 15 construct-inventory,
one vector-admission, four native AArch64 word-binding, two codegen refusal,
one actual CLI refusal, 13 CLI proof-export and five dependency-authority
tests. The two opt-in executions add to those counts. The bridge's 26 option
tests also pass. No empty selection is included.

The corrected Python invocation passes **110 tests**: 66 dependency-updater
regressions and 44 census/Darwin-inventory checks. Its first invocation ran the
44 latter tests but failed to import the updater module because `scripts` was
not on its Python path. Both complete logs are retained; only the corrected
invocation counts as qualification. These inventory checks are not execution
of the full Darwin native campaign.

The first UB-map selection targeted the library rather than its integration
test and selected zero tests. That log is retained and contributes no credit;
the separate integration run below supplies the actual UB-map qualification.
Documentation, diagnostic inventories and the dependency tuple check pass.

## Standard library and remaining work

A complete O2 std census against the first merged backend still has **216
failing roots**, with every remaining diagnostic byte-identical to the
pre-merge fixed-backend census. It exits with compiler failure after
732.512s without timing out. Commands match after normalizing backend
and output directory; recorded environments and working directories match.
The same LLVM-built dependencies are used. This is a diagnostic census, not a
performance benchmark. The latest completed O0 census remains 197 failures.
The subsequent x86 proof merge below does not receive a separate std census.

The preceding mixed CG-core/alloc plus LLVM-remainder runtime build is bound
to its original backend; it is not claimed as a new mixed-library execution
against this artifact. Full CG std, self-hosting, complete machine proofs and
compile/runtime speed superiority over LLVM/clang remain open.

`assets.json` binds all attachments. The previous milestone's report remains
immutable; this supplement records qualification of the newly merged source.

## Subsequent remote proof merge

Remote main then advanced to `db6c150ee`, merged as `06a692725`. The only
conflicts were generated inventories, which were regenerated. This brings the
x86 source-bound memory theorem and its width, aliasing and ordering negatives,
a diagnostic dump option, a target-specific test helper guard and shell host
probe fix. The shared path-consensus item block moved unchanged (6,278 bytes,
checked against both Git versions); the AArch64 affine helper's visibility and
FP comparison spelling changed without altering their stated behavior.

The final frozen backend is SHA-256
`d80d589edc79d72302ba1ab5102da9cacb63b345dbc787769bba695930dd7025`, built from
`06a692725`. It repeats all five native groups successfully: another 72
executions, 9,622,400 checks, 9,216 caught panics and six named refusals. Strict
O0/O2 bridge counts and the `TCG-PROOF-465` refusals are unchanged. The two
merged-backend runs in this supplement total 144 native executions and
19,244,800 checks.

Selected final-source root checks total **179 passed, four failed and one
ignored**. Passing groups include 52 x86 function-verifier, ten FP lowering,
five AArch64 affine-value, six diagnostic and all 13 soundness-manifest checks.
The other passes and all four proof-qualification failures are detailed below.

The x86 body group reports 59 passed, three failed and one ignored fixture
printer. Two failures reproduce on the frozen pre-merge verifier: its current
AY/Clean pair certifies `AshrImm` and `AshrI8Imm`, while the recorded gap list
expects both to remain uncertified. That changes the expected certified set
and per-row credit counts; it is not a counterexample to either shift.
The new memory host-qualification test rejects the different pinned checker
identity. Its outcomes are retained; the failed host qualification is not
represented as a passing upstream proof campaign.

The loop symbolic-execution group reports 34 passed and one failed. The same
Euclid rotation test fails on the frozen pre-merge verifier with the same
`incomplete self-check-rejected` inconclusive result. These three measured
before/after failures and the new checker-identity refusal remain explicit.
No expected proof outcomes, checker identities or production gates were weakened.

Two attempts to select the affine helper by its file name selected no tests.
The actual module path (`aarch64_affine_lowering::scalar_values`) passes all
five tests. Empty selections contribute no credit. Source manifests confirm
all 3,283 recorded compiler-input files remained unchanged through qualification.
