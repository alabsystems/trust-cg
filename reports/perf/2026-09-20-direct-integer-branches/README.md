# Direct integer comparison branches — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Adjacent integer comparisons whose only consumer is the following conditional
branch now select CMP/B.cond directly at every optimization level. The actual
Rust `if index < 8 { output[index] = value; }` reproducer therefore compiles at
O0/O1 with backend proof checks enabled. It previously failed on the intermediate
CSet generated solely to materialize and immediately consume a boolean.

Selection requires a complete function-use inventory, a single definition,
exact operand/result shapes, matching known I8/I16/I32/I64 operand types and
unclaimed adjacent source instructions. Each emitted comparison and branch
retains its own original source identity and lowering digest. The comparison
helper preserves narrow sign/zero extension and the existing exact immediate
rules. Escaping booleans and unknown, malformed, wider, floating, nonadjacent or
already claimed shapes keep the existing selection path. Generic CSet proof
mapping, frame policy and verifier authority are unchanged.

## Qualification

The four new selector test groups, 964 existing selector tests, 979 pipeline
tests and native predicate matrix pass with no ignored tests. The native test
executes 125,760 calls across O0–O3: ten signed/unsigned/equality predicates at
four widths, boundary and deterministic random values, noncanonical narrow high
bits, independent C comparisons and conditional-write canaries. Separate source
identities, exact comparison operands and branch successors are checked by the
selector tests. The native target is registered in the required Linux gate,
which now lists 124 target families; this is not a new full-floor result.

The uninstrumented genuine Trust backend builds, and the actual Rust corpus
has sixteen admitted O0/O1 cases and two explicit unwind refusals (both now only missing STP/LDP frame mappings). Ten
writer/bounds cases execute 2,570 ABI-wrapped calls with sixteen-word arenas and
eight buffer placements. The newly admitted dominated cases exercise both
writing and non-writing paths, including very large out-of-range indices.
The separate dynamic-bound cases retain eight trap-before-store controls.
Six reference/static cases retain their C value, bit-pattern, alignment,
allocation-identity and relocation checks, including 7,200 address calls with
SP/X19–X29/D8–D15 checks and exact ELF function/CFI inspection.

The 53 source-bound frame/diamond regressions also pass, for 2,001 distinct
Rust tests. The Linux gate suite passes 31 tests and skips one non-Linux-host
control; its intentionally failing fixture output is retained. Those results
are recorded in `records/cg-direct-branch-tests-third`. Root formatting and source/HEAD stability
checks pass. Full commands, results, resource envelopes, original inputs,
objects, native drivers and source fingerprints are retained here. Heavy jobs
ran serially with a 16 GiB anchored process-group RSS ceiling, zero grace, two
Cargo jobs and one test thread. Large backend/tool binaries are hash identified.

## Remaining obligations

This is a lowering repair and native qualification, not a new whole-source
proof. Existing default CMP citations are coarse; typed flag/branch proof
binding and composition to final native memory effects remain separate work.
The frontend runs explicitly unverified, while backend checks stay enabled.
Unwind frame proofs, general CSet, broader unsupported domains and L01–L14
completion obligations remain open. This source report does not claim an
installed update, self-hosting or a signed release.

```sh
cargo test --locked -p trust-cg-lower --lib isel::branch_compare:: -- --test-threads=1
cargo test --locked -p trust-cg-codegen --test aarch64_direct_cmp_branch -- --nocapture --test-threads=1
cargo test --locked -p trust-cg-codegen --lib pipeline:: -- --test-threads=1
python3 -m unittest scripts.tests.test_linux_aarch64_gate
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-direct-integer-branches
```

Private frontend/native reproduction requires the sealed toolchain and helper
identities recorded in the retained preflight; the harnesses preserve original
machine paths. Results apply to this candidate and host.
