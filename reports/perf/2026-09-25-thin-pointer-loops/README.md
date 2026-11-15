# Thin-pointer loop phis and O1 CFG cleanup

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Base source `776e4957ada1435dff9e8df0b705f35b7ddb6389`, with the exact modified source hashes and snapshots
retained in the qualification records, repairs two independently reproduced
lowering failures. The compiler is genuine immutable Trust `ae9c2c1da`, with
its matching private SDK. No dependency revision pin changes.

The bridge used `TrustIR::Ty::bit_width()` to identify loop-carried scalar
locals. That API intentionally has no target-independent width for pointers,
so `NonNull<T>` and raw-pointer cursor updates were refused. Pointer-shaped IR
now additionally requires a Rust layout consisting of one pointer scalar.
This excludes fat-pointer metadata pairs and modeled aggregate slot addresses;
loop completeness and back-edge value checks remain enabled.

The expanded regression then exposed an existing O1 refusal in the reachable
`*const u16::sub` helper, also reproduced with the published backend. Its
unreachable predecessor assigned the shared return carrier a different value.
The O1 pipeline now runs the existing CFG simplification pass before scheduling,
as O2/O3 already do. The register allocator and its independent value-flow
validator are unchanged. Temporary allocator tracing is retained only in the
archived diagnostic source snapshot, not the final implementation.

Final qualification passes the mandatory private bridge all-targets check,
fresh backend build, exact four-test discovery and selected pointer regression.
Seven functions cover `NonNull<u8>`, `NonNull<u64>` loads, raw-pointer writes with
variable strides, reverse `u16` reads, transparent wrappers assigned wholly or
through their field, and slices whose data pointer and length both change.
For each LLVM/CG and O0–O3 combination, a C oracle performs 8,840 checks over
17 starting offsets and 65 lengths, including zero iterations and full-buffer
sentinels: **70,720 checks across eight native executions**. The selected test
reports one pass, zero failed/ignored and three other tests filtered out.
The real compiler-supplied Rust runtime is linked and its panic control must
terminate with SIGABRT; no panic stubs or helper replacement is used.
The prior scalar-union join regression also passes again against this backend:
31,200 native bit checks over thirteen functions, LLVM/CG and O0–O3. This
checks the new O1 CFG cleanup against the previously repaired branch joins.

The new O1 machine regression fails on the original pipeline and passes after
cleanup. Final optimizer qualification runs all 52 pipeline tests and all 35
CFG-simplification tests. The initial pipeline rerun recorded 51 passes and one
stale pass-count assertion, corrected alongside the new pass. The maintained
root formatting gate passes. The private-library comparison retains its
preexisting formatting debt and requires zero new formatter edits; changed
tests and fixtures pass their complete formatting check.

The seventh full-core diagnostic repeats the entire original source and the
same LLVM control retained in the [union report](../2026-09-25-scalar-union-joins/README.md).
The failing-root count drops from 60 to 59: `core::fmt::write` is the sole removed
root, with no new failures. Full-core compilation still fails; emitted objects
are partial diagnostic output, not a whole-library success.

All native and core runs explicitly disable frontend verification and CG proof
certificates. No proof-required ABI gate, full Linux floor, self-host, release
promotion or whole-system completion is claimed. Live qualification of older
frozen revisions does not qualify these changes. The records preserve original
failures, diagnostic builds, failed qualification attempts, final positive
runs, source snapshots, compiler identities and exact commands.

Every retained tar member is bound by hash and size in `assets.json`;
`manifest.json` and `inventory.json` bind raw/compressed records.
`excluded.json` explicitly lists rebuildable backend/runtime binaries. Native
objects, executables and command transcripts remain lossless.
