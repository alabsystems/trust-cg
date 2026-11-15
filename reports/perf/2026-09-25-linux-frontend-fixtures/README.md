# Exact ae9 Linux frontend fixture qualification, 2026-09-25

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

All 72 existing `e2e_frontend_roundtrip` tests pass on exact compiler
`rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)` and target
`aarch64-unknown-linux-gnu`. Each listed case ran in its own process; the
runner checked its start, successful completion and zero ignored cases.
The fixture bytes, native oracles, ABI shims and test bodies are unchanged.

The earlier codegen all-targets check stopped at this target's unsupported
compiler guard. An isolated diagnostic changed only that guard to select the
already exact `kernel_fixture_ae9_linux` predicate, then compiled and executed
all 72 cases. The measured success qualifies this existing corpus for this
specific compiler/target pair. It does not generalize compatibility to other
compiler revisions or hosts. No historical slice source was reconstructed and
no new fixture generation is claimed.

The maintained change opts this target into that exact predicate. The legacy
Rust 1.95 versus current fixture selector is unchanged; ae9 still classifies
as unsupported in that legacy selector. Individual targets explicitly choose
the Linux qualification. The seven selector tests cover exact version,
wrong version, missing/malformed identity and wrong target. One test was
renamed to describe the separate legacy selector accurately; its assertions
are unchanged.

The other ten kernel targets retain their
[regenerated-input qualification](../2026-09-25-linux-kernel-fixtures/README.md).
Together the two qualifications cover 117 integration cases and seven
selector cases. This is a case census across those targets, not a complete
compiler or proof-required acceptance result. The earlier required regression
floor retains its own source revision. The separate rustc-private ABI bridge
still lacks calling-frame proof authority for its paired save/load forms.

The broader `targo --unverified check --locked --offline -j 1 -p
trust-cg-codegen --all-targets` check passes in 812.42 seconds.
All seven selector cases pass again; the maintained formatting gate passes.

The all-targets check and renamed selector tests are recorded separately from
the 72-case run. Both bind source hashes over base
`8023b5b381c212ca070b142d07e5e6553a80c912`. Source changes between them are
limited to comments in build/selector support and a selector test name; the
qualified frontend test file is byte-identical. All builds use genuine Targo's
explicit unverified development lane and the recorded immutable toolchain.
No dependency pins or global toolchain selection were changed.

manifest.json records hashes and sizes of all 88 losslessly
compressed logs, results and runners. fixture-inputs.json
binds all 74 unchanged fixture variants and the compiler/tool identities.
Every result retains its actual scope and outcome. The original compiler-guard
failure is retained in the preceding kernel qualification report.
