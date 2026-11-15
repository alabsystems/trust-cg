# Original output-memory proof expansion failure

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The required original conditional memory theorem still fails on current AY main.
The guarded native diagnostic build succeeds; **0/2 required positive tests pass**,
with no ignored tests and 8,693 unrelated tests filtered. The failures are retained
as failures. No compiler or solver installation changes in this campaign.

Source authentication, elaboration, faithful raw interning and printer round-trip
all succeed. They take about 380 ms together. The strict native checker then
refuses the proposed original-source refutation: "lowered BvExpr exceeds 4096 nodes".
The whole stage test reaches this refusal in 386 ms. The separate public-API test
returns unknown at the original 30-second deadline rather than producing the
required UNSAT certificate. The two tests take 30.50 seconds together.

This locates an expression-expansion limit before the solver's eventual timeout.
It is not evidence of a false theorem, nor permission to accept an unchecked
refutation or increase the query's limits. No complete certificate is available,
so independent Clean replay is not attempted.

The 96,284-byte query is unchanged from the [Linux baseline](../2026-09-17-output-memory-linux-baseline/README.md),
SHA256 e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7.
AY base is 441437842aff0fbfe1f44c214eeb279297137432; the staged diagnostic
source tree is 6f48c7443ac9a7485d9ec989363197d6e52c292a. Only two tests,
their module registration and the exact original fixture are added. This is the
maintained T0–T6 stock-Rust development export, not a complete Trust-certified
AY workspace build. The source and transformed file inventories are retained.

The build uses Cargo/Rust 1.97.1, two jobs, an exclusive host resource lease and
a zero-grace 16 GiB RSS watchdog. It takes 369.01 seconds. Tests additionally set
an 8 GiB executor memory limit; the query retains its 30,000 ms timeout. No limit
or proof authority is relaxed. The frozen test executable is 240,281,280 bytes,
SHA256 48495b725bfafbd5e93a37bf6e031985e029aecee3057f986fb6c7b4c86108da;
its original local path is in the result manifest, while its large binary is not
embedded in this source archive. Every stored artifact is audited in compressed
and decoded form.

Ordinary Rust output-buffer compilation remains separately refused at O0–O3.
Caller ownership, writable live storage, final-byte composition and production
memory admission remain open, as do all L01–L14 complete-system requirements.
