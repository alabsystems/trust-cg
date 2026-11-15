# First independently replayed original output-memory certificate

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The exact original 96,284-byte conditional output-memory query now has a complete
Alethe certificate accepted by the independent frozen Clean checker. The query
bytes remain unchanged: SHA256
e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7.
Across that query, the five prior memory queries and three small common-write
fixtures, **9 original certificates are accepted and 27 corruptions rejected**.
The corruption cases replace a rule with a hole, remove the empty conclusion,
or negate the original asserted premise.

This is a partial candidate checkpoint. The proof-library build succeeds and
**16 selected test methods pass, 3 fail, none are ignored**. Both original-memory
methods pass, including native strict checking and certificate generation.
Both frontend-normalized output-memory methods still fail. The new common-write
positive method passes at widths 9, 64 and 128, while its negative method fails:
the missing-separation fixture accidentally used the same byte value for the
saved cell and output, so dropping separation did not invalidate that case.
This test failure is retained; a follow-up must give the output an independent
value, preserving the expected refusal. All six native outside-frame controls
and seven sparse-memory controls pass, including overwritten malformed values
and cancellation. Filtered unrelated tests are reported per group in the logs.

No public solver test or fresh solver CLI build ran in this candidate: the
harness stops before the DPLL build because the proof-library selection failed.
The installed solver therefore remains at its earlier timeout baseline.
This report does not claim a fully passing candidate, completed production
memory admission, an installed repair, or whole-system completion.

The candidate proves the disjoint-span and outside-frame offset theorems before
expanding reads discarded by those proofs. It validates every store, key,
value and sort, including overwritten values, then lowers the remaining source.
Identical output writes are reapplied with explicit read-over-write and
congruence derivations. Expression, work, memory and deadline limits remain in
force; source-shape recognition supplies no proof authority. The span search
now covers 64 bytes, matching the existing 64-store memory model, and accepts
the original subtraction and non-wrap guard spellings. Actual offset theorems
are still independently checked.

AY base is 441437842aff0fbfe1f44c214eeb279297137432; the exact candidate tree is
34b9a371d97dfa4256a7f173e690c629ab76cf3e. The maintained T0–T6 stock development
export is frozen with its full transformed inventory. This is not a complete
Trust-certified workspace build. Clean SHA256 is
680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc.
Build/tests use an exclusive host lease, two build jobs and a zero-grace
16 GiB RSS watchdog; independent replay uses the same lease with 8 GiB.
All 36 replay commands and their complete diagnostics are retained. Stored and
decoded artifact lengths and hashes are audited; executable identities are
retained without embedding the large test binary.

The numerical theorem remains conditional on alignment, non-wrap and private
frame separation. Caller ownership, live writable storage, ordinary Rust
frontend coverage and final-byte composition remain separate open obligations.
All L01–L14 complete-system rows remain open.
