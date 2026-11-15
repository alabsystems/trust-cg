# Linux regression floor after original-module receipts and source-frame repair

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Result: **PASS**, **127 required target families passed**,
**0 failed**, **692 Rust tests passed** on clean source
`9b2f7a7235a34e19fe6acc4ef4fb33416cda6943` with stock Rust 1.97.1 on the Linux AArch64 machine.

This executes the complete 127-family inventory in the maintained
`scripts/check_linux_aarch64.py`, after the original-module receipt and source-frame repair in `b488c3cc1`. The original classifier, target-specific
verifier environment exclusions, locked offline Cargo resolution, native
targets and negative controls are unchanged. The external anchored supervisor
runs each target serially with a 16 GiB process-group RSS cap, zero grace, two
Cargo jobs and one Rust test thread. Every command has a 1200-second deadline;
resource failure, skipped execution, filtered tests or incomplete output fail
the run. Tool and dependency identities and the source fingerprint are checked
before and after. Per-target logs, counts, exact commands, executable hashes,
guard evidence and the harness/gate sources are retained.

This is current-source root-workspace regression evidence. The installed
compiler package remains the previous qualified 884b cohort. Both complete conditional callback models now have independently checked external certificates, but native construction and compiler source/byte integration are still unfinished. The rustc-private bridge therefore retains its scalar calling-frame refusal. The separate [64-test targeted qualification](../2026-09-20-original-module-receipts/README.md) exercises original-module cache identity and restores source-bound constant/copy/conditional return frames. This complete floor validates the resulting production tree. The first harness launch refused a short commit ID before running any target; its exact assertion log is retained, and this run uses the full commit identity. The historical 125-family run and its earlier failed census are
retained in their original reports. All L01–L14 requirements remain open.

`inventory.json` records SHA-256 hashes and byte lengths, including decoded
identities for compressed artifacts. Backend/test binaries are identified but
are not included as large duplicate build outputs.
