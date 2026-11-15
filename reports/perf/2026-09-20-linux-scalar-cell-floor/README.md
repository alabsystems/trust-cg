# Complete Linux regression floor after scalar-cell source repair

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Result: **PASS**, **126 required target families passed**,
**0 failed**, **687 Rust tests passed** on clean source
`3569f7827572c199fd41b02c27018de5320fe5c6` with stock Rust 1.97.1 on the Linux AArch64 machine.

This executes the complete 126-family inventory in the maintained
`scripts/check_linux_aarch64.py`, including the newly required
`bridge_copy_types` regression. The original classifier, target-specific
verifier environment exclusions, locked offline Cargo resolution, native
targets and negative controls are unchanged. The external anchored supervisor
runs each target serially with a 16 GiB process-group RSS cap, zero grace, two
Cargo jobs and one Rust test thread. Every command has a 1200-second deadline;
resource failure, skipped execution, filtered tests or incomplete output fail
the run. Tool and dependency identities and the source fingerprint are checked
before and after. Per-target logs, counts, exact commands, executable hashes,
guard evidence and the harness/gate sources are retained.

This is current-source root-workspace regression evidence. The installed
compiler package remains the previous qualified 884b cohort. The separate
rustc-private bridge still refuses its scalar calling frame; the source/ABI
binding and pointer-type repair do not themselves grant native instruction
credit. The historical 125-family run and its earlier failed census are
retained in their original reports. All L01–L14 requirements remain open.

`inventory.json` records SHA-256 hashes and byte lengths, including decoded
identities for compressed artifacts. Backend/test binaries are identified but
are not included as large duplicate build outputs.
