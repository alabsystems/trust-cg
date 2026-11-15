# GEP inventory repair regression

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**PASS: 15 tests, zero failures, zero ignored, zero filtered**, measured on
`f522ed45be84d8109cd1a8cb3424324148dd5e0f` with stock Rust 1.97.1.
The complete inventory target was rebuilt and executed with one Cargo job,
one test thread, offline locked dependencies and a 4 GiB process-group limit.
Other independent worktrees were compiling; this is correctness regression
evidence, not a controlled performance comparison.

The [preceding full floor](../2026-09-24-flat-gep-floor-first/README.md)
ran all 167 targets and failed only this inventory assertion. The repaired
GEP row now points to the native byte-gather test that actually constructs
GEP, rather than the renamed packed-field test that uses ExtractField.
The referenced native byte-gather target passed in that full run. Both the
source inventory and its committed JSON agree after the repair.

The incoming main changes at integration touch four backend source files;
the inventory target, its lowering dependencies, pinned lockfile and named
evidence test sources are unchanged from the measured repair. The exact
changed-file list is retained in the inventory. This does
not carry the earlier full-floor result forward to those backend changes.
A complete repaired floor and native frame-entry qualification remain separate
runs on their recorded source revisions.

The raw request, execution receipt, test log and executable SHA-256 are
retained with compressed and uncompressed hashes.
