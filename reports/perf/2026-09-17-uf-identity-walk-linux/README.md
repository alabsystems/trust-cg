# Linux qualification of the shared-node UF declaration walk

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A fresh Linux AArch64 library-test build at source
`8c36dbefe2392662b8f036e3512fc225cb4530e8` passes all **44 selected controls**:
38 source-bound verifier tests and all six UF traversal tests. Native listings
and executed names match exactly, with no missing, duplicate, ignored or failed
cases. The complete source fingerprint is unchanged across the campaign.

Both captured output-memory queries are exactly 96,284 bytes with SHA256
`e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`. They match the original retained failing
query byte for byte. The new traversal preserves that input while bounding
repeated visits to shared expression nodes; these tests make no elapsed-time,
allocation or end-to-end performance claim.

The [incoming Mac qualification](../2026-09-17-uf-identity-walk/README.md)
describes the source change and its tradeoffs. The visited-address set is local
to each immutable expression walk and does not become a proof or cache identity.
It costs temporary memory proportional to unique nodes; recursive depth,
tree-shaped query formatting and signature work remain separate costs.

This campaign uses stock Rust 1.97.1, locked dependencies, two build jobs,
serial tests and an exclusive host resource lease. Every child has a zero-grace
16 GiB RSS limit; build timeout is 1,200 seconds, listings 60 seconds and test
groups 600 seconds. No child times out, breaches memory limits or truncates
captured output. Frozen test executable SHA256:
`61fc6a59b4bf7a11d2d922110e1c05b87bc3defcee0ae55f56c8af6993ff4066` (478,774,920 bytes).

The existing qualified AY/Clean prefix is retained in the tool provenance.
Commands, test listings, complete output, original query strings, source/tool
identities and the runner are archived with audited compressed/decoded hashes
and lengths. The large executable remains local. This is a focused development
check, not a Trust-certified build, updated installation, new output-memory
admission or complete Linux acceptance report.
