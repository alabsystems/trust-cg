# Linux integration of Trust IR v43 opaque handles

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Development-only qualification on Linux AArch64, 2026-09-16. Tested source
`e1ed9ce699823f20e5215de9eb4dde9f211ee3cf` has identical compiler/build inputs to
incoming main `8751cedc`. Trust IR is pinned to
`b094459bbe4decfa424e257e7bb9e288114f6990`.

All **59 selected tests passed**, zero failures and zero ignored:

- Opaque-handle integration: 20/20, zero filtered.
- Trust IR conformance manifest: 6/6, zero filtered.
- Codegen handle identity, exported ABI and Core admission: 5/5, 3,821 filtered.
- Trust IR symbolic scanner: 28/28, 3,915 filtered.

The initial documentation check failed because incoming source changes left
`INVENTORY.md` stale. Regenerating that file with the maintained script fixed
it; the final documentation check passed. Both logs are retained. The original
campaign result deliberately retains the initial failure and `complete: false`;
the four passing test results and separate final documentation log are the
qualification evidence. No tests were rerun for the inventory-only correction.

The runner records source-file hashes, exact commands, durations and test
summaries. It held the host resource lease, used two Cargo jobs, and enforced a
16 GiB process-tree RSS limit with zero grace. Every command preserved its
source/build inputs and no watchdog fired. Stock Rust 1.97.1 was used. This is
not a full-workspace, Trust-certified, native-runtime execution or installation
qualification; existing installed binaries remain unchanged. The overall
Linux completion contract remains open.

`inventory.json` records compressed and decoded sizes and SHA-256 hashes for
all retained logs, results and the exact runner.
