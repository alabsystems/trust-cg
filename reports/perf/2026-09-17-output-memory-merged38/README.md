# Merged arithmetic/output-memory controls: Mac qualification

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Exact source `3d7164b2264648596928ebdd8983dc1b1f978f0d` (tree
`3f38a20ac349a1baf928427c5f34ad2a834d8ddf`) passes two fresh Trust
**unverified** compilations and **38 tests**, with no failures or ignores,
on ARM64/macOS. Root and independent terminal reviews passed. This is the
bounded development qualification of the merged arithmetic/output-memory
checker, not production output-memory admission.

The tested merge contains output-memory checkpoint `36956c86` and peer
source-bound arithmetic `c611a263`. It closes the merged-tree follow-up in
the [original 33-test report](../2026-09-17-output-memory33/README.md).
It does **not** qualify later main `405f20a6` or that revision's AOT export
validation work. Those later production changes require their own evidence.

## Four phases and actual coverage

All four phases exit zero: ordinary `trust-cg-verify --lib` check, fresh library
test build, exact `source_bound_` discovery, and serial execution. The actual
listing and results contain exactly 38 unique names: the original 33 frame
controls (16 base, six diamond, three callback-cell and eight output-memory)
plus five source-bound arithmetic unit controls. `selection.json` and the
unabridged logs retain the names, statuses and actual requests.

The ordinary metadata image is SHA256
`92b7523e18d03745a1c5114a174f6f59959e06eb127e5e3a3191be3b7e1779e4`
(44,175,678 bytes). The test image is SHA256
`cac0d6a4cb23faa8ba94d7b50e4a7d8813a38fd8371628caaf87f126fc8e7c4d`
(145,890,688 bytes). Fresh compiler invocations, generated environments,
artifact messages and direct-extern identities are recorded. The 34 recorded
primary/direct-extern/checker files total 783,749,118 bytes; their final
identities match the qualification's earlier book.

The scalar and paired-store diagnostics again capture two identical strings:
**one unique query**, 96,284 UTF-8 bytes, SHA256
`e7cb7c86173f17dfd2445faeaab42604ebe64f31e674f6e49803a93395a0e6c7`.
Its bytes are unchanged from the original 33-test campaign. These four phases
do not invoke a solver or independently replay this query. Any later solver
attempt, refusal or certificate belongs to a separate retained result.

## Unchanged limits and preservation

Compilation uses the pinned September 10 Trust development toolchain with
`targo --unverified`, debug/default features, one job and locked dependencies.
No stock Rust or newer managed compiler is substituted. The original limits
remain 7,200 seconds per build, 60 seconds for listing and 300 seconds for
the test group. The 12 GB scheduling reservation is not a hard memory cap or
a measured peak. Only `CARGO_TARGET_DIR` is relocated; runtime keeps the
previously pinned AY/Clean discovery prefix. Libtest `--show-output` retains
the query bytes.

Copy-only admission first creates an independent target: all 10,014 copied
entries satisfy metadata/distinct-inode checks, with exact bytes for the 64
selected artifacts. Neither the original cache nor the original 33-test
campaign's target is released or written. The terminal qualification retains
unchanged source, tool, configuration, sysroot, locked upstream, proof-prefix,
resource, owner and historical-record books. Three residual sampler sleeps
drain naturally in 4.161 seconds within the existing five-second grace; no
cleanup signal is sent. This does not establish hostile-descendant containment.
This report neither retains compiled payloads nor releases any target.

Terminal result SHA256:
`fa5b8b1f688eb0142ea5f059c845023e6e43d8a0095908d0c55d02c860916a7b`.
Copy result SHA256:
`2efe089b042f4ca05bbfc4cba5c5e654d9f6736b3fddc8b07f7814155ff216f2`.

## Claim boundary and evidence

The diagnostic compares complete ordered source/machine effects before adding
numerical memory premises. Its controls do not establish live writable
allocation, caller permission or ownership. The production frame-proof route
still refuses these effectful output bodies. No ordinary Rust writer fixture
is compiled, no generated native code is executed, and no proof owner or
production memory-admission policy is broadened by this campaign. The separate
Linux arithmetic evidence is not inherited as Mac execution or proof evidence.
There is no verified-Rust, complete TY source-to-native or TY/TLC performance
claim.

The archive `output-memory-merged38-evidence.tar.gz` (removed from the tree) and
per-file byte/mode audit contain exactly 53 regular
members: all 33 qualification records, eight clone records, four control/prior
files and eight exact selected source files. No compiled payload, links,
escaping paths, duplicate members or AppleDouble entries are included. Every
member's bytes and mode match its original before and after archiving; exact
payload size is 38,816,257 bytes. Archive SHA256:
`742abfe003bc511d243950ba1a668fc0440869fe15596545d504d3d7c0107064`
(6,461,440 bytes).

The shared plan remains its immutable **pre-activation** version; enabled
controller copies and hashes record the later launch. Absolute historical
workspace paths are provenance, not portable installation instructions. The
original 33-test report and its evidence remain unchanged.
