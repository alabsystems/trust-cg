# Integrated Linux gates before the sixth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `701a2d2360a366eb1894f11c6d4402f296bc1116`.
It is origin/main `dbfc88b79` plus the third L02-P9 repair.

The repair (`502fab20f`) refuses, with `[TCG-LINK-RESPONSE-FILE]`, every
value the link driver forwards that begins with `@`: output and input paths,
`-L` directories, `-l` names, the soname and run-time search paths. The C
driver, collect2 and GNU ld would otherwise expand such a value as a
response file. The repair also rewrites the documents to name the link
routes the local-exec scan does not examine:

- a `-Wl`-group object;
- `-l:<file>`;
- archive members;
- linker-script `INPUT()`;
- shared-library inputs.

A native test pins the first two as the documented boundary. That closes
the response-file route listed in
[the fifth push's gate record](../2026-09-23-linux-integrated-gates-4/README.md).
The unscanned routes remain, and are documented and pinned. L02-P9 stays
PARTIAL.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **147 required target families
and 866 Rust tests**. Source fingerprint
`31a0c2102f4f1c60b268abd3758bdb53ff65336d6e686fd1b8c9cf7bcf116835` was
identical before and after the run. The run took 586 seconds of target wall
time (08:21:02Z to 08:30:53Z), with a highest sampled resident set of
300 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change. The changed targets passed: `link_options`
16/16, `e2e_aarch64_elf_tlsie` 11/11 and `e2e_aarch64_link_runtime` 21/21.

## Library suites

On the same checkout, `cargo test -p trust-cg-codegen -p trust-cg-lower --lib`
passed: codegen 4,090 passed and 1 ignored (the pre-existing
`raw_machir_request_cache_real_exhaustive_campaign`), and lower 1,879
passed. `cargo test -p trust-cg-cli --bins` passed 29/29. The bridge lane
was not run: the repair changes the CLI link driver and comments in
`trust-cg-lower/src/adapter.rs`, neither of which is on the rustc backend's
object-emission path.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

`records/run9/` holds the complete floor output; `records/lib-i6.log.gz` and
`records/cli-bin-i6.log.gz` hold the library transcripts.
