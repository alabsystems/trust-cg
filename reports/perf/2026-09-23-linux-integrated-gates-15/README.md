# Integrated Linux gates before the sixteenth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `6b16cbac7a38f34636c4e05723fe53fef5718374`:
origin/main `977de52ca` plus two further commits on the L02-P10 branch.

- **The `LD64_GOTPAGE_LO15` window check** (`7c5ca6248`). LLD 22.1.6
  writes this GOT-base form truncated with its default layout. The fix adds
  `LD64_GOTPAGE_LO15`, `LD64_GOTOFF_LO15` and their PAuth forms to the
  checked kinds. The window runs from 0 to 32760 bytes and is measured from
  `_GLOBAL_OFFSET_TABLE_`; the probe showed all three linkers measure from
  that symbol. An image whose base cannot be located is refused as
  unproven. The fixed kind is refused through LLD as a shared library, a
  PIE, and a static IFUNC program. The 100-slot twins run through both
  linkers.
- **Test shims no longer race with exec** (`df3e0ebe7`).
  `e2e_aarch64_elf_tlsie` and `link_options` used to write their cc and
  linker shims in-process, and a test thread forking at the wrong moment
  could make exec fail with "Text file busy". The shims are now written by
  a child `/bin/sh`. Six concurrent runs of both targets at 16 test threads
  pass.

This round closes the defect recorded in
[the fifteenth push's gate record](../2026-09-23-linux-integrated-gates-14/README.md).

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **154 required target families
and 961 Rust tests**, including `link_options` 27/27 and
`e2e_aarch64_elf_tlsie` 13/13. Source fingerprint
`a5af631788f3a3e5607c829b0380946ca9d26297a9a8b23635a7f6ecf15601bf` was
identical before and after. The run took 717 seconds of target wall time
(23:19:32Z to 23:31:41Z), and the highest sampled resident set was 266 MiB.
All four controls were on, and the AY/Clean and dependency identities did
not change.

## Library, CLI and extra suites

- Codegen library: 4,135 passed, 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`).
- Lower library: 1,889 passed.
- CLI: the binary's tests passed 30, `link_options` 27, `output_paths` 8
  and `trust_ir_binary_container` 4.
- The trust-cg-verify CEGIS and proof-suite targets, and the race targets,
  passed.

The bridge lane was not run: only the CLI link driver and test files
changed.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN. L02-P10 stays PARTIAL until a closure audit.
