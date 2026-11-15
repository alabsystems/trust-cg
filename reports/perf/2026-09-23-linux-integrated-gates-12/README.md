# Integrated Linux gates before the thirteenth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `5258dfe62839f9b5da810b866be2f77669bbcdcb`.
The source is origin/main `e8ef75fc3` plus the L02-P9 closure-residual
increment. That increment was reviewed adversarially, repaired, and then
checked by an independent verifier.

## The increment

**Every input the linker loads is examined.** `link_driver::run_link` now
runs the link with the linker's input trace (`--trace`). Before it installs
a non-executable image, it scans every loaded AArch64 ELF relocatable for
`R_AARCH64_TLSLE_*`, including archive members, which it reads itself.
Eight routes are refused by name (`[TCG-LINK-TLS-MODEL]`), each with its pic
twin running:

- a `-Wl` operand;
- `-l :file.o`;
- an archive member linked by reference;
- `--whole-archive`;
- a thin archive;
- linker-script `INPUT()` and `GROUP()`;
- `--start-group`.

An unreadable trace (for example under `--verbose` or `-M`) refuses a
shared output (`[TCG-LINK-INPUT-TRACE]`). Shared-library inputs cannot
carry `TLSLE` relocations; the executable-side mismatch against them stays
classified.

**Which links are staged.** On Linux, every link is staged except a plain
executable link whose positional inputs carry no local-exec or GOT-page
relocation.

**CLI link modes.** Links through the CLI binary itself now run and check
the ELF kind: the default and `--pie` give `ET_DYN`+`DF_1_PIE`,
`--no-pie` gives `ET_EXEC`, and `--static` gives `ET_EXEC` with no
`PT_INTERP`. `--nostdlib` is also run.

**TEXTREL control.** It now pins its subject and has a twin without
`-z text` that links, shows `TEXTREL`, and runs.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **151 required target families
and 931 Rust tests**:

- `link_options` 20/20;
- `e2e_aarch64_elf_tlsie` 13/13;
- `e2e_aarch64_link_runtime` 32/32.

The source fingerprint
`8d5cbcd2dbf36fef725e8033e918412ef4a5f848d897fa604144b2e1694cc92d` was
identical before and after the run. The run took 687 seconds of target wall
time (16:30:10Z to 16:41:46Z), and the highest sampled resident set was
168 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and extra suites

- **Codegen library:** 4,122 passed, 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`).
- **Lower library:** 1,879 passed.
- **CLI:** the binary's tests passed 30, `link_options` 20, `output_paths`
  8 and `trust_ir_binary_container` 4.
- **trust-cg-verify:** the CEGIS and proof-suite targets passed.
- **Race targets:** both passed at 16 threads.

The bridge lane was not run. The rustc backend does not use the link
driver, and the `adapter.rs` change is comments only.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN. L02-P9 stays PARTIAL until a separate closure audit.
