# L02-P10 GOT-page check on the staged link (Linux AArch64) — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run re-qualifies L02-P10 after its branch was merged with the
integration head `dbfc88b79`, which carries the L02-P9 second repair
(`9f8f4def9`, merged in `ece600993`). It runs on clean source
`36ac06f11e126178aaf2af1cb89bc475042a3c48` (tree
`c0be5698f302b4f8196491eb5c256a065941120d`) on the Linux AArch64 host
(NVIDIA Grace, `CPU part 0xd87`, Ubuntu 24.04, glibc 2.39, GCC 13.3, GNU ld
2.42, stock Rust 1.97.1). That head is the merge commit `4126eb6c6` plus a
LIMITATIONS-only commit. `git status --porcelain --untracked-files=all` was
empty before and after the qualifying run and after the mutation leg.
`records/results.json` holds the provenance, tool identities and every
gate and probe exit.

The earlier run on the branch alone (`76ead5025`) stays in
[2026-09-23-linux-reloc-kind-limits](../2026-09-23-linux-reloc-kind-limits/README.md).
It covers the per-kind model, the `TLSLE` and `ABS32` refusals, the linker
window probe and the native controls. It does not cover the merged
`run_link`, which this run does.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.

## What the merge changes

On the integration head, `link_driver::run_link` stages every link with a
local-exec input. The linker writes into a fresh driver-owned directory
next to the output, and the image is checked there before one `rename`
installs it. The L02-P10 branch's GOT-page window check still read
`request.output` with a plain `std::fs::read` and removed it on refusal. The
merge resolves that as follows:

- A link is staged when its inputs have local-exec uses or GOT-page `ADRP`
  uses (`ADR_GOT_PAGE`, `TLSIE_ADR_GOTTPREL_PAGE21`, `TLSDESC_ADR_PAGE21`).
  Links with neither still write the output directly.
- The GOT-page check reads the staged image through `read_linked_image`
  (regular file only). `LinkError::OutputRefused` carries the staged path.
  No refusal writes, reads or removes the requested output.
- A staged image that cannot be read as ELF is refused as
  `[TCG-LINK-GOT-PAGE-UNCHECKED]` (kind `unclassified`), not reported as an
  observed `relocation-out-of-range`.
- `LinkError::OutputMissing` names GOT-page inputs as well, so a `pic` link
  with `-Wl,--version` is refused with `[TCG-LINK-NO-OUTPUT]`.
- The checked image is not renamed onto an existing output that is neither
  a regular file nor a symbolic link (`LinkError::OutputStaging`).

## Gates (records/logs)

| gate | result |
| --- | --- |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4097 passed; 0 failed; 1 ignored` |
| same, filtered to `link_driver`, `elf::reloc`, `elf::dwarf`, `pipeline::tests::local_exec`, `pipeline::tests::intra_object` | `ok. 52 passed; 0 failed; 0 ignored; 4046 filtered out` |
| `e2e_aarch64_link_runtime` (`--nocapture`) | `ok. 28 passed; 0 failed` |
| `e2e_aarch64_elf_tlsie` | `ok. 11 passed; 0 failed` |
| `aarch64_elf_dwarf` | `ok. 12 passed; 0 failed` |
| `e2e_aarch64_elf_relocation_model` | `ok. 19 passed; 0 failed` |
| `trust-cg-cli --test link_options` | `ok. 14 passed; 0 failed` |
| `trust-cg-cli --bin trust-cg` | `ok. 29 passed; 0 failed` |
| `trust-cg-cli --test output_paths` | `ok. 8 passed; 0 failed` |
| `trust-cg-verify --lib` (relocation filters) | `ok. 40 passed; 0 failed; 4139 filtered out` |
| `cargo check -p trust-cg-codegen` (plain and `--features verify`), `cargo build -p trust-cg-cli` | exit 0 |
| `scripts/check_fmt.sh`, the three gate script tests, `native_test_host_matrix.py --check`, `check_documentation.py --check`, `generate_diagnostics_inventory.py --check`, `check_evidence_archive.py --plan` | exit 0 |

In the `e2e_aarch64_link_runtime` log, the far-GOT control prints `far GOT:
the linker accepted it; the link driver refused the image` and both
`[TCG-LINK-GOT-PAGE-WINDOW]` lines. The refusal therefore comes from the
staged image check after GNU ld 2.42 linked the image.

## Direct CLI probes (records/direct)

`records/inputs/got_page.tmbc` is the same `pic` probe module as in the
earlier run (identical SHA-256). `tcg_desc_bump` reaches `tcg_desc_tls`
through a TLS descriptor and `tcg_desc_word` through the GOT. In `cg/`, the
file `libfar.so` held `precious\n` before the first probe.

- `cli-far-got-shared`: `trust-cg -shared -nostdlib --relocation-model pic`
  with `.got` at 8 GiB exits 1 with two `error[link:relocation-out-of-range]`
  `[TCG-LINK-GOT-PAGE-WINDOW]` lines (`tcg_desc_tls`,
  `R_AARCH64_TLSDESC_ADR_PAGE21`; `tcg_desc_word`, `R_AARCH64_ADR_GOT_PAGE`).
  It then prints `the linked output for libfar.so was refused and not
  installed; the linker's image was removed`. `libfar.so` still reads
  `precious` (`cat-libfar-after-refusal`), and no `.tcg-link-*` directory is
  left (`ls-after-far`).
- `cli-near-got-shared`: with `.got` at 2 GiB the library is installed
  (`readelf-SW-libnear.so`). An executable linked against it checks `42`
  then `44` and exits 0 (`run-desc`).
- `cli-pic-version`: `-Wl,--version` under the `pic` model exits 1 with
  `[TCG-LINK-NO-OUTPUT] … the link has GOT-page ADRP inputs (…)`, and
  `libfar.so` still reads `precious`.
- `cli-pic-dev-null`: `-o /dev/null` exits 1. The driver cannot create its
  staging directory in `/dev` as this user (`Permission denied`), and
  `/dev/null` stays a character device 1:3 (`stat-dev-null`). As root, the
  directory would be created and the install step would refuse the device
  output. The unit test covers that step with a socket output; this run did
  not run as root.
- `cli-pic-fifo` and `cli-compile-only-fifo` time out at 10 s with no
  output. This happens with a staged link and with `-c` alike, so it is not
  the link driver: the CLI's output-alias check opens an existing FIFO
  output (`same_file::is_same_file`) and blocks before any compile. The
  FIFO is untouched (`stat-fifo`). LIMITATIONS.md states this boundary.

## Mutation leg (records/mutation)

`harnesses/mutation-reloc-limits-staged-20260923.py` applied each mutant to
the clean head, ran the named tests and restored the file byte for byte.
All four were killed, each expected test named `FAILED`, and `status_after`
is empty:

- S1: a GOT-page link is not staged (`if local_exec_uses.is_empty()`). The
  scripted-driver unit test gets `Ok` for the far image. The e2e control
  panics `a GOT 8 GiB from the code must not link silently: Ok(...)`. The
  CLI `--version` test sees the `pic` link succeed.
- S2: the check reads `request.output` instead of the staged image. The unit
  test and the e2e control fail: the refusal becomes `unclassified` (an
  unreadable or pre-existing file) instead of `relocation-out-of-range`.
- S3: an unreadable image is reported as `relocation-out-of-range`. Both
  GOT-page unit tests fail.
- S4: the non-regular-output guard is removed. The socket output is
  replaced, and the unit test gets `Ok` instead of `OutputStaging`.

## Boundaries

This is unit, linker and execution evidence on one host, not proof. The
GOT-page check covers only links through `run_link` (the CLI's link step)
and only AArch64 ELF relocatable inputs. It does not cover archive members,
shared libraries or links made outside the driver. It compared the
farthest code byte with the farthest `.got`/`.got.*` byte, with fallbacks.
This README first called that conservative. It was not: a linker script
could move the GOT's slots into a section of another name, 8 GiB away,
while `.got.plt` stayed near. The check then admitted an image whose
`ADR_GOT_PAGE` delta GNU ld had truncated. The 2026-09-23 slot-region
repair (plan, "GOT-page slot
region repair") derives the region from the image instead. The linker
probe in the earlier run placed the GOT at 2 GiB and 8 GiB, not at a
`+-4 GiB` edge, and gold gave no GOT-page evidence. Staging now applies to
every link with a GOT-page input, such as `pic` objects and initial-exec
imports. Such a link needs a writable directory next to its output.

## Reproduce

```sh
python3 -B harnesses/qualify-reloc-limits-staged-20260923.py <worktree> <run-dir>
python3 -B harnesses/mutation-reloc-limits-staged-20260923.py <worktree> <run-dir>
python3 -B harnesses/archive-reloc-limits-staged-20260923.py <run-dir> <this directory>
```

`<run-dir>/inputs/got_page.tmbc` is `records/inputs/got_page.tmbc.gz`
decompressed.
