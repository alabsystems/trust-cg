# Linker-written PLT and TLS descriptor trampoline `ADRP`s (second L02-P10 closure audit) on Linux AArch64, 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the change that answers the second 2026-09-23 closure
audit of ledger gap L02-P10 (audit at `eb89b7e68`; the audited change was
`7df1bfdf7`). The change is `8a0f3faf8`. The run used clean source
`8a0f3faf8319405dfa7b500fb0486c0da544ddcd` (tree
`13031e7718e1f58a8bfea2715f24b32adaea7980`) on the Linux AArch64 host
(`aarch64-unknown-linux-gnu`, Ubuntu 24.04, gcc 13.3, GNU ld and readelf
2.42, llvm-objdump 18, stock Rust 1.97.1). `git status --porcelain
--untracked-files=all` was empty before the run, after the build with the
prior link driver, after the probes and timing, and after the mutation
legs, which restore their file. The CLI rebuilt after the prior-driver
build and after the mutants has the same SHA-256 as the one the gates
built. `records/results.json` holds the run's full record: provenance,
tool paths and hashes, every gate's `test result:` lines, every probe's
exit code and output, the timing samples, and each mutant's failing tests
with each panic's location and message.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.
This is execution and object evidence on one host, not a proof.

## What the audit found

PLT stubs were an undisclosed route to a truncated GOT-page `ADRP`, and
the driver installed the image. A call to an imported or preemptible
function carries only `R_AARCH64_CALL26`, but GNU ld 2.42 writes the PLT
header's and each entry's `adrp x16` to `.got.plt` without checking the
+-4 GiB page window. `staged_image_refusals` refused an image not in reach
only when a positional or traced input carried a GOT-page relocation.

## The change

`got_page_layout` records the GOT-addressing code the linker wrote itself
(`LinkerGotCode`): a PLT (`R_AARCH64_JUMP_SLOT`, `DT_JMPREL` or an
executable `.plt`), an IPLT (`R_AARCH64_IRELATIVE` or an executable
`.iplt`) and the lazy TLS descriptor trampoline (`DT_TLSDESC_PLT`). The
staged image is always checked. An image not shown in reach that holds
such code is refused whatever its inputs. A known slot (a PLT entry's
`JUMP_SLOT` slot, the trampoline's `DT_TLSDESC_GOT` word) that no code byte
reaches is `[TCG-LINK-GOT-PAGE-WINDOW]` (`relocation-out-of-range`); other
such code is `[TCG-LINK-GOT-PAGE-UNPROVEN]`. The plan section "L02-P10
second closure audit" of `docs/linux-aarch64-completion.md` and
`LIMITATIONS.md` state the remaining residuals.

## Gates (records/logs)

| log | result |
| --- | --- |
| `test-codegen-lib` | 4130 passed, 1 ignored (4129 at `7df1bfdf7`, plus the new unit test) |
| `test-e2e_aarch64_link_runtime` | 32/32 |
| `test-e2e_aarch64_elf_tlsie` | 13/13 |
| `test-e2e_aarch64_switch` | 2/2 |
| `test-cli-all` | CLI bin 30/30; `link_options` 24/24 (23 plus the new native control); `output_paths` 8/8; `trust_ir_binary_container` 4/4; every other target ok |
| `check-codegen`, `check-codegen-verify` | exit 0 |
| `check-fmt`, `script-gate-tests` (94, OK, 1 skipped), `native-test-host-matrix`, `check-documentation`, `diagnostics-inventory`, `evidence-plan-citations` | exit 0 |

## Direct probes (records/direct)

The probes ran in a scratch directory (`$WORK`). `caller.trust_ir` and
`got_page.o` are the files retained by
`reports/perf/2026-09-23-linux-got-page-trace/records/inputs`, byte for
byte. `defs_main.c` defines `tcg_desc_bump` (returns 7) and exits 0 when
`tcg_call_desc()` returns 7. `records/inputs` holds all of them.

| probes | result |
| --- | --- |
| `prior-cli-{plt,both}` | The CLI built with `7df1bfdf7`'s link driver runs the audit's command, `trust-cg --format=text -shared -nostdlib --relocation-model pic -o libprior_plt.so caller.trust_ir -Wl,--section-start=.got.plt=0x200010000`, and the same with `.got` at `0x200000000` too. Both exit 0 and install the library |
| `prior-objdump-plt-*`, `prior-readelf-r-*` | The installed `.plt` holds `adrp x16, 0x10000` (at `0x2d4` and `0x2f0`) for `R_AARCH64_JUMP_SLOT` against `tcg_desc_bump` at `0x200010018` |
| `run-user_prior_{plt,both}` | The `cc -rdynamic` user dies with SIGSEGV (139) |
| `cli-{plt,both}` | This source: exit 1, exactly one `error[link:` line: a `relocation-out-of-range` refusal of `tcg_desc_bump` (`R_AARCH64_JUMP_SLOT`), `[TCG-LINK-GOT-PAGE-WINDOW] linker-generated PLT (1 R_AARCH64_JUMP_SLOT slot(s), DT_JMPREL, an executable .plt section)`, naming the slot at `0x200010018`. The directory listing is unchanged |
| `raw-gnu-ld-{plt,both}`, `run-user_raw_*` | `cc -shared -nostdlib` on the `pic` object `caller.o` with the same placements links (exit 0), and the user dies with SIGSEGV (139) |
| `cli-near`, `objdump-plt-near`, `run-user_near` | With `.got.plt` at `0x80010000` the library links through the CLI, its PLT holds `adrp x16, 0x80010000`, and the user exits 0 |
| `cli-route-wl` | `-Wl,got_page.o` with `.got` and `.got.plt` 8 GiB away: exit 1, exactly four `error[link:` lines, the two input uses of `got_page.o` plus the PLT entry of `tcg_desc_bump` and the TLS descriptor trampoline (`DT_TLSDESC_PLT at 0x380`), all `[TCG-LINK-GOT-PAGE-WINDOW]`. The listing is unchanged |
| `raw-gnu-ld-route`, `readelf-d-raw-route`, `objdump-plt-raw-route` | GNU ld's own library of the same inputs has `DT_TLSDESC_PLT` `0x380` and `DT_TLSDESC_GOT` `0x200000010`. The trampoline holds `adrp x2, 0x0` and `adrp x3, 0x10000` and the PLT `adrp x16, 0x10000`: every linker-written `ADRP` is truncated |

## Timing (records/timing)

The timing leg built the CLI with the prior link driver (`7df1bfdf7`'s
`link_driver.rs`, everything else from this source), copied it to `$WORK`
and restored the source. It then ran each case 31 times with three debug
binaries: the prior one, the current one in `target/debug`, and an
identical copy of the current one in `$WORK` (the scatter control). The
runs were interleaved, and the order rotated each round. Times in ms:

| case | prior median (IQR, min) | current median (IQR, min) | current copy median (IQR, min) |
| --- | --- | --- | --- |
| `--shared --nostdlib` of `caller.trust_ir` | 17.25 (16.07–23.12, 14.90) | 21.37 (18.04–24.62, 16.95) | 22.32 (16.34–23.86, 15.19) |
| default executable of `answer.trust_ir` | 20.46 (17.33–21.73, 15.47) | 21.64 (19.66–23.26, 17.85) | 20.15 (17.80–21.50, 16.00) |

The samples are bimodal (about 16 to 18 ms and 22 to 25 ms), so the medians
depend on which mode dominates. The identical copy differs from the current
binary by as much as the prior binary does: its minimums are 1.8 ms lower
in both cases. The two binaries in `$WORK` (prior and current copy) have
minimums 0.3 and 0.5 ms apart. With 31 samples on one host, this shows no
cost of the change above the measurement's scatter, not a precise cost.
The added work is a read of the dynamic tags of an image already in
memory.

## Mutation legs (records/mutation)

Each mutant edits `link_driver.rs` once (`mutant.diff`), runs the named
tests (`*.log`) and restores the file. A mutant counts as killed only when a
test failed, not when a build failed.

| mutant | killed by |
| --- | --- |
| `no-linker-got-code` (linker-written code refuses nothing, as at `7df1bfdf7`) | The unit test, the new native control, the route test and the first audit's reproducer test |
| `linker-code-only-with-inputs` (the image is checked only with a positional GOT-page use or a trace, the `7df1bfdf7` condition) | The unit test only (its untraced case). Every native control is a traced `--shared` link |
| `no-jump-slot-slots` (a PLT's `JUMP_SLOT` slots are not known slots, so every PLT refusal is conservative) | The unit test, the new native control and the route test |
| `no-tlsdesc-trampoline` | The unit test, the route test and the first audit's reproducer test |
| `no-irelative` | The unit test only. No native control builds an IPLT (a static glibc executable with `.got.plt` placed far fails GNU ld's own `ADR_PREL_PG_HI21` check against `.bss`) |
| `no-plt-section` | The unit test and three native controls (the evidence text) |
| `no-jmprel` | The unit test and three native controls (the evidence text) |

All 7 mutants are killed.

## Boundaries

- The code is found only from the image. It is not seen in a static image
  without a section header table, in an image that cannot be read as ELF
  (refused only when an input carries a GOT-page use), or in other
  linker-written stubs (range-extension and erratum veneers; not
  examined).
- The IPLT and the conservative PLT and trampoline cases have unit-level
  controls only.
- An unstaged plain `-nostdlib` executable link is still not read back: its
  only way to an IPLT slot more than 4 GiB away is more than 4 GiB of
  positional input.
- The earlier run's boundaries still apply
  (`reports/perf/2026-09-23-linux-got-page-trace/README.md`).
- Only GNU ld 2.42 was run here.
