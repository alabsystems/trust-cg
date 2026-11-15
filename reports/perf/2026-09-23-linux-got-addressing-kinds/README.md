# Every aaelf64 GOT-addressing kind and hidden IPLTs (third L02-P10 closure audit) on Linux AArch64, 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the change that answers the third 2026-09-23 closure
audit of ledger gap L02-P10 (an independent verifier of `8a0f3faf8`). The
change is `a0d5453ae`. The run used clean source
`a0d5453aefe1e1ff740dce02d459ecd1cf7314d3` (tree
`77e9c3bb79a5b62d3f0566e6042eccc8128fb877`) on the Linux AArch64 host
(`aarch64-unknown-linux-gnu`, Ubuntu 24.04, glibc 2.39, gcc 13.3, GNU ld,
as, readelf and objdump 2.42, LLD 22.1.6, stock Rust 1.97.1). The harness
ran in phases (gates, direct, kinds, timing, two mutant batches, finish);
`git status --porcelain --untracked-files=all` was empty before and after
each phase, and the CLI rebuilt after the prior-driver build and after the
mutants has the SHA-256 the gates built
(`44c416be5b312de0714c5033f50ec22cdf3ddaadb400277191289834ee0f6805`).
`records/results.json` holds every phase record: provenance, tool paths and
hashes, every gate's `test result:` lines, every probe's exit code and
output, the timing samples, and each mutant's failing tests with each
panic's location and message. After the gates, direct, timing and mutant
phases the harness was amended to replace host paths in recorded command
lines (`$HARNESSES`, `$RUN`) and to keep its per-phase files; the kinds and
finish phases were rerun with it, and the per-phase files were then dropped
because `results.json` holds them verbatim.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.
This is execution and object evidence on one host, not a proof.

## What the audit found

1. `R_AARCH64_TLSGD_ADR_PAGE21` (traditional general-dynamic `ADRP`) was
   not a checked kind: `trust-cg -shared -nostdlib --relocation-model pic
   -Wl,gd.o -Wl,--section-start=.got=0x200000000 -o libgd.so
   b1_scalars.tmbc` installed `get_gd` with `adrp x0, 0`.
2. Tiny-model GOT loads (+-1 MiB) were not checked:
   `R_AARCH64_TLSIE_LD_GOTTPREL_PREL19` followed by 1.5 MiB of text
   installed, and GNU ld links `TLSGD_ADR_PREL21`, `TLSDESC_ADR_PREL21` and
   `TLSDESC_LD_PREL19` truncated as well.
3. A linker script that merges `.iplt` into `.text` and `.rela.iplt` into a
   `PROGBITS` `.rodata` hid a static image's IPLT, as `-z nosectionheader`
   did (4, the disclosed residual).

## The change

`AARCH64_GOT_ADDRESSING_RELOCATIONS` lists the 17 aaelf64 kinds whose value
is a GOT slot measured from the place they patch, each with its reach
(window) and the dynamic relocations that fill its slot; every GOT-addressing
use of a positional or traced input is checked against its own window from
every possible site to every possible slot place; a defined
`STT_GNU_IFUNC` symbol is a page-window use of its own. The kind table is
pinned by `got_addressing_kinds_match_the_psabi_tables` against a
transcript of all 57 aaelf64 rows whose operation names a GOT slot
(`records/psabi/aaelf64-got-kinds-excerpt.txt.gz` holds the source lines,
from aaelf64 at abi-aa commit `a5e86d3fe`, file SHA-256 `7432d7d3…`):

| Kind (`R_AARCH64_`) | Reach | Window on `X` | GNU ld 2.42, GOT out of window (`records/kinds`) |
| --- | --- | --- | --- |
| `ADR_GOT_PAGE`, `TLSIE_ADR_GOTTPREL_PAGE21`, `TLSDESC_ADR_PAGE21`, `TLSGD_ADR_PAGE21` | `ADRP` page delta | `-2^32 <= X <= 2^32 - 4096` | links (truncated) |
| `TLSLD_ADR_PAGE21` | `ADRP` page delta | same | refuses |
| `AUTH_ADR_GOT_PAGE`, `AUTH_TLSDESC_ADR_PAGE21` | `ADRP` page delta | same | unrecognized |
| `TLSIE_LD_GOTTPREL_PREL19`, `TLSDESC_LD_PREL19` | load literal | `-2^20 <= X <= 2^20 - 4` | links (truncated) |
| `GOT_LD_PREL19` | load literal | same | refuses |
| `TLSLD_LD_PREL19`, `AUTH_GOT_LD_PREL19` | load literal | same | unrecognized |
| `TLSGD_ADR_PREL21`, `TLSDESC_ADR_PREL21` | `ADR` | `-2^20 <= X <= 2^20 - 1` | links (truncated) |
| `TLSLD_ADR_PREL21` | `ADR` | same | refuses |
| `AUTH_GOT_ADR_PREL_LO21` | `ADR` | same | unrecognized |
| `GOTPCREL32` | 32-bit data word, any place | `-2^31 <= X <= 2^31 - 1` | unrecognized |

The other 40 rows need no image check: 26 GOT-base forms (the value is a
slot's distance from the GOT base, both placed by the linker; GNU ld
refuses `LD64_GOTPAGE_LO15` and `LD64_GOTOFF_LO15` with 5,000 slots and
`TLSDESC_OFF_G1` with `.got.plt` 8 GiB from `.got`, and does not recognize
the other `MOVW_GOTOFF_*` forms than `_G0_NC`/`_G1`, `TLSLD_MOVW_*` or the
PAuth forms), 10 low-12-bit forms paired with a checked row, and 4 markers.
LLD 22 was run with the default layout only: it links `GOT_LD_PREL19`,
`ADR_GOT_PAGE`, `GOTPCREL32`, the initial-exec and descriptor page kinds
and the PAuth `ADRP`, load-literal and `ADR` kinds, and refuses the
general- and local-dynamic kinds, `TLSIE_LD_GOTTPREL_PREL19` and the
descriptor load-literal and `ADR` kinds as unknown.

*Correction (2026-09-23):* the GOT-base rationale above holds for GNU ld
and gold 2.42 but not for LLD 22.1.6. LLD links `LD64_GOTPAGE_LO15` with the
offset truncated to 15 bits; running LLD with the default layout only did
not show it, and an independent verifier found the CLI installing such LLD
images. The `LDR` GOT-base forms are now checked; see
[GOT-base repair](#got-base-repair-ld64_gotpage_lo15-through-lld-recordsrepair)
below.

## Gates (records/logs)

| log | result |
| --- | --- |
| `test-codegen-lib` | `test result: ok. 4133 passed; 0 failed; 1 ignored` (4130 at `8a0f3faf8`, plus three new unit tests; the pin test replaces the earlier one) |
| `test-codegen-e2e` | `aarch64_elf_symbol_binding` 19/19, `e2e_aarch64_elf_relocation_model` 19/19, `e2e_aarch64_elf_tlsie` 13/13, `e2e_aarch64_globals_linux` 15/15, `e2e_aarch64_link_runtime` 32/32 |
| `test-cli` | CLI bin 30/30, `link_options` 26/26 (24 plus the two new native controls), `output_paths` 8/8 |
| `check-codegen-verify`, `check-fmt`, `check-documentation-write` (tree clean after), `check-documentation`, `diagnostics-inventory`, `evidence-plan-citations` | exit 0 |
| `script-gate-tests` | `Ran 94 tests`, `OK (skipped=1)` |

## Direct probes (records/direct)

`$WORK` is the scratch directory. The prior CLI is this source's CLI built
with `8a0f3faf8`'s `link_driver.rs` (SHA-256 `5ba9511c…`). Every source,
script and user program is in `records/inputs`; the objects are assembled
from them with GNU as 2.42.

| route | prior CLI (`8a0f3faf8` driver) | this source | GNU ld outside the driver | near twin through this source |
| --- | --- | --- | --- | --- |
| 1: `-Wl,gd.o`, `.got` at `0x200000000` | installs; `get_gd` holds `adrp x0, 0`; user prints `module=0`, exit 1 | exit 1, one `relocation-out-of-range` `[TCG-LINK-GOT-PAGE-WINDOW]` for `gdvar` (`R_AARCH64_TLSGD_ADR_PAGE21`, its `TLS_DTPMOD64` slot at `0x200000008`); nothing written | user `module=0`, exit 1 | `.got` at `0x80000000`: links, `module=1`, exit 0 |
| 2: `-Wl,tie_0x180000.o` | installs; the load literal reads `0xfffffffffff9ffe0`, its `TLS_TPREL64` slot is at `0x19ffe0`; user SIGSEGV (139) | exit 1, one `unclassified` `[TCG-LINK-GOT-PAGE-UNPROVEN]` for `ievar` (`R_AARCH64_TLSIE_LD_GOTTPREL_PREL19`, the +-1 MiB load-literal window; 1.5 MiB of text reaches the slot from some bytes, so no overflow is observed) | user SIGSEGV | `tie_0x10000.o`: links, `ievar=42`, exit 0 |
| `-Wl,gd21.o` (`adr x0, :tlsgd:`, then `__tls_get_addr`), `.got` at `0x1000000` | installs; user SIGSEGV | exit 1, one `[TCG-LINK-GOT-PAGE-WINDOW]` (`R_AARCH64_TLSGD_ADR_PREL21`, `TLS_DTPMOD64` slot) | user SIGSEGV | default layout: links, 42, exit 0 |
| `-Wl,desc21.o` (descriptor `ldr` and `adr`), `.got` at `0x1000000` | installs; user SIGSEGV | exit 1, two `[TCG-LINK-GOT-PAGE-WINDOW]` (`TLSDESC_LD_PREL19`, `TLSDESC_ADR_PREL21`, `TLSDESC` slot) | user SIGSEGV | default layout: links, 42, exit 0 |
| 3: `--static --nostdlib --no-pie -Wl,ifunc.o -Wl,-T,script_0x200000000.ld` | installs; IPLT `adrp x16, 0`; program SIGSEGV | exit 1, one `[TCG-LINK-GOT-PAGE-UNPROVEN]` naming `myfunc` (`STT_GNU_IFUNC`) | SIGSEGV | `script_0x80000000.ld`: links, exit 42 |
| 4: `--static --nostdlib --no-pie -Wl,ifunc.o -Wl,-z,nosectionheader`, `.got.plt` at `0x200000000` | installs; program SIGSEGV | exit 1, one `[TCG-LINK-GOT-PAGE-UNPROVEN]` naming `myfunc` | SIGSEGV | with section headers at `0x80000000`: links, exit 42; with `-z nosectionheader` at `0x80000000`: refused (no image without section headers is shown in reach) |
| default static layout, `.got.plt` at `0x200000000` | refused (visible PLT and IPLT: two lines) | exit 1, three lines (the IFUNC, the PLT and the IPLT) | SIGSEGV | `0x80000000`: links, exit 42 |

Each refusal leaves the directory listing unchanged. Every check the
harness evaluates is true (`records/results.json`,
`phases.direct.result.direct.checks`).

## Timing (records/timing)

31 interleaved rounds, the order rotated each round, of the prior CLI, this
source's CLI and an identical copy of it (the scatter control); times in
ms:

| case | prior median (IQR, min) | current median (IQR, min) | current copy median (IQR, min) |
| --- | --- | --- | --- |
| `--shared --nostdlib` of `b1_scalars.tmbc` | 14.83 (13.86–17.79, 12.83) | 17.17 (16.14–19.53, 13.97) | 14.27 (13.51–17.33, 12.44) |
| default executable of `answer.trust_ir` | 20.76 (19.88–21.22, 17.38) | 21.94 (20.03–23.38, 18.48) | 21.82 (20.07–23.82, 16.80) |
| `--static` with `.data` at 8 MiB | 36.19 (34.75–44.51, 30.53) | 74.80 (69.44–80.95, 59.93) | 74.09 (67.61–78.90, 59.04) |

The first two cases differ from the prior by no more than the identical
copy differs from the current binary. The third is a real cost: its code
and possible slots lie more than 1 MiB apart, so this source reads the
linker's input trace (the C runtime's objects and `libc.a`'s members) for
narrow-window uses and IFUNC definitions, which the prior driver did not
for an image in page reach. That adds about 38 ms (median) to such a static
link on this host.

## Mutation legs (records/mutation)

Each mutant edits `link_driver.rs` once (`mutant.diff`), runs the named
tests (`*.log`) and restores the file. A mutant counts as killed only when
a test failed, not when a build failed. The row mutants make
`got_relocation_name` skip one code.

| mutant | killed by |
| --- | --- |
| `drop-tlsgd-adr-page21` (route 1) | the pin test, the tiny/GD/IPLT unit test, the native GD/tiny control |
| `drop-tlsie-ld-gottprel-prel19` (route 2) | the pin test, the tiny/GD/IPLT unit test, the native control |
| `drop-tlsgd-adr-prel21` | the pin test, the native control |
| `drop-tlsdesc-ld-prel19`, `drop-tlsdesc-adr-prel21` | the pin test, the native control (one refusal short) |
| `drop-got-ld-prel19` | the pin test, the tiny/GD/IPLT unit test |
| `drop-tlsld-adr-page21`, `drop-gotpcrel32`, `drop-auth-adr-got-page` | the pin test only (GNU ld refuses or does not recognize these kinds, so no native control can install them) |
| `no-ifunc-definition` (routes 3 and 4) | the tiny/GD/IPLT unit test, the native hidden-IPLT control |
| `page-window-for-every-reach` | five unit tests and the native GD/tiny control |
| `one-use-per-symbol` | the tiny/GD/IPLT unit test, the native control (the descriptor route's second refusal) |
| `data-word-sites-in-code` | the narrow-window unit test only |

All 13 mutants are killed.

## Boundaries

- The narrow windows are checked without locating the site: a tiny-model
  image larger than 1 MiB is refused even when GNU ld wrote it correctly,
  and every image whose code and possible slots lie more than 1 MiB apart
  needs a readable linker trace (so `-Wl,--verbose` now refuses it).
- A hidden IPLT is refused through its IFUNC's definition, not found in the
  image; an IFUNC no examined input defines (a link outside the driver, a
  non-AArch64 input) is not seen.
- Only AArch64 ELF relocatable inputs are read; links outside the driver,
  files replaced after the link, linker-plugin code without a traced file
  and other linker-written stubs (range-extension and erratum veneers) are
  not examined.
- `GOTPCREL32`, `TLSLD_LD_PREL19` and the PAuth rows have unit-level
  controls only: GNU ld 2.42 does not recognize them. LLD was probed with
  the default layout only.
- The earlier runs' boundaries still apply
  (`reports/perf/2026-09-23-linux-got-page-plt/README.md`).
- Only GNU ld 2.42 linked the native controls.

## GOT-base repair: `LD64_GOTPAGE_LO15` through LLD (records/repair)

An independent verifier of `a0d5453ae` found that the exemption of the
GOT-base forms (above) does not hold for LLD 22.1.6.
`R_AARCH64_LD64_GOTPAGE_LO15` (`G(GDAT(S)) - Page(GOT)`, `0 <= X < 2^15`)
is the GOT load of GCC's small-PIC model (`-fpic`). GNU ld and gold 2.42
refuse it out of range. LLD writes `X & 0x7ff8` without a diagnostic, and
the CLI installed its images. The repair is `7c5ca6248`
(`7c5ca6248998242653e6a69edcc8d966e4096d23`, tree
`7925aba4a2c6950a513f48b6729015b483e269b1`). It adds `LD64_GOTOFF_LO15`,
`LD64_GOTPAGE_LO15` and their PAuth forms to the checked kinds. Each is
checked from the GOT base the image's symbol table gives
(`_GLOBAL_OFFSET_TABLE_`). Every place such a slot can lie (the section
holding the base, each `GLOB_DAT`, `AUTH_GLOB_DAT` and `IRELATIVE` target,
and the `IRELATIVE` entries between `__rela_iplt_start` and
`__rela_iplt_end`) must be at or above the base (or its page) and less than
32 KiB above it. An image whose base cannot be located is not shown in
that window.

The run used clean `7c5ca6248` on the same host, with GNU ld, gold, as,
readelf and objdump 2.42, LLD 22.1.6 and stock Rust 1.97.1. It ran the
phases gates, direct, kinds, timing, two mutant batches and finish, from
`harnesses/qualify-got-base-repair-20260923.py`. `git status
--porcelain --untracked-files=all` was empty before and after each phase.
The CLI the gates built and the CLI rebuilt after the mutants have the same
SHA-256 (`e878987e32b997dc725773150f2679fe19ee7710e15399230fdb7adc49fefeed`).
`records/repair/results.json` holds every phase record (the per-phase files
were left out, since `results.json` holds them verbatim). The run was
archived with `harnesses/archive-got-base-repair-20260923.py`, which also
rewrote `inventory.json` over the whole archive. The earlier records are
unchanged. The direct and kinds phases were rerun before archiving (the
first direct run's records held all 6,001 relocations of one library, and
the first kind probe recorded host paths in its command lines). Neither
rerun changed a result.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure.
This is execution and object evidence on one host, not a proof.

### Gates (records/repair/logs)

| log | result |
| --- | --- |
| `test-codegen-lib` | `test result: ok. 4135 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out` (4133 before, plus the two new unit tests) |
| `test-codegen-e2e` | `e2e_aarch64_elf_tlsie` `test result: ok. 13 passed; 0 failed`; `e2e_aarch64_link_runtime` `test result: ok. 32 passed; 0 failed` |
| `test-cli` | CLI bin `test result: ok. 30 passed; 0 failed`; `link_options` `test result: ok. 27 passed; 0 failed` (26 plus the new native control) |
| `test-cli-got-base-lld-required` | the new control with `TCG_REQUIRE_LLD=1`: `test result: ok. 1 passed`, no `SKIP:` line |
| `test-cli-got-base-without-lld` | the new control with no `ld.lld` reachable: one `SKIP:` line, the GNU ld legs `test result: ok. 1 passed` |
| `check-codegen-verify`, `check-fmt`, `check-documentation-write` (tree clean after), `check-documentation`, `diagnostics-inventory`, `evidence-plan-citations`, `build-cli` | exit 0 |
| `script-gate-tests` | `Ran 94 tests`, `OK (skipped=1)` |

The first gates attempt failed one test: `e2e_aarch64_elf_tlsie`
`native::local_exec_tls_in_a_linker_steered_shared_object_is_refused`. The
spawn of its freshly written driver script returned `ETXTBSY` ("Text file
busy"), a race with another test thread's fork that this change does not
touch. It passed in the rerun and in the two earlier gate runs of this change.
The attempt is kept as `logs/test-codegen-e2e-first-attempt.log`,
`logs/phase-gates-first-attempt.json` and `logs/gates-first-attempt.out`.

### Direct probes (records/repair/direct)

The prior CLI is this source's CLI built with `a0d5453ae`'s
`link_driver.rs` (SHA-256 `44c416be…`, the binary the previous run
qualified). "LLD" means a `cc` wrapper that runs the host `cc` with
`-fuse-ld=lld` first on `PATH` (`records/repair/inputs/lld-cc.sh.gz`). The
inputs are `gb.s` (the verifier's shape: 6,000 GOT slots, then `f_gb`
loads `dv_last` = 4242 through `LD64_GOTPAGE_LO15`), `gb_near.s` (100
slots), `gb_user.c`, `ifunc_gotpage.s` (a static `_start` that applies its
`IRELATIVE` relocations and calls an IFUNC through an `LD64_GOTPAGE_LO15`
load) and `helper.trust_ir`. Every check the harness evaluates is true
(`direct/checks.json`).

Two direct records are archived under names other than the ones
`results.json` gives their probes: `prior-readelf-S-lld-shared` (`readelf -SW`)
is `direct/prior-readelf-sections-lld-shared.txt.gz`, and
`prior-readelf-s-lld-shared` (`readelf -sW`) is
`direct/prior-readelf-symbols-lld-shared.txt.gz`. The original names differ in
case alone, which a case-insensitive filesystem (macOS's default) stores as one
file, so every macOS checkout showed one of them modified. Both were renamed
with their bytes unchanged (their `inventory.json` SHA-256 rows still match),
and the harness now gives the probes the new names.

| route | prior CLI (`a0d5453ae` driver) | this source | the linker outside the driver | near twin through this source |
| --- | --- | --- | --- | --- |
| LLD, `-shared -nostdlib --relocation-model pic -Wl,gb.o` | installs; `adrp x28, 0x89000`, `ldr x0, [x28, #15760]`; `dv_last`'s `GLOB_DAT` slot at `0x94d90`, base `0x89210`; user prints `f_gb=1904`, exit 1 | exit 1, one `relocation-out-of-range` `[TCG-LINK-GOT-PAGE-WINDOW]` (`X = 48528` from the page `0x89000`); nothing written, a file at the output keeps its bytes | user `f_gb=1904`, exit 1 | 100 slots: links, user `f_gb=4242`, exit 0 |
| LLD PIE, `-Wl,gb.o,gb_user.o` | installs; prints `f_gb=1904`, exit 1 | exit 1, one `unclassified` `[TCG-LINK-GOT-PAGE-UNPROVEN]` (`.got` ends 50447 bytes above the page of the base; the slot is filled through `RELATIVE`, so no overflow is observed) | prints `f_gb=1904`, exit 1 | links, `f_gb=4242`, exit 0 |
| LLD, `--static --nostdlib --no-pie -Wl,ifunc_gotpage.o` | installs; `adrp x28, 0x220000`, `ldr x1, [x28, #768]`; the IFUNC's `IRELATIVE` slot is in `.got.plt` at `0x230300` (`X = 66304`); SIGSEGV (139) | exit 1, one `[TCG-LINK-GOT-PAGE-UNPROVEN]` naming `myfunc` (the `IRELATIVE` target ends 66311 bytes above the page of the base) | SIGSEGV | GNU ld through this source: links, exit 42 |
| GNU ld, the same library | (not run) | exit 1, one `[TCG-LINK-GOT-PAGE-UNPROVEN]`: GNU ld's `.got` ends 49127 bytes above the page of the base, a conservative refusal | links with `dv_last`'s slot in range; user `f_gb=4242`, exit 0 | links, `f_gb=4242`, exit 0 |
| GNU ld, the same PIE | (not run) | GNU ld refuses the link ("relocation truncated to fit: R_AARCH64_LD64_GOTPAGE_LO15"), classified `relocation-out-of-range`; nothing written | refuses | links, `f_gb=4242`, exit 0 |

### The linker matrix (records/repair/kinds)

`harnesses/probe-got-base-kinds-20260923.py` links one object per aaelf64
GOT-base kind (26, plus `GOTREL64`/`GOTREL32`) through GNU ld 2.42, gold
2.42 and LLD 22.1.6. Where GNU as has no syntax, the type of a stand-in
relocation is patched. It then puts each checked form's slots out of its
window where a layout can, and decodes every written field against the
linker's own base and slot. The table is the plan's ("L02-P10 GOT-base
forms", `docs/linux-aarch64-completion.md`). Only `LD64_GOTPAGE_LO15` is
written out of its window, and only by LLD: 2,016 of the far library's
6,000 offsets were truncated; in the verifier's shape `X = 48144` was
written as 15376; and in a static IFUNC program `X = 66160` was written as
624. GNU ld refuses `LD64_GOTPAGE_LO15`, `LD64_GOTOFF_LO15`,
`MOVW_GOTOFF_G1` (IFUNC slot 8 GiB away) and `TLSDESC_OFF_G1` out of
range. gold refuses `LD64_GOTPAGE_LO15` ("relocation overflow") and stops
with an internal error on or does not recognize every other GOT-base form.
LLD recognizes no other GOT-base form. The base probes show that every
linker measures from `_GLOBAL_OFFSET_TABLE_`. That symbol is not the start
of `.got` for GNU ld's PIE and static PIE (`0x18` bytes in), nor for
gold's 6,000-slot library (`0x8000` bytes in).

### Timing (records/repair/timing)

15 interleaved rounds, the order rotated each round, of the prior CLI, this
source's CLI and an identical copy of it (the scatter control); median in
ms (quartiles, minimum):

| case | prior | current | current copy |
| --- | --- | --- | --- |
| `--shared --nostdlib` of `b1_scalars.tmbc` | 17.83 (15.72–18.95, 12.89) | 17.79 (16.09–20.55, 15.08) | 17.12 (14.96–18.98, 13.12) |
| default executable of `answer.trust_ir` | 23.78 (21.27–24.82, 17.23) | 24.92 (22.09–26.41, 18.48) | 22.74 (21.34–24.71, 17.86) |
| `--static` with `.data` at 8 MiB | 73.61 (70.58–83.36, 66.70) | 76.45 (74.47–91.03, 63.92) | 78.80 (70.69–89.22, 60.79) |

The current-over-prior median ratios (0.998, 1.048, 1.038) are within the
identical copy's scatter (0.962, 0.912, 1.031). Each of these images
defines `_GLOBAL_OFFSET_TABLE_`, so the new check reads the symbol table
and needs no trace. An image without the symbol now has its trace read.

### Mutation leg (records/repair/mutation)

Each mutant edits `link_driver.rs` once (`mutant.diff`) and runs the
`link_driver` unit tests. Mutants that can change a native result also run
the new native control with `TCG_REQUIRE_LLD=1`. A mutant counts as killed
only when a test failed, not when a build failed. All 7 are killed:

| mutant | killed by |
| --- | --- |
| `drop-gotpage-lo15` (313 not collected) | the pin test; the native control (LLD's library is installed) |
| `no-got-base-window` (every image shown) | `got_base_windows_are_checked_from_the_located_got_base`, `a_got_base_use_is_refused_by_name_out_of_the_got_base_window`, `a_traced_got_page_input_refuses_an_image_not_shown_in_reach`; the native control |
| `unlocated-base-shown` | the same three unit tests (the native images all name the symbol) |
| `no-irelative-slots` | `got_base_windows_are_checked_from_the_located_got_base` only: the native IFUNC program's `__rela_iplt_*` symbols still name its slot |
| `drop-gotoff-lo15` (310 not collected) | the pin test only (no linker on the host writes it unchecked) |
| `base-not-page` (`GOTPAGE` measured from the base) | `got_base_windows_are_checked_from_the_located_got_base`, `a_got_base_use_is_refused_by_name_out_of_the_got_base_window` |
| `section-from-base` (slots below the base missed) | `got_base_windows_are_checked_from_the_located_got_base` |

### Boundaries of the GOT-base repair

- The check trusts `_GLOBAL_OFFSET_TABLE_`. A definition an input or a
  linker script places away from the base the linker measures from is not
  seen.
- An IFUNC slot whose `IRELATIVE` relocation a linker script hid from both
  the section headers and `__rela_iplt_start`/`__rela_iplt_end` is not
  seen. No start-up code applies such a relocation.
- The check is conservative. It refuses GNU ld libraries with a GOT larger
  than 32 KiB that GNU ld wrote correctly, and every image with a GOT-base
  use whose base cannot be located (stripped, no section headers, or an
  LLD image that never names the symbol). Every image not shown in a
  GOT-base window has its linker trace read.
- The `MOVW` GOT-base forms stay exempt on the probe's evidence for these
  three linker versions. The PAuth `LO15` rows have unit controls only,
  because no linker on the host recognizes them.
- The earlier boundaries of this archive still apply.
