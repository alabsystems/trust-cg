# Traced GOT-page inputs and text-offset ceiling controls (L02-P10 residuals) on Linux AArch64, 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the change that answers the 2026-09-23 closure audit of
ledger gap L02-P10 (audit at `8ca934447`). The change is `7df1bfdf7`. The run
used clean source `7df1bfdf7c0da926c702b6d5058d6bda1c2eceef` (tree
`142076d4f2564d804010b86a55e59320fe299ab9`) on the Linux AArch64 host
(`aarch64-unknown-linux-gnu`, Ubuntu 24.04, gcc 13.3, GNU ld, readelf, ar and
objdump 2.42, stock Rust 1.97.1). `git status --porcelain
--untracked-files=all` was empty before the run, after the direct probes,
after the timing leg and after the mutation legs, which restore their file.
`records/results.json` holds the run's full record:

- provenance, and tool paths and hashes;
- the `trust-cg` binary hash;
- every gate's `test result:` lines;
- every probe's exit code and output;
- the timing samples;
- each mutant's failing tests, with each panic's location and message.

L02-P10 stays **PARTIAL**. A separate adversarial audit decides closure. This
is execution and object evidence on one host, not a proof.

## What the audit left open

1. **The GOT-page window check read only positional inputs.** `run_link`
   took its uses from `got_page_uses(&request.objects)`, and
   `got_page_window_output_refusals_for` refused nothing when there were
   none. The audit linked the archived `pic` object `got_page.o` into
   `trust-cg -shared -nostdlib --relocation-model pic
   -Wl,--section-start=.got=0x200000000,--section-start=.got.plt=0x200010000
   -o libbypass.so b1_scalars.tmbc` three ways: as `-Wl,got_page.o`, as
   `-l :got_page.o`, and as a `--whole-archive` member. Each exited 0, and a
   user of the library died with SIGSEGV.
2. **The text-offset ceilings had no control.** No test triggered the u32
   block-offset, jump-table u32, jump-table `ADR` imm21 or u32 LSDA
   refusals.

## The change

- `examine_input_trace` reads each loaded AArch64 ELF relocatable object
  once, for both its local-exec and its GOT-page `ADRP` uses.
- The staged image is checked first. The trace is examined at most once,
  and only when the image is not a confirmed executable (the local-exec
  check) or not shown to keep every GOT-page `ADRP` in reach. There is no
  second trace pass.
- Every GOT-page use in a positional or traced input refuses an image not
  shown in reach by name (`[TCG-LINK-GOT-PAGE-WINDOW]`,
  `[TCG-LINK-GOT-PAGE-UNPROVEN]`, `[TCG-LINK-GOT-PAGE-UNCHECKED]`). A trace
  that does not show what was loaded refuses such an image with
  `[TCG-LINK-INPUT-TRACE]`.
- A plain (untraced) executable link must now be `-nostdlib`, because the
  host's C start files carry GOT-page `ADRP`s. Every link with the C runtime
  is staged and traced.
- The four u32 domain checks go through one helper. A unit-test-only
  synthetic text prefix lets unit tests drive each check inside a real
  compile.

`CHANGELOG.md` and the plan section "L02-P10 closure-audit residuals" of
`docs/linux-aarch64-completion.md` list the controls.

## Gates (records/logs)

| log | result |
| --- | --- |
| `test-codegen-lib` | 4129 passed, 1 ignored (base 4122, plus 7 new) |
| `test-e2e_aarch64_link_runtime` | 32/32 |
| `test-e2e_aarch64_elf_tlsie` | 13/13 |
| `test-e2e_aarch64_switch` | 2/2 |
| `test-cli-all` | CLI bin 30/30; `link_options` 23/23 (20 plus the 3 `linux_got_page` controls); `output_paths` 8/8; `trust_ir_binary_container` 4/4; every other target ok |
| `check-codegen`, `check-codegen-verify`, `check-lower` | exit 0 |
| `check-fmt`, `script-gate-tests` (94, OK, 1 skipped), `native-test-host-matrix`, `check-documentation`, `diagnostics-inventory`, `evidence-plan-citations` | exit 0 |

## Direct probes (records/direct)

The probes ran in a scratch directory (`$WORK`) with the binary built from
the clean source. The inputs are in `records/inputs`. `got_page.o` and
`got_page.tmbc` are the ones the got-page-region run retained
(`records/repair`), and `desc_main.c` is its user (`records/direct/cg`), all
byte-identical. `b1_scalars.tmbc` is the conformance fixture the audit used.

| probes | result |
| --- | --- |
| `readelf-r-got_page.o` | `R_AARCH64_TLSDESC_ADR_PAGE21` against `tcg_desc_tls` and `R_AARCH64_ADR_GOT_PAGE` against `tcg_desc_word` |
| `cli-audit-{wl,lcolon,whole}` | The audit's three commands at current source: exit 1, exactly two `error[link:relocation-out-of-range] … [TCG-LINK-GOT-PAGE-WINDOW] got_page.o` (`./got_page.o`, `libarch.a(got_page.o)`) lines, no `libbypass_*.so`; the listing is unchanged |
| `raw-gnu-ld-{wl,lcolon,whole}`, `run-user_raw_*` | GNU ld links the same inputs outside the driver (exit 0), and the user dies with SIGSEGV (139) each time |
| `objdump-libraw_wl`, `readelf-r-libraw_wl` | The unchecked library's `tcg_desc_bump` holds `adrp x0, 10000` and `adrp x1, 0` for the TLSDESC slot at `0x200010018` and the `GLOB_DAT` slot at `0x200000008`: the truncated deltas the audit reported |
| `cli-audit-near`, `run-user_near` | The `-Wl` command with `.got` at 2 GiB links, and the user exits 0 |
| `cli-route-{wl,colon,member,whole,thin,input,group,startgroup}` | Eight routes for `gp/got_page.o` into a `--shared --nostdlib` library of `caller.trust_ir` with `.got` 8 GiB away. Each: exit 1, exactly two `error[link:` lines, each saying the linker loaded the input although it is not a positional input; the listing is unchanged |
| `raw-route-*`, `run-user_gpraw_*` | GNU ld links every route outside the driver, and every user dies with SIGSEGV (139) |
| `cli-near-*`, `run-user_gpnear_*` | With `.got` at 2 GiB every route links through the driver, and every user exits 0 |
| `gnu-ld-trace-default-link`, `readelf-r-start-file-*` | GNU ld's trace of a default executable link names `Scrt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o` and `crtn.o`. Their `R_AARCH64_ADR_GOT_PAGE` relocations are against `main`, `__gmon_start__`, `_ITM_deregisterTMCloneTable`, `_ITM_registerTMCloneTable` and `__cxa_finalize` |
| `raw-crt-far`, `run-crt_raw` | A default executable linked by `cc` with `.got` at 8 GiB and `.data` at 2 GiB links (exit 0) and dies with SIGSEGV (139) |
| `cli-crt-far` | The same link through the CLI: exit 1. `Scrt1.o` (`main`) is refused as `[TCG-LINK-GOT-PAGE-UNPROVEN]`, and `crti.o` (`__gmon_start__`) and `crtbeginS.o` (three uses) as `[TCG-LINK-GOT-PAGE-WINDOW]`. Nothing is written |
| `cli-crt-near`, `run-crt_near` | With `.got` at 2 GiB the executable links and returns 42 |
| `cli-crt-far-verbose` | Adding `-Wl,--verbose` puts other text in the trace. The image is refused with the five uses and exactly one `[TCG-LINK-INPUT-TRACE]`, which names the GOT-page reason |

## Timing (records/timing)

The timing leg built the CLI with the base link driver (`dbec0925f`'s
`link_driver.rs`, everything else from this source) and restored the source.
It then ran each case 21 times, interleaved per round, with both debug
binaries:

| case | base median | current median | ratio |
| --- | --- | --- | --- |
| default `trust-cg --format=text -o prog answer.trust_ir` (base: direct link; current: staged and traced) | 23.33 ms | 23.34 ms | 1.001 |
| `--shared --relocation-model pic` of `b1_scalars.tmbc` (traced in both) | 21.12 ms | 22.61 ms | 1.071 |

The interquartile ranges overlap: default 21.0 to 24.8 ms (base) and 22.4 to
26.0 ms (current); shared 19.4 to 24.2 ms and 20.3 to 24.5 ms. The minimums
differ by about 2 ms in both cases (17.4 and 19.3 ms; 16.7 and 18.5 ms).
That is a plausible measure of the added staging, trace output, image
read-back and layout check. With 21 samples on one host this is not a
precise cost, only evidence that the change adds no second link or trace
pass.

## Mutation legs (records/mutation)

Each mutant edits one source file (`mutant.diff`), runs the named tests
(`*.log`) and restores the file. A mutant counts as killed only when a test
failed, not when a build failed.

| mutant | killed by |
| --- | --- |
| `no-traced-got-page` (the check ignores traced uses, as at base: the route-coverage mutant) | All three `link_options` `linux_got_page` controls. The route test fails at its first route (`wl: trust-cg: linking … libgp_wl.so`, the link succeeds), the audit reproducer and the C-runtime test likewise. Also `a_traced_got_page_input_refuses_an_image_not_shown_in_reach` |
| `got-page-check-reads-no-trace` (the trace is read only for a non-executable image, the local-exec condition) | `c_runtime_got_page_adrps_are_checked_in_an_executable` (the executable is installed); the scripted unit test. The shared-library routes still pass, because the local-exec condition reads their trace |
| `no-member-bytes` (member lines are resolved, but no member is read) | The route test passes `wl` and `colon` and fails at `member` (`link_options.rs:2139`: `member: trust-cg: linking … libgp_member.so`). `results.json` records `member_route_kill: true`, which the harness requires |
| `c-runtime-link-plain` (a link with the C runtime counts as plain, as at base) | Unit tests only: `traces_link_inputs_selects_every_linux_link_but_the_plain_executable`, `traced_links_pass_the_trace_before_every_passthrough` and the scripted test. The native C-runtime control uses `-Wl` placement, which is traced either way. A default link with no `-Wl` cannot place its GOT far without a multi-GiB input |
| `got-page-trace-problems-ignored` | The scripted unit test (the executable with an unreadable trace must get `[TCG-LINK-INPUT-TRACE]`) |
| `no-traced-got-page-missing-output` | `a_traced_link_that_writes_nothing_is_refused_only_for_a_checked_input` |
| `no-imm21-check` | `a_jump_table_adr_past_the_imm21_window_is_refused_in_a_real_compile`. Without the named check, `encode_adr`'s own signed-immediate check still refuses the compile with a generic message (`encoding failed: … signed immed…`), so the named check adds the exact refusal but no wrong code was possible |
| `no-u32-block-check` | `the_u32_block_offset_ceiling_is_refused_at_its_edge` (the instruction check refuses instead) |
| `no-u32-instruction-check` | `the_u32_instruction_offset_ceiling_is_refused_at_its_edge` (the compile succeeds) |
| `no-u32-jump-table-check` | `the_u32_jump_table_offset_ceiling_is_refused_at_its_edge` (the compile succeeds) |
| `no-u32-lsda-check` | `the_u32_lsda_code_length_ceiling_is_refused_at_its_edge` (the compile succeeds) |

All 11 mutants are killed. `rebuild-after-mutants` rebuilt the CLI from the
restored source.

## Boundaries

- The u32 ceilings are driven by a unit-test-only synthetic prefix inside
  real compiles, not by a 4 GiB function. The imm21 window is reached by a
  real function of about 1 MiB.
- Not examined:
  - a plain `-nostdlib` executable link (its inputs are only positional);
  - non-Linux ELF targets (not traced);
  - shared libraries, which apply no relocation to the link;
  - a file replaced between the link and the read of the trace's files;
  - code a linker plugin generates without a traced file;
  - a file a linker writes at another path;
  - links made outside the driver.
- The image check keeps the blind spots `LIMITATIONS.md` lists, for example
  a linker-filled slot in allocated zero fill that no relocation names.
- Every Linux link with the C runtime is now staged. It refuses a
  non-regular output such as `/dev/null`, needs a writable output directory,
  replaces a symlink at the output, and can leave a 0700 `.tcg-link-*`
  directory if it is killed.
- The trace model is GNU ld 2.42 (and LLD 22, from the L02-P9 run) on this
  host. Only GNU ld was run here.
