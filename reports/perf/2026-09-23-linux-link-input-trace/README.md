# Traced link inputs and CLI link modes (L02-P9 residuals) on Linux AArch64, 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the change that answers the 2026-09-23 closure audit of
ledger gap L02-P9 (audit at `57f35f51d`). The change is `c624786da`. The
records here are from the re-run at the 2026-09-23 repair (see
[Repair](#repair-2026-09-23) below) on clean source
`dafd676098a17671409e4b9214c4ecc805fd40ec` (tree
`5d1a8c28dc7197df876e6e7d68500b119be2294a`). Its only source difference from
`c624786da` under `crates/` is a doc comment in `trust-cg-cli/src/main.rs`;
the rest is documentation and this run's harness. The run used the Linux AArch64 host
(`aarch64-unknown-linux-gnu`, Ubuntu 24.04, gcc 13.3, GNU ld/readelf/ar 2.42,
LLD 22.1.6, stock Rust 1.97.1). `git status --porcelain --untracked-files=all`
was empty before the run, after the direct probes, and after the mutation
legs restored their file. `records/results.json` records the provenance, the
tool paths and hashes, the `trust-cg` binary hash, every gate's
`test result:` lines, every probe's exit code and output, and the mutants
with each failing test's panic location and message.

L02-P9 stays **PARTIAL**. A separate adversarial audit decides closure. This
is execution and object evidence on one host, not a proof.

## What the audit left open

1. The local-exec TLS guard was not fail-closed on the driver's own options.
   Only positional AArch64 ELF relocatable inputs were scanned. At the
   previous repair, `trust-cg --shared --relocation-model pic -o libtcgwl.so
   -Wl,le.o tls_reader_thread.tmbc` exited 0, and a user with its own
   thread-local exited 236 instead of 42. Those records are in
   [the output-guard run](../2026-09-23-linux-tls-model-output-guard/README.md),
   `records/repair-3/direct/cli-route-wl.txt.gz` and `run-user_wl.txt.gz`.
2. The CLI binary had not linked and run `--pie`, `--no-pie`, `--static`
   or `--nostdlib` at current source.
3. The TEXTREL control did not pin its subject and had no twin without
   `-z text`.

## The change

- `link_driver::run_link` stages every Linux link that is not a plain
  executable link (every `--shared` link, and every link with `-l` or `-Wl`)
  and runs it with `-Wl,--trace,--trace` as the C driver's first argument.
  When the staged image is not an executable or relocatable object, every
  AArch64 ELF relocatable object the trace names is read, archive members
  from the archive. A local-exec relocation in any of them refuses the image
  with `[TCG-LINK-TLS-MODEL]`, naming the loaded input. A trace that does
  not show what was loaded is refused with `[TCG-LINK-INPUT-TRACE]`.
- Both scans read `SHT_REL` sections as well as `SHT_RELA` (see the
  `SHT_REL` probe below).
- New and strengthened controls are listed in `CHANGELOG.md` and in the
  plan section "L02-P9 closure-audit residuals" of
  `docs/linux-aarch64-completion.md`.

## Gates (records/logs)

| log | result |
| --- | --- |
| `test-cli-all` | `link_options` 20/20; CLI bin 30/30; `output_paths` 8/8; `trust_ir_binary_container` 4/4; every other target ok |
| `test-e2e_aarch64_elf_tlsie` | 13/13 |
| `test-e2e_aarch64_link_runtime` | 32/32 |
| `test-codegen-lib` | 4122 passed, 1 ignored |
| `check-codegen`, `check-codegen-verify`, `check-lower` | exit 0 |
| `check-fmt`, `script-gate-tests` (94, OK, 1 skipped), `native-test-host-matrix`, `check-documentation`, `diagnostics-inventory`, `evidence-plan-citations` | exit 0 |

## Direct probes (records/direct)

The probes ran in a scratch directory (`$WORK`) with the binary built from
the clean source. The modules `tls_lib.tmbc`, `tls_prog.tmbc`,
`tls_user.tmbc` and `tls_reader_thread.tmbc` are the ones retained by the
output-guard run (same bytes; `records/inputs`). `le/tcgtls.o` is
`tls_lib.tmbc` compiled with the `static` model (local-exec), and
`pic/tcgtls.o` is the same module with the `pic` model (TLS descriptors).

| probes | result |
| --- | --- |
| `trace-gnu-{member,thin,input,wl}` | Outside the driver, GNU ld 2.42 links each route into a `-shared` library (exit 0). Its trace names the archive member as `(le/libtcgarc.a)tcgtls.o`, the thin member as `le/tcgtls.o`, and the `INPUT()` file by its path |
| `trace-lld-{member,thin,input,wl}` | LLD 22 refuses each route itself (exit 1). Its trace names members as `le/libtcgarc.a(tcgtls.o)` and `le/libtcgthin.a(tcgtls.o)` |
| `cli-route-{wl,lcolon}` | The audit's two commands at current source: exit 1, exactly one ``error[link:tls-model-mismatch] `tcg_cli_tls` (R_AARCH64_TLSLE_ADD_TPREL_HI12): [TCG-LINK-TLS-MODEL] le.o: …`` (`./le.o` for `-l :le.o`), and the image removed |
| `cli-route-{member,whole,thin,input,group,startgroup}` | The same for an archive member by reference and whole, a thin member, `INPUT()`, `GROUP()` and `--start-group` |
| `state-after-refused-routes` | The scratch listing is identical before and after the eight refused links |
| `cli-pic-*` → `cli-user-*` → `run-user_*` | Each route with the `pic` object links, and the user exits **42** (eight of eight) |
| `cli-trace-{verbose,map}` | `-Wl,--verbose` and `-Wl,-M` put other text in the trace: exit 1 with exactly one `error[link:unclassified]: [TCG-LINK-INPUT-TRACE] …` |
| `cli-mode-*`, `readelf-{h,l,d}-mode_*`, `run-mode_*` | default and `--pie`: `DYN (Position-Independent Executable file)` with `INTERP`. `--no-pie`: `EXEC` with `INTERP`. `--static`: `EXEC` with no `INTERP` and no `DYNAMIC`. `--nostdlib` (with `-Wl,start.o`, a `_start` that exits with `main`'s value): PIE with `INTERP`. `--nostdlib --static`: `EXEC` with no `INTERP`. Each exits **42** |
| `cli-mode-shared-pie` | `--shared --pie` is refused by name before anything runs |
| `cli-mode-static-dynonly`, `run-dynamic_dynonly` | `--static` against a library that exists only as `dyn/libtcgdynonly.so` gives exactly one `` error[link:library-not-found] `tcgdynonly` ``; the dynamic twin exits **42** |
| `readelf-r-le_rel.o`, `outside-cc-shared-le_rel`, `objdump-librel_raw.so`, `cli-route-sht-rel` | `le/tcgtls.o` with its relocation sections rewritten as `SHT_REL` links through `cc -shared` outside the driver (exit 0). The library's `tcg_cli_tls_bump` computes `tpidr_el0 + 0x10`, an offset into the executable's TLS block. `trust-cg -Wl,le_rel.o` refuses it (exit 1) |
| `textrel-z-text`, `textrel-twin`, `readelf-d-textrel_twin`, `run-textrel_twin` | Under `-z text` GNU ld names ``relocation against `puts@@GLIBC_2.17' in read-only section `.rodata'``. The twin without `-z text` links, `readelf -d` shows `TEXTREL` and `FLAGS TEXTREL BIND_NOW`, and it exits 0 |

## Mutation legs (records/mutation)

Each mutant edits `crates/trust-cg-codegen/src/link_driver.rs`
(`mutant.diff`), runs the named tests (`*.log`), and restores the file. A
mutant counts as killed only when a test failed, not when a build failed.

| mutant | killed by |
| --- | --- |
| `no-trace` (a Linux link is never traced) | `link_options` 18/20 (the eight-route and unreadable-trace controls fail); `native::traced_archive_members_are_read_from_gnu_ld_and_lld` |
| `no-archive-members` (member lines are not resolved) | Fail-closed kills only, not a leak. `local_exec_objects_on_every_link_route_are_refused_by_name` fails at its first route, `wl`, which involves no archive: the refusal gains a second error, `[TCG-LINK-INPUT-TRACE]` for the C driver's own `(/usr/lib/gcc/aarch64-linux-gnu/13/libgcc.a)_divdi3.o` trace line, so the one-error assertion fails (`left: 2, right: 1`, `link_options.rs:1090`). `input_trace_examination_reads_every_loaded_relocatable` fails because each member line becomes a named problem. Under this mutant every member, whole, thin and group route would still be refused, so this mutant shows no member-route control detecting a leak |
| `no-member-bytes` (member lines are resolved, but no copy of a member is read; added at the repair) | A leak, detected at the member routes. `local_exec_objects_on_every_link_route_are_refused_by_name` passes `wl` and `lcolon`, then fails at `member` because the link succeeds (`!output.status.success()`, `link_options.rs:1088`: `member: trust-cg: linking 1 object file(s) -> libtcg_member.so`). `native::traced_archive_members_are_read_from_gnu_ld_and_lld` fails because the GNU ld leg returns `Ok(LinkSuccess)` for `le libregular.a` (`e2e_aarch64_elf_tlsie.rs:1360`). `input_trace_examination_reads_every_loaded_relocatable` finds only the loose `le.o` use and none of the three member uses. `results.json` records `member_route_kill: true`, which the harness requires |
| `no-sht-rel` (`SHT_REL` is not read) | `native::sht_rel_local_exec_is_refused_like_sht_rela`; `sht_rel_relocations_are_read_like_sht_rela` |
| `skip-every-positional` (a positional object the pre-link scan could not read is skipped) | `an_unreadable_input_trace_is_a_named_problem` |

5 of 5 mutants are killed; for `no-archive-members` the kills are fail-closed
refusals, not leak detection (see its row). Each leg's `panics` field in
`results.json` gives the exact failure. `rebuild-after-mutants` rebuilt the CLI from the
restored source.

## Boundaries

- Not examined: a plain executable link, whose only non-positional inputs
  are the C driver's own start files and libraries; a file replaced between
  the link and the read of the trace's files; code a linker plugin generates
  without a traced file (LLD's in-memory LTO); a file a linker writes at
  another path; links made outside the driver.
- The GOT-page window check still reads positional inputs only.
- On Linux every link other than a plain executable link is staged: every
  `--shared` link, every link with `-l` or `-Wl`, and every link with a
  positional input the AArch64 ELF reader cannot read, which includes every
  non-AArch64 link. Each such link refuses `-o /dev/null` (a non-regular
  output), needs a writable output directory, replaces a symlink at the
  output, and can leave a 0700 `.tcg-link-*` directory if it is killed.
- The trace formats are those of GNU ld 2.42 and LLD 22 on this host.
- `scripts/check_panic_clippy.sh --package trust-cg-codegen` was red before
  this change: its baseline has 0 entries for `link_driver.rs`, while five
  production sites already exist at base `306912d63`. It is red after it with
  the same five sites. This change adds none.

## Repair (2026-09-23)

A review of `c624786da` and this archive found two defects in how they were
stated, not in the code. First, `LIMITATIONS.md` still said that only links
with a local-exec or GOT-page `ADRP` input are staged and that other links
write the output directly. It now states the staging scope above and that the
staging consequences apply to every staged link. The CHANGELOG, README, plan
and the CLI's `link()` doc comment name the unreadable-input group too.
Second, this README and the ledger note had presented the `no-archive-members`
kill as member-route evidence. The earlier run's
`link_options-routes.log.gz` showed the kill at route `wl`, as described in
the mutation table. The harness now adds `no-member-bytes`, records each
leg's panics, and qualifies only when `no-member-bytes` fails the route test
at `member`. The whole run (gates, probes, mutants) was repeated on clean
`dafd67609`, and its records replace the earlier run's. Every direct-probe
record and input is byte-identical to the earlier run's; the gate results
are the same counts.

## Files

- `harnesses/qualify-link-input-trace-20260923.py`: the qualifying run
  (gates, probes, mutants).
- `harnesses/archive-link-input-trace-20260923.py`: copies the run's
  records here gzip-compressed and writes `inventory.json`.
- `records/results.json`, `records/logs/*.log.gz`,
  `records/direct/*.txt.gz`, `records/mutation/*/*.gz`, and
  `records/inputs/*.gz` (modules, the probes' objects `le-tcgtls.o`,
  `pic-tcgtls.o` and `le_rel.o`, and sources).
