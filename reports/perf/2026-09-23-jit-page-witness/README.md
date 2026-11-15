# Kernel page-protection witness in the installed JIT binding — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record retains two runs for audit row L11-P6's page-protection
increment on the Linux AArch64 host (Linux 6.17 aarch64, NVIDIA Grace, 20
cores). The stock Rust 1.97.1 toolchain and the pinned AY/Clean package
prefix were on `PATH`, and every Cargo command used `--locked --offline`.

1. The first run, at `2130afa5852029607f4852d8bfca2fb373202d17`
   (`records/HEAD.txt`, origin/main `9984dbb55` plus the change), is kept
   below as it was taken. Its single passing library run did not establish
   the library gate: review found that the parallel library suite at that
   commit failed in 5 of 9 runs.
2. The repair run, at the commit in `records/repair/HEAD.txt`, is the
   qualifying run for the current code. It is described first.

The change adds a `PageProtectionWitness` to `ExecutableMemoryProtection`.
On Linux the JIT observes the whole allocation through `/proc/self/maps`
right after the read-execute seal. Three installed routes observe it again
before any code byte is read: `get_contract_symbol_bound`,
`native_install_gate_packet(_for_surface)` and `into_installed_artifact`.
They refuse by name:

- `[TCG-JIT-PAGE-WITNESS-WX]` for a writable-and-executable observation.
- `[TCG-JIT-PAGE-WITNESS-MISMATCH]` for any other difference from the
  recorded `r-xp`.
- `[TCG-JIT-PAGE-WITNESS-UNCOVERED]` for an uncovered range.
- `[TCG-JIT-PAGE-WITNESS-UNREADABLE]` for an unreadable or malformed answer,
  or no consistent text read after the last retry.

`InstalledArtifact::entrypoint`, `entrypoint_ptr` and
`ensure_published_entrypoint_ptr` (and the Petri handoff through
`entrypoint_ptr`) do not observe the kernel again, and raw `ExecutableBuffer`
lookups never do.

Resealed forgeries are refused by name as well: a foreign source gets
`[TCG-JIT-PAGE-WITNESS-SOURCE]` and a forged recorded string gets
`[TCG-JIT-PAGE-WITNESS-RECORDED]`. The installed binding is v6 and the
manifest `trust-cg.artifact/v3`.

## Repair: torn `/proc/self/maps` reads

The first version read `/proc/self/maps` once and refused the whole file on
any row that started before its predecessor ended. The kernel builds that
text chunk by chunk (about a page per `read()`) and drops the mm lock between
chunks. When another thread grows a malloc arena or maps, unmaps or protects
memory between two chunks, one read lists a VMA twice, for example
`fc5109574000-fc5109578000 rw-p` followed by `fc5109574000-fc5109580000
rw-p`. Such a read can show a combination of states that never held at one
instant. Compile-service executables were then refused at random, at
publication (`compile.page_protection_witness`) or at lookup.

The repair:

- asks the `PROCMAP_QUERY` ioctl on an open `/proc/self/maps` first (Linux
  6.11 and later). Each call returns one VMA, which the kernel documents as
  self-consistent. A range inside one VMA, as a published allocation is, is
  therefore one kernel answer; a range across several VMAs is several
  successive answers with no joint guarantee. `ENOTTY` is remembered and the
  text reader answers instead.
- makes the text reader retry the whole file, up to 16 times, when a row at
  or after the range overlaps or goes back behind its predecessor, or when
  the range is not covered. Disorder wholly below the range, before any of
  it is covered, cannot affect its coverage and is tolerated. A malformed row
  or an I/O error is refused at once. After the last attempt the reader
  refuses by name. An accepted text read has ordered rows covering the
  range, each true at some moment during the read, not necessarily all at
  once.

### Repair results

| Record (`records/repair/`) | Scope | Result |
| --- | --- | --- |
| `lib-parallel-run01..12.log.gz` | `cargo test -p trust-cg-codegen --lib`, default parallel mode, 12 consecutive runs | 12/12: 4,082 passed, 0 failed, 1 ignored (the pre-existing `raw_machir_request_cache_real_exhaustive_campaign`) |
| `lib-serial.log.gz` | the same suite with `--test-threads=1` | 4,082 passed, 0 failed, 1 ignored |
| `jit_wx_refusal-run1..5.log.gz` | the touched floor target, `--nocapture`; runs 1-2 `--test-threads=1` (the floor's mode), runs 3-5 parallel | 5/5: 10 passed, 0 failed (9 before; 1 new churn row) |
| `affected-targets.log.gz` | `wp0_artifact_bytes_unchanged`, `jit_install_gate`, `jit_contract_artifact`, `compile_service_async_api`, `jit_teardown_policy`, `jit_cross_thread_execute_mode`, `jit_runtime_hardening`, `jit_icache_coherence`, `--test-threads=1` | all pass: 6, 89, 26, 33, 5, 1, 4 and 3 tests |
| `affected-targets-parallel.log.gz` | `jit_install_gate`, `compile_service_async_api`, `jit_contract_artifact`, 5 parallel runs each | 15/15 pass |
| `cargo-check.log.gz` | `cargo check -p trust-cg-codegen` (default, `--features verify`, `--no-default-features`, `--tests`); `-p trust-cg-jit-matrix -p trust-cg-cli --all-targets` | all pass, no warnings |
| `check-fmt.log.gz`, `doc-checks.log.gz`, `script-tests.log.gz` | `scripts/check_fmt.sh`; documentation, diagnostics-census, host-matrix and plan-citation checks; Linux, Darwin and bridge gate script tests | all pass; 94 script tests, OK (1 skipped) |

The library suite line, identical in all 12 parallel runs apart from time:

```
test result: ok. 4082 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.77s
```

The touched target, run 1:

```
test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 11.99s
```

The churn row prints one summary line per run. In the five qualifying runs
the eight churn threads made 600,236 to 665,879 mapping/allocation rounds
each; 39 to 67 of 2,000 raw text reads per run were torn; the test installed
64 executables, made 512 contract lookups (all answered by `PROCMAP_QUERY`)
and 4,000 text-reader observations, with 0 refusals. No text-reader
observation needed a retry in these runs: the torn rows fell below the
allocation, where they are tolerated. The retry itself runs live in mutation
M7 below, and in the library tests.

### Repair controls (mutations, not committed; diffs retained)

Each mutation was applied to `jit_page_witness.rs` at the repair commit's
source, run, and reverted. The `.diff.gz` next to each log is the exact
change.

| Mutation | Runs | Result |
| --- | --- | --- |
| T1: no `PROCMAP_QUERY` (every observation, including the compile service's, uses the retrying text reader) | library suite 10x parallel; `jit_wx_refusal` 3x | 10/10 library runs pass (4,082); `jit_wx_refusal` 3/3 pass, churn row 0 refusals with 512 text-read lookups |
| M5: T1 plus the first version's parser (any disorder refused) and no retry | churn row 3x | 3/3 fail: 129 spurious lookup refusals in run 1 ("no consistent /proc/self/maps snapshot ... after 1 read(s)"); runs 2 and 3 fail at publication (`compile.page_protection_witness`) |
| M6: T1 with the below-range tolerance but no retry | churn row 3x | 3/3 pass, 0 refusals |
| M7: T1 with retry but without the below-range tolerance | churn row 3x | 3/3 pass, 0 refusals; 87 to 137 of 4,000 text reads needed a retry, at most 4 attempts |

So the churn row detects the first version's defect, and on this host either
defence alone removed the spurious refusals under this churn. The shipped
code has both, and uses `PROCMAP_QUERY` where the kernel has it.

### Repair evidence boundary

This is execution evidence on one Linux 6.17 AArch64 host, not proof. No
observation shows the whole process at one instant. The churn row shows no
spurious refusal in these runs; it does not bound the retry's failure rate
under heavier churn, and a text read that stays torn for 16 attempts is
refused by name, not accepted. The ioctl's cost per lookup (one `open` and
normally one `ioctl`) and the text reader's cost (proportional to the number
of mappings) were not measured. The earlier boundary below still applies,
corrected: a protection changed and restored between two observations, or
changed after one, is not detected, and raw installed and buffer lookups are
not re-checked. The full 145-target Linux floor was not re-run for the repair
either (the shared disk had about 12 GB free); the eight JIT and
compile-service targets above and the touched floor target were. The
Darwin and x86-64 Linux arms, including the `PROCMAP_QUERY` encoding on
x86-64, did not run.

## First run at 2130afa58 (superseded library claim)

## Results

| Record | Scope | Result |
| --- | --- | --- |
| `codegen-lib.log.gz` | `cargo test -p trust-cg-codegen --lib`, one run | 4,078 passed, 0 failed, 1 ignored. One run only: at this commit the parallel suite failed in 5 of 9 review runs on torn `/proc/self/maps` reads, so this line does not establish the gate. See the repair run above. |
| `jit_wx_refusal.log.gz` | the touched floor target, `--nocapture --test-threads=1` | 9 passed, 0 failed (4 before; 5 new rows) |
| `affected-targets.log.gz` | 39 integration targets that use manifests, the compile service, installed artifacts or JIT contracts, `--test-threads=1` | 38 targets pass with 471 tests (5 of them compile to 0 tests on this host); `ay_sat_bcp_install_gate` fails 0/2 |
| `floor-jit-batch{1,2,3}.log.gz` | 18 more required-floor targets whose sources reach the JIT or its contracts | 18/18 pass, 119 tests; the counts equal the 2026-09-23 floor run at `d5b5e5382` |
| `cargo-check.log.gz` | `cargo check -p trust-cg-codegen`, `--features verify`, `--no-default-features` | all pass |
| `check-fmt.log.gz`, `doc-checks.log.gz` | `scripts/check_fmt.sh`; `check_documentation.py --check`, `native_test_host_matrix.py --check`, `generate_diagnostics_inventory.py --check` | all pass |
| `script-tests.log.gz` | Linux, Darwin and bridge gate script tests | 94 run, OK (1 skipped) |

The libtest line of the touched target:

```
test result: ok. 9 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.57s
```

The single library suite line (not a gate result; see above):

```
test result: ok. 4078 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 4.75s
```

`ay_sat_bcp_install_gate` fails before the binding is built. The fixture
compile is refused with `compile.backend`: proof promotion has no mapping for
`StpPreIndex`/`LdpPostIndex` (the known PROOF-465 pair-opcode wall). The same
two failures reproduce with the `trust-cg-codegen` sources checked out from
`9984dbb55` (`base-9984dbb55-ay_sat_bcp_install_gate.log.gz`), so they
predate this change. The Linux floor does not include that target.

### Negative controls (mutations, not committed)

Each mutation was applied to `compile_service.rs` at this commit, run, and
reverted. Only the logs were retained, not the diffs, so these four cannot be
replayed exactly from the archive:

| Mutation | Result |
| --- | --- |
| M1: drop the lookup re-read (`validate_live_page_protection_witness`) | the library lookup test and `jit_wx_refusal` both die with SIGSEGV: lookup reaches the RW page |
| M2: drop the writable-and-executable check | `jit_wx_refusal` fails its mprotect row (RWX reported as a mismatch); the library forgery and lookup tests fail |
| M3: ignore the publication-witness result | the library publication row fails: the compile is still refused by the manifest-protection comparison, but not by the named witness diagnostic |
| M4: skip the sealed-witness check | the library forgery test fails: forged witnesses fall through to the generic contract mismatch |

### What the controls cover

- Positive: a raw published buffer's publication observation and a fresh
  kernel read are both `r-xp` over exactly the allocation. An installed
  binding carries the Linux kernel witness, equal to the target contract and
  the manifest, and lookup by name runs the code.
- Negative, live kernel: the test `mprotect`s the installed allocation to RW,
  RWX, no access and read-only. Each lookup is refused by name before any
  byte is read, and lookup works again once the allocation is back to RX. Page zero and a
  kernel-half address are refused as uncovered.
- Negative, forged: resealed bindings with a forged recorded protection, a
  changed source, or a forged, mixed or missing observation are refused by
  name (library tests using the `cfg(test)` reseal hook). Through the public
  API the same forgeries are refused by the binding's private seal. A v5
  binding and a v2 manifest are refused.
- Negative, injected kernel answers (library tests, thread-local maps hook):
  uncovered, mixed, malformed and RWX answers at lookup, and an uncovered
  answer at publication.

### Evidence boundary

This is execution evidence on one host, not proof. The first version's text
said each `/proc/self/maps` read shows the kernel's state at one instant;
that was false (see the repair section). A protection changed and restored
between two observations, or changed after one, is not detected. Raw
installed and buffer lookups and raw pointers are not re-checked. The witness
covers the code allocation, not the separate read-write data image. Thread
and execution-lease context is not bound, so L11-P6 stays PARTIAL. The
Darwin (recorded-only) and x86-64 Linux arms compile from the same source but
did not run here. The full 145-target Linux floor was not re-run for this commit:
each debug integration binary is about 0.5 GB and the shared disk had about
22 GB free. Instead, the run covered the 23 floor targets whose sources reach
the JIT or its contracts. Five of them ran in the affected set:
`jit_wx_refusal`, `jit_exception_handling`, `jit_icache_coherence`,
`jit_teardown_policy` and `e2e_aarch64_globals_linux`. The other 18 ran in
the three batches:

- `core_jit_planning`, `jit_cert_cache_identity_aarch64`,
  `jit_cross_thread_execute_mode`, `jit_fail_closed_proof_policy`,
  `jit_runtime_hardening` and `jit_source_bound_arithmetic`.
- `aarch64_call_result_liveness`, `aarch64_value_decode_native`,
  `abi_definition_refusals`, `aggregate_call_results`,
  `e2e_aarch64_elf_relocation_model` and `multi_result_call_abi`.
- `aarch64_elf_symbol_binding`, `aarch64_final_layout_crosscheck`,
  `e2e_aarch64_elf_sections`, `e2e_aarch64_host_target_authority_linux`,
  `e2e_aarch64_stack_probe_native` and `e2e_fp_to_int_saturation`.
