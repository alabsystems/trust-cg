# L04-P11 switch and indirect-call controls, register-copy binding — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record qualifies the L04-P11 increment described in
docs/linux-aarch64-completion.md
(section "L04-P11 switch and indirect-call controls, register-copy binding"):
Linux-executed switch and indirect-call controls at O0–O3, and the function
verifier binding AArch64 register copies to their decoded-word forms instead
of exempting them. Ledger gap L04-P11 stays OPEN (see "Evidence boundary").

The source is this branch's commit sequence on base `f3da1fb17`:

| Commit | Content |
| --- | --- |
| `ddf6cba83` | native controls; Linux floor `TARGET_MINIMUM_PASSES`; Darwin pins |
| `fa3d2d039` | register copies bind their decoded-word forms; gate, pins and published ratio |
| `d7908456e` | `L04P11_RETAIN_DIR` object retention in the two native targets |
| `a0ef64085` | the two in-crate pins (`coverage_gate`'s denominator, `proof_database`'s BitwiseShift count) the first sweep missed |

The Linux floor ran on clean `fa3d2d039`. The qualifying harness
(`harnesses/qualify-l04p11-20260924.py`, stored verbatim) ran on clean
`a0ef64085`. The commits after `fa3d2d039` change only tests: the retention
hook in the two native targets, whose tests the harness re-runs, and two unit
pins. `records/source.json` has HEAD, tree and an empty
`git status --porcelain --untracked-files=all` before and after the harness.
`harnesses/make-inventory-20260924.py` wrote `inventory.json`.

## Host and tools

Linux `6.17.0-1026-nvidia` on NVIDIA Grace (Cortex-X925/Cortex-A725), glibc
2.39 (`records/host.json`). `cc` is Ubuntu GCC 13.3.0, with GNU ld, objdump
and readelf 2.42; no `clang` is installed. rustc/cargo 1.97.1 ran through the
rustup proxies; AY 0.27.0 and Clean 0.9.0 resolved from the pinned package
prefix. `records/tools.json` has each resolved path, SHA-256 and version.
Cargo ran with `--locked --offline -j 16`, `CARGO_TARGET_DIR` outside the
repository, `CARGO_PROFILE_{DEV,TEST}_DEBUG=0`, PATH led by the pinned
AY/Clean package directory and ambient `TCG_*`/`TRUST_CG_*` variables
removed. Other build and probe processes shared the host throughout.

## Linux floor

`scripts/check_linux_aarch64.py --jobs 16 --require-clean
--require-offline-deps --require-proof-tools --max-rss-gib 16` on clean
`fa3d2d039`: **PASS, 166/166 targets, 1,005 tests** (the previous recorded
floor had 1,003; the two new tests make the difference).
`e2e_aarch64_switch` passed 3 (minimum 3) and `e2e_aarch64_indirect_call` 2
(minimum 2). `records/floor/report.json.gz` is the runner's report (source
fingerprint, dependency and proof-tool identities, per-target commands, RSS
receipts and counts); `records/floor/logs/` has the two targets'
transcripts.

## Results

Each command has `records/commands/<name>.capture.json` (argv, working
directory, relevant environment, UTC start and end, return code, log hash
and summary lines) beside its log.

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_switch -- --show-output --test-threads=1` with `L04P11_RETAIN_DIR` | `ok. 3 passed`; `switch matrix on aarch64-linux-gnu/ELF: 64 functions x O0-O3, 8685036 checked calls` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_indirect_call -- --show-output --test-threads=1` with `L04P11_RETAIN_DIR` | `ok. 2 passed`; `indirect calls on aarch64-linux-gnu/ELF: 10 callers x O0-O3, 7008 checks` |
| `objdump -d --no-show-raw-insn`, `readelf -sW` of the retained O2 objects | exit 0 (logs retained) |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4147 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-verify --test coverage_gate_tests --test aarch64_value_decode_gate --test proof_gate_strict --test soundness_manifest --test meta_theorems` | `ok.` 49, 5, 32, 11 and 8 passed |
| `cargo test -p trust-cg-verify --lib -- aarch64_value_decode function_verifier::tests coverage_gate` | `ok. 210 passed; 4031 filtered out` |
| `cargo test -p trust-cg-cli --bins --test emit_proofs_flag` | `ok.` 30, 0 and 13 passed |
| `python3 -m unittest` of the five floor-gate script test modules | `Ran 154 tests`, `OK (skipped=1)` |
| `python3 -m unittest discover -s scripts/tests -p 'test_*.py'` | `Ran 654 tests`, `FAILED (failures=2, errors=1, skipped=2)`, see below |
| `python3 scripts/native_test_host_matrix.py --check` | exit 0 |
| `scripts/check_fmt.sh` | `check_fmt: OK` |
| `cargo test -p trust-cg-verify --lib` (complete) | `FAILED. 4233 passed; 8 failed`, see below |

On the documentation tree of the final commit, before `inventory.json` was
written, `python3 scripts/check_documentation.py --check`,
`python3 scripts/generate_diagnostics_inventory.py --check`,
`python3 scripts/check_evidence_archive.py --plan` and the six
documentation script test modules (84 tests) passed
(`records/final-checks/`).

The three script failures are environmental and independent of this change:
`test_bridge_build_probe` needs `BRIDGE_PROBE_TARGO` to name a tool,
`test_benchmark_prerequisites`'s dylib helper test expects different backend
flags, and `test_soundness_capture`'s release test expects `--release` in the
`wasm_encoding_gate` command. The last two fail identically with the base
`scripts/soundness_check.sh` (the only one of their inputs this branch
touches, in a comment line); none of the three imports a module this branch
changed.

### Native controls

The retained objects and drivers are `records/objects/{switch_matrix,indirect_call}/`
(objects gzip-compressed). At both O2 and O3 each module's object is byte
identical (the inventory shows the equal decoded hashes).

- `e2e_aarch64_switch`: 64 matrix functions, 38 jump tables, 16 binary
  searches and 10 linear chains, over i8–i64 and u8–u64 selectors, probed
  2,171,259 times per level against the GCC `switch` oracle, including the
  garbage-upper-bits leg on the 8/16/32-bit functions. Every function's
  strategy is read back from its decoded code words at every level, and from
  binutils `objdump -d` of the linked object
  (`records/commands/objdump-d-switch-matrix-O2.log.gz`).
- `e2e_aarch64_indirect_call`: ten callers, 1,752 checks per level, the
  relocated `tc_ops` table of four CG functions and a C function, and C
  callees that overwrite X1-X17, V0-V7 and V16-V31 (not X18 or the
  caller-saved upper halves of V8-V15). Every caller
  keeps its indirect BLR/BR and no BL, in the code words and in
  `records/commands/objdump-d-indirect-call-O2.log.gz`.

### Mutation controls

Each mutation replaces one exact source span of the committed tree,
rebuilds, runs the named tests and restores the file; the harness refuses to
continue unless the tree is clean again. `records/mutations.json` has every
span and outcome.

| Mutation | Tests run | Result |
| --- | --- | --- |
| `m1` jump-table bounds `CMP idx, #range` → `#range + 1` | switch; indirect call | switch: 2 of 3 fail (the programs crash); indirect call: 1 of 2 fails (the function-pointer test, whose module has two jump tables; the program crashes) |
| `m2` binary-search `B.LT` → unsigned `B.LO` | switch | 3 of 3 fail |
| `m3` 8/16-bit selector not cleaned (no UXTB/UXTH) | switch | only the new matrix fails; the two older tests pass |
| `m4` indirect call's BLR clobber set dropped | indirect call | passes; equivalent mutant, all four objects byte-identical to the clean run (the allocator's call-clobber pass applies the AArch64 clobber set to every call-flagged instruction) |
| `m5` indirect call's stack-argument offset + 8 | indirect call | only the new function-pointer test fails (the nine-argument calls) |
| `v1` MOVXrr put back into `is_covered_elsewhere_indirect_branch` | copy-binding unit test; `coverage_gate_tests` binding row | both fail |
| `v2` typed-copy width taken from the operand view | value-credit unit tests; `coverage_gate_tests` ratio pin | both fail: the credit hook refuses the captured `MOVWrr X3, X7` word (filed as MovWrr, its intent is now X-width) and the gate reports the MOVWrr row RED |
| `v3` copies unbound and unexempted (option (b) alone) | `trust-cg-codegen --lib` and seven proof-grade floor targets | fails the library (1 test), `jit_fail_closed_proof_policy` (3 of 7), `jit_source_bound_arithmetic` (every I32/U32/I64/U64 compile refused on MOVWrr/MOVXrr alone) and `aarch64_raw_dataflow_boundary` (1 of 6); `jit_cert_cache_identity_aarch64`, `core_jit_planning`, `jit_wx_refusal` and `aarch64_final_layout_crosscheck` pass |

## Complete `trust-cg-verify --lib`

At unmodified base `f3da1fb17`
(`records/baseline/verify_lib_full_f3da1fb17.{log.gz,capture.json}`):
`FAILED. 4227 passed; 14 failed` in 3,325 s. At `a0ef64085`: `FAILED. 4233
passed; 8 failed` in 3,275 s. All eight later failures are among the
fourteen earlier ones: six `ay_bridge` batch/CLI solver tests, one
`fsym_summary` AY witness test and the x86-64 address-teeth audit report. The
other six earlier failures (three AY solver tests, the resident-solver
process-group test, the portable-authority replay test and the worker-policy
test) passed in this run. This branch does not touch them. In the whole-database AY batch
(`test_ay_batch_verify_all_categories_comprehensive`) the genuinely verified
count moved from 1389/2422 to 1391/2424 with the same 695 errors and 3
timeouts: the two new MOVWrr/MOVXrr obligations discharged under AY. They
are content-identical to the MovW/MovX obligations (same canonical words, same
intent); only the names the typed opcodes bind differ, so the two discharges
add no new evidence.

## Evidence boundary

These are native execution controls against GCC on one Linux host, evaluator
and solver discharges of registered obligations, and the repository's own
gates. They are not proofs of the switch or call lowering. The jump-table
entry contents and the `ADD`/`BR` target binding have no instruction
obligations, and while the bounds check's `CMP` and `B.HI` bind `cmp` and
`condbr` obligations, nothing links the compared bound to the table's size;
that part of L04-P11 was not attempted. A copy's registered obligation is
proved once, on its form's canonical captured word (for example
`MOV X3, X7`); the verifier checks only that the instruction's operands name
that form, only ENC-5 checks the instruction's own word, and proof
certificates do not record that ENC-5 ran. None of it shows that the lowering
chose the right registers.
The new native tests are host-neutral but have not run on a Darwin host.

## Reproduce

From a clean checkout of `a0ef64085` on an AArch64 Linux GNU host with GCC,
binutils, the pinned AY/Clean package prefix and the offline Cargo
dependencies: `python3 harnesses/qualify-l04p11-20260924.py <out-dir>` (edit
its `L04P11_SOURCE_ROOT`, package prefix and target directory for the host),
then the floor command above from a clean checkout of `fa3d2d039` or later.

## Corrections after independent review — 2026-09-24

An independent verifier reviewed this branch. The sentences above on the
clobber set, the typed-copy discharges, the jump-table bounds check and what
a bound copy obligation states were corrected in place; `inventory.json` was
regenerated with the same harness. The review's other findings (emitted copy
shapes no form covered, `SubsRI` and the TPREL adds outside the gate's
denominator) were fixed in `2c600920e`, recorded in
[2026-09-24-linux-l04p11-review](../2026-09-24-linux-l04p11-review/README.md).
The runs recorded here are unchanged.

## Corrections after the second review — 2026-09-24

A second independent verifier checked the branch at `b8e99d969`. The
"Evidence boundary" above says a copy's registered obligation is proved on
its form's canonical captured word; that obligation is an identity over the
word's transcription (for `MOVXrr`, `x7 == 0 | (x7 << 0)`), so its AY
discharge proves nothing about an emitted instance. The per-instance evidence
is ENC-5's per-compile decode, which no certificate records. The review's
other findings were repaired in `02b3f18d7`, recorded in
[2026-09-24-linux-l04p11-review2](../2026-09-24-linux-l04p11-review2/README.md).
`inventory.json` was regenerated with the same harness; the runs recorded
here are unchanged.
