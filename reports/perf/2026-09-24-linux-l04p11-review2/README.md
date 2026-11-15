# L04-P11 second review repair — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A second independent verifier checked the L04-P11 branch at `b8e99d969`
(recorded in [2026-09-24-linux-l04p11-review](../2026-09-24-linux-l04p11-review/README.md)).
It found no soundness defect in the copy binding, and three issues: ORR
(vector) copies credited for the whole opcode, the TLSLE TPREL adds credited
with nothing binding them, and documentation overstating what copy
certificates prove. The repair and its boundary are described in
docs/linux-aarch64-completion.md
(section "L04-P11 … — Second review repair"). Ledger gap L04-P11 stays OPEN.

| Commit | Content |
| --- | --- |
| `02b3f18d7` | the `MOV Vd.16B, Vn.16B` decoded-word form and ENC-5 arm for ORR (vector); the three-register 16B OR bound to the lanewise obligation per instruction, every other shape refused; the gate row requiring both; `AddTprelHi12`/`Lo12` as named deferred rows, refused by the function verifier; pins and published ratios |
| `fa9144ea1` | the walk-query golden fixture without the two TPREL queries (a stale pin the harness found) |
| the commit adding this record | documentation, the corrections to the two earlier L04-P11 records, this record |

The Linux floor and the harness (`harnesses/qualify-l04p11-review2-20260924.py`,
stored verbatim) both ran on clean `02b3f18d7`; the library re-run
(`harnesses/qualify-l04p11-review2-fixture-20260924.py`) ran on clean
`fa9144ea1`. `records/source.json` and `records/source-after-fixture.json`
have HEAD, tree and an empty `git status --porcelain --untracked-files=all`
before and after each. `harnesses/make-inventory-20260924.py` wrote
`inventory.json`. The host, tools and Cargo environment are those of the
first-round record (NVIDIA Grace, GCC 13.3, binutils 2.42, rustc 1.97.1, AY
0.27.0 and Clean 0.9.0 from the pinned prefix, `--locked --offline -j 16`,
`TCG_*`/`TRUST_CG_*` removed).

## Linux floor

`scripts/check_linux_aarch64.py --jobs 16 --require-clean
--require-offline-deps --require-proof-tools --max-rss-gib 16` on clean
`02b3f18d7` (2026-09-24 09:52–10:05 UTC): **PASS, 166/166 targets, 1,005
tests**. `e2e_aarch64_switch` 3 (minimum 3), `e2e_aarch64_indirect_call` 2
(minimum 2); the proof-grade targets `jit_fail_closed_proof_policy` 7,
`jit_source_bound_arithmetic` 2 and `aarch64_raw_dataflow_boundary` 6;
`e2e_aarch64_link_runtime` 32 (it includes the local-exec TLS links) and `aarch64_elf_dwarf`
12. `records/floor/` has the runner's report and those seven transcripts.

A first attempt at the same commit (without `--max-rss-gib`) failed three
targets, `e2e_aarch64_eh_linux`, `aarch64_elf_dwarf` and
`aarch64_elf_cfi_differential`: its PATH left out the directory holding
`llvm-dwarfdump`, and those tests stop when no LLVM reader is found. The
other 163 passed. `records/floor-first-attempt/` has its report and the
`aarch64_elf_dwarf` transcript. The recorded run's PATH adds that directory,
as the harness's does.

## Results (harness at `02b3f18d7`)

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib -- aarch64_value_decode function_verifier::tests coverage_gate proof_database` | `ok. 255 passed; 3989 filtered out` |
| `cargo test -p trust-cg-verify --test aarch64_value_decode_gate --test coverage_gate_tests --test meta_theorems --test proof_gate_strict --test soundness_manifest` | `ok.` 5, 49, 8, 32 and 11 passed |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4147 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-cli --bins --test emit_proofs_flag` | `ok.` 30, 0 and 13 passed |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_switch --test e2e_aarch64_indirect_call` | `ok.` 3 passed (8,685,036 checked calls) and 2 passed (7,008 checks) |
| `scripts/check_fmt.sh` | `check_fmt: OK` |
| `cargo test -p trust-cg-verify --lib -- --skip ay_bridge` | `FAILED. 3949 passed; 4 failed` |
| at `fa9144ea1`: `cargo test -p trust-cg-verify --lib -- aarch64_value_decode function_verifier:: coverage_gate proof_database` | `FAILED. 265 passed; 1 failed; 3978 filtered out` |
| at `fa9144ea1`: `cargo test -p trust-cg-verify --lib -- --skip ay_bridge` | `FAILED. 3950 passed; 3 failed` |

At `02b3f18d7` the library run had one failure more than the first review
round: `function_verifier::walk_query_resolution_golden` still pinned the
resolution of the two TPREL queries the repair removed from the function
verifier. `fa9144ea1` regenerates that fixture with `UPDATE_GOLDEN=1` (the
diff is exactly those two lines). At `fa9144ea1` the complete library minus
`ay_bridge` fails only `fsym_summary`'s two AY witness tests and the x86-64
address-teeth audit report, which are among the fourteen that fail at the
unmodified base `f3da1fb17` (first-round record,
`records/baseline/verify_lib_full_f3da1fb17.capture.json`). The re-run's
subset filter `function_verifier::` also matches `x86_64_function_verifier::`,
which is why that audit report is its one failure; the golden test passes
there. The `ay_bridge` solver-batch lane was not re-run.

## Mutation controls

Each replaces one exact source span, runs the named tests (which must fail)
and restores the file; the harness refuses to continue unless the tree is
clean again (`records/mutations.json`). `r1`–`r3` repeat the first review
round's controls. The new `s1`–`s7` guard their change with
`std::hint::black_box`, so each compiles under `-D warnings` and fails only
by its semantics.

| Mutation | Tests | Result |
| --- | --- | --- |
| `r1` the typed `MOVXrr Xd, ZR` form removed | copy-binding, credit-hook and captured-corpus unit tests | 3 of 3 fail |
| `r2` `SubsRI` back to "never selected" | `coverage_gate_tests` ratio and widening-multiply rows | 2 of 2 fail |
| `r3` `AddTprelHi12`/`Lo12` back to the exclusion | `coverage_gate_tests` ratio | fails |
| `s1` `if n != m && black_box(false)` in the ORR (vector) intent: two different sources read as a copy | `orr_vector_binds_the_16b_copy_and_the_16b_or_by_exact_shape`, `tprel_adds_and_malformed_neon_orr_are_refused`; `per_compile_decode_check_runs_the_value_obligation` | 2 of 2 fail; 1 of 1 fails (the live 16B OR word is no longer an ENC-5 match: its intent is now a copy) |
| `s2` `decoded == want \|\| black_box(true)` in `check_neon_orr_16b_word` | `orr_vector_binds_…`; `per_compile_decode_check_…` | 1 of 1 fails; 1 of 1 fails |
| `s3` the gate's `NeonOrrV` special case guarded off | `neon_orr_row_needs_both_bound_shapes_and_tprel_rows_are_deferred`; `aarch64_decoded_value_rows_are_credited_by_every_form` | 1 of 1 fails; 1 of 1 fails |
| `s4` `NeonOrrV => black_box(Some(("orrv.16b lanewise-intent", …)))` | `tprel_adds_and_malformed_neon_orr_are_refused`; `aarch64_decoded_value_rows_…` | 1 of 1 fails; 1 of 1 fails (both assert no opcode-wide query; the per-instruction binding still refuses unbound shapes first) |
| `s5` `n != m \|\| black_box(true)` in `is_neon_orr_16b_three_register`: copies bind the OR obligation | `orr_vector_binds_…`, `tprel_adds_…`; `aarch64_decoded_value_rows_…` | 2 of 2 fail; 1 of 1 fails |
| `s6` `AddTprelHi12 => black_box(Some(("add(lsl#12) == tp", …)))` | `neon_orr_row_needs_both_…`, `tprel_adds_…`; `aarch64_emittable_coverage_is_honest_under_strict` | 2 of 2 fail; 1 of 1 fails |
| `s7` the TPREL deferred reason guarded off | `neon_orr_row_needs_both_…`; `aarch64_emittable_coverage_is_honest_under_strict` | 1 of 1 fails; 1 of 1 fails (both rows become unmapped) |

## What the copy certificates prove

`records/value-form-smt2.txt.gz` has the SMT-LIB query of every registered
decoded-value form, raw (`ay_bridge::serialize_to_smt2`) and after the
solver-side simplifier (`generate_smt2_query`). It was printed by a unit test
added to `02b3f18d7` for that purpose and reverted before the floor and the
harness ran. Each copy form's query asserts the negation of an identity over
one canonical word's transcription: for `MOVXrr`,
`(not (= x7 (bvor (_ bv0 64) (bvshl x7 (_ bv0 64)))))`; for the zero-source
forms an input-free constant identity (`0 == 0 | (0 << 0)`); for
`MOV Vd.16B, Vn.16B`,
`(not (= (concat v7_hi v7_lo) (concat (bvor v7_hi v7_hi) (bvor v7_lo v7_lo))))`.
The query holds neither the word nor its decode. The per-instance evidence is
ENC-5's decode of each emitted word, per compile, which no certificate
records.

## Evidence boundary

These are the repository's own gates and unit tests, the Linux floor and
native controls against GCC on one host. The copy forms are identities over
canonical words, and only ENC-5 checks each instance. The three-register 16B
OR stands on the lanewise obligation (statistical unless AY discharges it)
and ENC-5's field check. NEON AND, EOR, BIC and NOT are still credited for the
whole opcode with no ENC-5 arm. The TPREL adds are counted, not credited, and
the object relocation inventory's TLSLE rows say nothing about the
instructions.

## Corrections after the third review — 2026-09-24

A third independent verifier checked `02b3f18d7`, `fa9144ea1` and
`76f57e1a2` and found the repair sound. Two statements above are
incomplete:

- "NEON AND, EOR, BIC and NOT are still credited for the whole opcode with no
  ENC-5 arm" named four of the credited rows ENC-5 does not decode; there
  were 100 credited opcode-wide and 8 bound per instruction. `b22bca970` binds
  the five NEON bitwise opcodes like ORR (16B shape only, word decoded by
  ENC-5, 8B shapes refused), leaving 104 of the 174 credited rows without an
  ENC-5 arm, now listed in LIMITATIONS.md and pinned by a coverage test.
- The refusals of the V64 OR and of the TPREL adds stop those instructions
  from promoting, but in the verifier's probes no whole-compile verdict
  changed: every local-exec TLS and vector function it compiled was already
  refused for its `StpPreIndex`/`LdpPostIndex` frame pair.

The repair and its qualification are in
[2026-09-24-linux-l04p11-review3](../2026-09-24-linux-l04p11-review3/README.md).
`inventory.json` was regenerated with the same harness; the runs recorded
here are unchanged.
