# L04-P11 third review repair — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A third independent verifier checked the L04-P11 branch at `02b3f18d7`,
`fa9144ea1` and `76f57e1a2` (recorded in
[2026-09-24-linux-l04p11-review2](../2026-09-24-linux-l04p11-review2/README.md))
and found the repair sound. It reported:

- the 8B NEON bitwise forms were treated inconsistently (the 8B ORR refused,
  the 8B AND/EOR/BIC credited);
- 100 credited opcodes had opcode-wide credit and no ENC-5 arm, while the
  docs named four;
- virtual and physical register numbers could collide in the verifier's
  shape check;
- the docs overstated the whole-compile effect of the new refusals.

The repair and its boundary are described in
docs/linux-aarch64-completion.md
(section "L04-P11 … — Third review repair"). Ledger gap L04-P11 stays OPEN.

| Commit | Content |
| --- | --- |
| `b22bca970` | NEON AND/ORR/EOR/BIC/NOT bound per instruction in their 16B shape only, with ENC-5 decoding that shape and 8B shapes refused; virtual registers numbered apart from physical operands; ENC-5's catch-all reason exported and the credited rows without an ENC-5 arm derived, pinned and disclosed in LIMITATIONS.md; ARCHITECTURE.md corrected |
| the commit adding this record | the "Third review repair" subsection, CHANGELOG, corrections to the second-round record, this record |

The Linux floor and the harness (`harnesses/qualify-l04p11-review3-20260924.py`,
stored verbatim) both ran on clean `b22bca970`. `records/source.json` has
HEAD, tree and an empty `git status --porcelain --untracked-files=all` before
and after the harness. `harnesses/make-inventory-20260924.py` wrote
`inventory.json`. The host, tools and Cargo environment are those of the
first-round record (NVIDIA Grace, GCC 13.3, binutils 2.42, rustc 1.97.1, AY
0.27.0 and Clean 0.9.0 from the pinned prefix, `--locked --offline -j 16`,
`TCG_*`/`TRUST_CG_*` removed, PATH including the LLVM readers).

## Linux floor

`scripts/check_linux_aarch64.py --jobs 16 --require-clean
--require-offline-deps --require-proof-tools --max-rss-gib 16` on clean
`b22bca970` (2026-09-24 11:14–11:36 UTC): **PASS, 166/166 targets, 1,005
tests**. `e2e_aarch64_switch` 3 (minimum 3), `e2e_aarch64_indirect_call` 2
(minimum 2); the proof-grade targets `jit_fail_closed_proof_policy` 7,
`jit_source_bound_arithmetic` 2 and `aarch64_raw_dataflow_boundary` 6;
`e2e_aarch64_link_runtime` 32 and `aarch64_elf_dwarf` 12. `records/floor/`
has the runner's report and those seven transcripts.

## Results (harness at `b22bca970`)

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib -- aarch64_value_decode function_verifier::tests function_verifier::walk_query coverage_gate proof_database neon_lowering_proofs::tests` | `ok. 374 passed; 3873 filtered out` |
| `cargo test -p trust-cg-verify --test aarch64_value_decode_gate --test coverage_gate_tests --test meta_theorems --test proof_gate_strict --test soundness_manifest` | `ok.` 5, 50, 8, 32 and 11 passed |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4147 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-cli --bins --test emit_proofs_flag` | `ok.` 30, 0 and 13 passed |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_switch --test e2e_aarch64_indirect_call` | `ok.` 3 passed (8,685,036 checked calls) and 2 passed (7,008 checks) |
| `scripts/check_fmt.sh` | `check_fmt: OK` |
| `cargo test -p trust-cg-verify --lib -- --skip ay_bridge` | `FAILED. 3953 passed; 3 failed` |

The three library failures (`fsym_summary`'s two AY witness tests and the
x86-64 address-teeth audit report) are among the fourteen that fail at the
unmodified base `f3da1fb17` (first-round record,
`records/baseline/verify_lib_full_f3da1fb17.capture.json`). The `ay_bridge`
solver-batch lane was not re-run.

## Mutation controls

Each replaces one exact source span, runs the named tests (which must fail)
and restores the file. The harness refuses to continue unless the tree is
clean again (`records/mutations.json`). `r1`–`r3`, `s1`–`s3`, `s6` and `s7`
repeat the earlier rounds' controls whose source spans still exist. The
second round's `s4` and `s5` mutated spans this repair replaced, and `t1` and
`t2` take their place. The new mutants guard their change with
`std::hint::black_box` or change a pattern, so each compiles under
`-D warnings` and fails only by its semantics. All fifteen are caught.

| Mutation | Tests | Result |
| --- | --- | --- |
| `r1` the typed `MOVXrr Xd, ZR` form removed | copy-binding, credit-hook and captured-corpus unit tests | 3 of 3 fail |
| `r2` `SubsRI` back to "never selected" | `coverage_gate_tests` ratio and widening-multiply rows | 2 of 2 fail |
| `r3` `AddTprelHi12`/`Lo12` back to the exclusion | `coverage_gate_tests` ratio | fails |
| `s1` two different ORR sources read as a copy | ORR binding and refusal unit tests; ENC-5 per-compile test | 2 of 2 fail; fails |
| `s2` `decoded == want \|\| black_box(true)` in the 16B word check | bitwise and ORR unit tests; ENC-5 per-compile test | 2 of 2 fail; fails |
| `s3` the gate's ORR special case guarded off | gate ORR/TPREL row unit test; decoded-value row test | fails; fails |
| `s6` the verifier credits `AddTprelHi12` again | gate-row and refusal unit tests; gate ratio test | 2 of 2 fail; fails |
| `s7` the TPREL deferred reason guarded off | gate-row unit test; gate ratio test | fails; fails |
| `t1` `NeonAndV => black_box(Some(("andv.16b lanewise-intent", …)))` | `neon_bitwise_8b_shapes_are_refused_like_orr` | fails |
| `t2` the three-register bitwise pattern without `bits: 128` | `neon_bitwise_binds_only_the_16b_shape`, `neon_bitwise_8b_shapes_are_refused_like_orr`, `tprel_adds_and_malformed_neon_orr_are_refused` | 3 of 3 fail |
| `t3` `q \| black_box(1)` in ENC-5's NOT check | `neon_bitwise_binds_only_the_16b_shape`; `per_compile_decode_check_runs_the_value_obligation` | fails; fails |
| `t4` `Op::NeonAndV` removed from ENC-5's bitwise arm | `per_compile_decode_check_runs_the_value_obligation`; `credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed` | fails; fails |
| `t5` physical operands ignored when numbering virtual registers (`if black_box(false)`) | `virtual_registers_never_alias_physical_operands`, `tprel_adds_and_malformed_neon_orr_are_refused` | 2 of 2 fail |
| `t6` `NeonAndV => (0, black_box(0b01))` in ENC-5's operation table | `neon_bitwise_binds_only_the_16b_shape`; `per_compile_decode_check_runs_the_value_obligation` | fails; fails |
| `t7` the inventory probe's catch-all match guarded off | `credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed` | fails |

## The reviewer's probe, re-run

`records/probe/zz_r3_probe_codegen.rs` is the verifier's scratch probe, stored
verbatim (its header says it is not for commit to the crate). It compiles
small `i64`, FP, `<16 x i8>` and `<8 x i8>` functions and a local-exec TLS
read under proof-required settings for the Linux triple at O0 and O2, and
records each promotion verdict and ENC-5's counters.
`records/probe/reviewer-run.log.gz` is the verifier's run on the reviewed branch.
`records/probe/rerun-b22bca970.log.gz` is a re-run on the tree committed as
`b22bca970`, with the probe added as an untracked
`crates/trust-cg-codegen/tests/zz_r4_probe.rs` and removed afterwards (before
the floor and the harness). In the re-run:

- the `<8 x i8>` AND and XOR functions' refusal inventories now name
  `NeonAndV` and `NeonEorV` beside `StpPreIndex`/`LdpPostIndex`;
- ENC-5 matches the `<16 x i8>` `and`/`eor` words it used to allowlist, and
  names the 8B words `a64-value: NEON bitwise shape outside the bound 16B
  forms`;
- no whole-compile verdict changed: every vector and local-exec TLS function
  was already refused for its unbound `StpPreIndex`/`LdpPostIndex` frame
  pair, and the `i64` function still promotes.

## Evidence boundary

These are the repository's own gates and unit tests, the Linux floor, native
controls against GCC on one host, and a compile probe. The NEON bitwise
obligations state the 16B operation; an instruction binds them only in that
shape, and ENC-5 checks its word per compile. 104 of the 174 credited AArch64
rows still have no ENC-5 arm (LIMITATIONS.md lists them): their words are not
decoded per compile. The virtual-register collision affected only which shape
the pre-allocation verifier run read; the reviewer found promotion
unaffected, and this record does not test that separately.

## Fourth review repair — 2026-09-24

A fourth independent verifier checked `b22bca970` and `1e386a1c2` and found
them sound. It reported three low findings, repaired in `8ecd133d3` (see the
completion record's "Fourth review repair"):

- the disclosure split five rows wrongly: it is now 91 opcode-wide and 13
  per instruction, by the verifier's per-instruction query;
- register-register ADD/SUB/AND/ORR/EOR with an extra operand was credited
  while the encoder drops that operand and ENC-5 allowlists the word. The
  verifier now refuses it, and the disclosure test pins ENC-5's 30 named arm
  exits;
- two maintained docs repeated the "re-decodes every instruction" claim.

The statements of this record about the split ("96 opcode-wide and 8 per
instruction" in the completion record's third-review subsection) are
superseded by that repair. `harnesses/qualify-l04p11-review4-20260924.py`
(stored verbatim) ran on clean `8ecd133d3`. `records/fourth-review/source.json`
has HEAD, tree and an empty status before and after the run.

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib -- function_verifier::tests function_verifier::walk_query aarch64_value_decode coverage_gate` | `ok. 218 passed` |
| `cargo test -p trust-cg-verify --test aarch64_value_decode_gate --test coverage_gate_tests --test meta_theorems --test proof_gate_strict --test soundness_manifest` | `ok.` 5, 50, 8, 32 and 11 passed |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4147 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-codegen --test jit_fail_closed_proof_policy --test jit_source_bound_arithmetic --test aarch64_raw_dataflow_boundary` | `ok.` 7, 2 and 6 passed |
| `scripts/check_fmt.sh` | `check_fmt: OK` |

| Mutation | Tests | Result |
| --- | --- | --- |
| `u1` the register-ALU extra-operand refusal guarded off (`&& black_box(false)`) | `register_alu_with_an_extra_operand_is_refused`; the disclosure test | fails; fails |
| `u2` ENC-5's ADD/SUB register arm allowlists from three operands (`> black_box(2)`, the reviewer's Plant C) | the disclosure test | fails (`AddRR`'s live word is no longer a Match) |
| `u3` a MOVZ instruction with no operands falls back to the opcode-wide query | the disclosure test | fails (`MOVZWi`/`MOVZXi` become opcode-wide) |
| `u4` one ENC-5 arm exit's reason text changed | the disclosure test | fails (the pinned exit list) |

The Linux floor was not re-run: no floor target's pins changed, and no
emission site produces the newly refused shapes.
