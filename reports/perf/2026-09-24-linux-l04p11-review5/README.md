# L04-P11 fifth review repair — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A fifth independent verifier checked the L04-P11 branch at `8ecd133d3` and
`0f4d5002a`. It found the five-opcode refusal holds on every verifier path,
and it reported four latent findings:

- three rows misclassified in the ENC-5 disclosure;
- the wording of the degenerate fallback and of `Adcs`/`Sbcs`;
- an immediate shift given a register amount, which encoded a move while it
  was credited as a shift;
- an encoder that rarely checks arity.

The repair and its boundary are described in
docs/linux-aarch64-completion.md
(section "L04-P11 … — Fifth review repair"). Ledger gap L04-P11 stays OPEN.

| Commit | Content |
| --- | --- |
| `58cb15743` | `imm_val` refuses a present non-immediate, with relocation placeholders explicit and immediate shifts requiring their amount; ENC-5's shift arm reports a mismatch; the verifier refuses immediate-form ALU instructions with a register third operand and ADDS/SUBS/NEG with an extra operand; the gate's immediate-form representatives carry immediates; the disclosure is classified by verification (88/16, with a pinned degenerate-fallback list); a derived, pinned inventory of 117 opcodes whose encoder ignores a credited trailing operand; LIMITATIONS.md and ARCHITECTURE.md |
| `1922f495c` | test only: the immediate-shift refusal checked end to end in the disclosure test |
| the commit adding this record | the "Fifth review repair" subsection, CHANGELOG, this record |

The host, tools and Cargo environment are those of the first-round record
(NVIDIA Grace, GCC 13.3, binutils 2.42, rustc 1.97.1, AY 0.27.0 and Clean
0.9.0 from the pinned prefix, `--locked --offline -j 16`,
`TCG_*`/`TRUST_CG_*` removed). `harnesses/make-inventory-20260924.py` wrote
`inventory.json`.

## Linux floor

`scripts/check_linux_aarch64.py --jobs 16 --require-clean
--require-offline-deps --require-proof-tools --max-rss-gib 16` on clean
`58cb15743` (2026-09-24 13:11–13:32 UTC): **PASS, 166/166 targets, 1,005
tests**. `e2e_aarch64_switch` 3, `e2e_aarch64_indirect_call` 2,
`jit_fail_closed_proof_policy` 7, `jit_source_bound_arithmetic` 2,
`aarch64_raw_dataflow_boundary` 6 and `panic_fuzz_encode` 11.
`records/floor/` has the runner's report and those six transcripts.

## Results (harness at `1922f495c`)

`harnesses/qualify-l04p11-review5-20260924.py` (stored verbatim) ran on clean
`1922f495c`. `records/source.json` has HEAD, tree and an empty status before
and after it.

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib -- function_verifier::tests function_verifier::walk_query aarch64_value_decode coverage_gate proof_database` | `ok. 261 passed` |
| `cargo test -p trust-cg-verify --test aarch64_value_decode_gate --test coverage_gate_tests --test meta_theorems --test proof_gate_strict --test soundness_manifest` | `ok.` 5, 51, 8, 32 and 11 passed |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4148 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-codegen --test jit_fail_closed_proof_policy --test jit_source_bound_arithmetic --test aarch64_raw_dataflow_boundary` | `ok.` 7, 2 and 6 passed |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_switch --test e2e_aarch64_indirect_call` | `ok.` 3 passed (8,685,036 checked calls) and 2 passed (7,008 checks) |
| `scripts/check_fmt.sh` | `check_fmt: OK` |

## Mutation controls

Each replaces one exact source span behind `std::hint::black_box`, runs the
named tests (which must fail) and restores the file
(`records/mutations.json`). All six are caught.

| Mutation | Tests | Result |
| --- | --- | --- |
| `w1` `imm_val` reads any present non-immediate as 0 | `immediate_fields_refuse_non_immediate_operands` | fails |
| `w2` `LslRI` reads a register amount as 0 (the reported case) | `immediate_fields_refuse_non_immediate_operands` | fails |
| `w3` the register-third-operand refusal guarded off | `malformed_alu_shapes_are_refused_on_every_arm` | fails |
| `w4` ENC-5's shift arm allowlists a non-immediate amount | `credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed` | fails (the arm must mismatch any word) |
| `w5` the gate's `AndRI`/`OrrRI`/`EorRI` representative is the register form | `aarch64_emittable_coverage_is_honest_under_strict` | fails (the rows turn RED) |
| `w6` the ADDS/SUBS/register-ALU extra-operand refusal guarded off | `malformed_alu_shapes_are_refused_on_every_arm`, `register_alu_with_an_extra_operand_is_refused`; the trailing-operand inventory test | 2 of 2 fail; fails |

## Integration sweep

`harnesses/sweep-l04p11-review5-20260924.py` ran every `[[test]]` target of
`trust-cg-codegen`, `trust-cg-cli`, `trust-cg-llvm-import`, `trust-cg-test`
and `trust-cg-jit-matrix` on clean `1922f495c` (13:45–14:03 UTC, four test
threads). The goal was to confirm that no emission site relied on the
encoder reading a non-immediate as 0, or produced one of the newly refused
ALU shapes. `records/sweep/` has `sweep.json` and each crate's test log.

| Crate | Targets | Passed | Failed |
| --- | --- | --- | --- |
| `trust-cg-codegen` | 412 | 3,051 | 2 |
| `trust-cg-cli` | 15 | 123 | 0 |
| `trust-cg-llvm-import` | 13 | 3 | 0 |
| `trust-cg-test` | 5 | 49 | 0 |
| `trust-cg-jit-matrix` | 10 | 91 | 0 |

The two failures are both `ay_sat_bcp_install_gate` tests. They already
failed in the 2026-09-23 integration sweep: their fixture's proof promotion
is refused for its `StpPreIndex`/`LdpPostIndex` frame pair. No log contains
any of the new refusal messages (`expected an immediate, got`,
`is not credited: the encoder encodes only`, `with a register third operand`,
`has no immediate shift amount`). The rustc-bridge shape corpus, which needs
the custom toolchain build, was not run.

## The reviewer's probe

`records/probe/` has the verifier's scratch probe (stored verbatim; its
header says it was not for commit) and its four outputs: the disclosure
classification (a), the extra-operand sweep (b), credited shapes reaching
named arm exits (c), and the targeted cases (d). They were produced on the
reviewed commits, before this repair. The trailing-operand inventory test
reuses the probe's shape pools and its definition of an ignored trailing
operand, and finds 117 opcodes after the repair.

## Evidence boundary

These are the repository's own gates and unit tests, the Linux floor, an
integration sweep and native controls against GCC on one host. The encoder
still does not check arity: the 117 inventoried opcodes are an open gap,
pinned so the list changes only deliberately. Some of those trailing
operands are redundant rather than ignored, and the inventory does not
separate them. 104 of the 174 credited AArch64 rows still have no ENC-5 arm,
and 16 opcode-wide rows bind a degenerate X==X obligation when no operand
shape can be rebuilt.
