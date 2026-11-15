# Workspace library test suites on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

No maintained gate runs the root workspace's library (`--lib`) unit tests as a
whole. On 2026-09-22 one of them,
`compiler::tests::test_aarch64_parallel_and_serial_multi_function_byte_identical`,
was found to have failed on main unnoticed; it was repaired in `3058c0de4`.
This record is the first full sweep of those suites on the Linux AArch64
host. The first pass ran at main `3058c0de4`. trust-cg-verify was re-run at
`be25d1ba6`, which adds only the whole-module DWARF change in trust-cg-codegen
and the bridge thread-local twin. At `be25d1ba6` the codegen suite passed
again with 4,063 tests, recorded in
[the gate record](../2026-09-23-linux-integrated-gates-2/README.md). This is
regression evidence, not a gate.

## Results

| Crate | Passed | Failed | Ignored |
| --- | ---: | ---: | ---: |
| trust-cg-codegen | 4,059 | 0 | 1 |
| trust-cg-opt | 3,528 | 0 | 2 |
| trust-cg-lower | 1,879 | 0 | 0 |
| trust-cg-regalloc | 712 | 0 | 1 |
| trust-cg-ir | 524 | 0 | 0 |
| trust-cg-llvm-import | 194 | 0 | 0 |
| trust-cg-jit-matrix | 138 | 0 | 0 |
| trust-cg-sat-host | 46 | 0 | 0 |
| trust-cg-gpu | 40 | 0 | 0 |
| trust-cg-process-env | 40 | 0 | 0 |
| trust-cg-dialect | 10 | 0 | 0 |
| trust-cg-fuzz | 7 | 0 | 0 |
| trust-cg-onnx-import | 5 | 0 | 0 |
| trust-cg-drat-trim | 2 | 0 | 0 |
| trust-cg-lift, trust-types | 0 | 0 | 0 |
| **trust-cg-verify** | **4,167** | **11** | 0 |
| trust-cg-verify `test_ay_batch_verify_all_categories_comprehensive` (run alone) | 0 | 1 | 0 |

trust-cg-cli and trust-cg-test have no library unit tests. The first pass
ran every crate at eight test threads and stopped at its 50-minute bound
inside trust-cg-verify, so trust-cg-verify was re-run on its own at two
threads. The comprehensive AY rollup was excluded from that re-run and run
alone, because it takes 32 minutes.

## The trust-cg-verify failures

Eleven of the twelve failures are solver-backed tests. In none of them did AY
report a counterexample:

- `ay_bridge::tests::test_ay_batch_verify_fp_conversion_proofs`:
  `FCVTZS_NaN_produces_zero` returns `(:reason-unknown (incomplete
  proof-trusted))`, which `proof_gate` treats as a hard failure: AY's own
  proof self-check rejected the verdict. The same obligation gives the same
  answer with the Trust-bundled AY 0.26.0 (build 9799) and with the installed
  development AY 0.27.0. The other 13 FP-conversion rows are disclosed
  certification gaps. Both transcripts are retained.
- `test_ay_batch_verify_all_categories_comprehensive`: 1,389 of 2,422
  obligations are genuinely verified. 335 degenerate X==X rows are excluded,
  none fails with a counterexample, 3 time out and 695 end in an error or
  unknown. 165 are unexpected under the test's known-issue list:
  - 84 bare `unknown` Comparison rows. They are exactly the AArch64 FCMP
    consumers: 14 predicates × CSEL/CSINC/CSNEG × f32/f64 over a reaching
    `FCMP`.
  - 81 `proof-trusted` rows: 44 x86-64 lowering, 24 floating-point, 13 FP
    conversion.
- `test_ay_batch_verify_strength_reduction_proofs`,
  `test_cli_verify_fp_mul_commutative`, `test_cli_verify_fp_neg_double`,
  `test_cli_verify_fp_sub_as_add_neg`: AY does not verify the pinned
  identities.
- `checked_overflow_proofs::tests::test_checked_overflow_i64_z3_cli` and
  `loop_backedge_symexec::tests::diamond_loop_end_to_end_refines_and_swap_refutes`
  time out at the solver.
- three `fsym_summary::tests::ay_solver_*` tests do not get their pinned AY
  answers.

The other failure is not a solver question.
`x86_64_function_verifier::reconstruction_teeth_audit::report_which_credited_opcodes_have_no_address_teeth`
pins the set of credited x86-64 memory opcodes whose reconstruction cannot
refute an address error at 37. It is now 51. The 14 additions are exactly
the `Volatile*` memory opcodes that the owner's x86-64 volatile-access work
made reconstructable. Their address evidence comes from the separate decoded
address lane, so the pin is stale, not a lost check. It is left for that
lane's owner.

These results bear on the open gaps: FP proofs have only statistical
evidence (L04-P3), the FCMP/CSET flag consumers (L04-P8, X-OPCODES-P3/P5),
Clean floating-point support (X-OPCODES-P4), and a green full matrix (L13-P6).
They close nothing.

## Retained files

- `records/workspace-lib-pass1.log`: the first pass, all crates.
- `records/trust-cg-verify-lib.log`: the trust-cg-verify re-run.
- `records/comprehensive-ay-rollup.log`: the solo rollup with its full
  per-category report and every unexpected row.
- `records/ay-fp-conversion-ay026.log`, `records/ay-fp-conversion-ay027.log`:
  the AY build A/B.
- `records/ay-ab.sh`, `records/lib-rest2.sh`: the scripts that ran them.

Tool identities: stock Rust 1.97.1. The installed package prefix
`~/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23` supplied AY 0.27.0
(`ec2bf181…`) and Clean 0.9.0 (`8d819378…`) on PATH. The A/B named each AY
explicitly through `AY_SOLVER_PATH`.
