# Integrated Linux AArch64 gates for the October Linux batch landing (2026-10-15)

## What lands

The Linux batch `50cdee4f6` was gated against an early-October `main` (`i64`: floor,
every lane and tippy green; bridge lane only the known L06-P1 case and one load
flake in an LLVM-built contention twin). After a pause `main` had moved by about
1,300 commits, so the batch was merged onto origin/main three times (`395954590`,
`5f7965f07` and the commit carrying this report). It contains:

- **L02-P15** LLVM-importer repair rounds 4-7 (rulings LD-08..LD-17);
- **X-HOST-P13** one user-cache rule for every AY reader (LD-18);
- **L02-P13** per-global `@llvm.used` retention, unreferenced declarations,
  coverage sections and the triple reading of listed declarations (LD-20..LD-25);
- a floor row for `a64_refine_byte_invariance` on Linux and Darwin;
- ledger notes for those rows.

The L06-P16 closure-body symbol rule (LD-19) is **not** landed: origin's
OD-RUST-CALL-ONE-RULE-20261008 now declares closure bodies and `rust-call` items
exactly as rustc's ABI lists them and checks every placement, which removed the
comparisons the rule was built on. Its programs remain as rows that must match LLVM
(LD-26). Codex's eleven local commits after `a0245b1c4` are not landed: they fix
the nounwind tail-call defect origin fixed differently and need a ruling.

## Environment

Trust development mode (Trust ae9c2c1da), AY admitted. Logs stay out of tree
(host-local: `/home/ayates/trust-cg-floor-20260922/run-i65`, `run-base65`,
`*-i65.log`, `*-base65.log`, `prop-*-p1.log`, `prop-check-p2.log`,
`bridge-land1014`).

## Results

| Lane | origin/main `6fe8c91a1` (`base65`) | batch merge `395954590` (`i65`) |
| --- | --- | --- |
| Floor (246 / 247 targets) | FAIL: `e2e_aarch64_elf_link` (8 tests), `aarch64_source_bound_body` (1) | the same two targets, the same tests |
| codegen/lower lib | 6,874 / 0 | 6,876 / 0 |
| opt lib | 4,537 / 0 | 4,537 / 0 |
| CLI | 119 / 0 | 119 / 0 |
| natives | 27 / 8 (the `elf_link` tests) | the same |
| local call | 13 / 1 (`batched_fn_pointer_indirect_call_reaches_the_right_function`) | the same |
| verify gates | 62 / 2 | the same two |
| symbol binding, fsym, fsym CLI | green | green |
| Bridge lane, aggregate target | 123 / 5 | 124 / 5, the same five |

After merging origin/main `c359903eb` (`5f7965f07`): tippy clean on 19 packages,
codegen/lower lib 6,899 / 0, the ELF targets fail only origin's eight `elf_link`
tests, the LLVM importer suite 402 / 0 with no SKIP, the bridge builds. After
merging origin/main `1d05efbc6` (no conflicts; origin's x86 verifier work): the
workspace type-checks with all targets, and the documentation and gate-script
checks pass.

Every failure above reproduces on origin/main alone; the batch adds none. Origin's
Linux failures (the `elf_link` fixture admission, a GCC `-Werror` in a generated C
driver, two verify-gate pins, four bridge rows) are being triaged separately. This
is regression evidence on one host, not proof.
