# Integrated Linux AArch64 gates for the L02-P15, L02-P6 and L02-P10 repairs (2026-10-04)

## What runs `i60` to `i63` integrate

The batch is local `main` (Codex's source-bound credit, lint-scope, guard-elision,
refinement-representation and bridge storage/iterator commits, with their OD-59..OD-68)
plus origin/main (the owner's bridge panic-entry, `vec![value; n]` capacity, allocation
and panic=abort LSDA-region work, with its OD-58), and three verified repair branches:

- **L02-P15, LLVM text importer** (`fix/l02p15-importer-escapes-and-module-flags`,
  first three repair rounds; each round had an independent verifier, rounds 2-4
  CONFIRMED). One escape decoder canonicalizes every quoted name, metadata name and
  attribute string before any reader runs, which removes the `"+v8a\2C+call-saved-x9"`
  wrong code. Module flags and named metadata llc 22 acts on are read or refused by
  name, `"branch-target-enforcement"` is refused in every form, and literals are read
  as LLVM reads them. Rulings LD-01..LD-05.
- **L02-P6, hidden/protected visibility** (`fix/l02p6-audit6-declaration-dedup-coverage`,
  verifier CONFIRMED). A floor row refuses two declarations of one symbol that differ
  in visibility or linkage on every module entry; it kills the sixth audit's surviving
  mutants K19 and K20. Ruling LD-06.
- **L02-P10, link driver** (`fix/l02p10-audit12-tls-permissions-bitcode`; round-1
  verifier REFUTED, repaired, round-2 verifier CONFIRMED). The driver now checks the
  PT_TLS template against trust-cg's `.tdata`/`.tbss`, requires read and execute
  permission for trust-cg's own sections, and recognizes LLVM bitcode inputs. The
  floor now requires `trust-cg-cli` `link_options` (68). Ruling LD-07.

Origin, local `main` and this lane each allocated `OD` numbers in parallel, which
collided three times during integration. This lane's rulings are therefore numbered
`LD-NN` in their own series (stated in the record's preamble), and local `main`'s
lint-scope ruling, which collided with origin's published OD-58, is OD-68.

## Environment

Trust development mode (Trust ae9c2c1da), AY admitted. Logs stay out of tree
(host-local: `/home/ayates/trust-cg-floor-20260922/run-i60`, `run-i61`, `*-i6[0-3].log`).

## Results

| Lane | `i60` (77a6d9272) | `i61` (f3accbfdb) | `i62` (051d06092) | `i63` (9ac898288) |
| --- | --- | --- | --- | --- |
| Floor (225 targets) | PASS | PASS | not re-run | not re-run |
| codegen/lower lib | 0 failed | 6,656 passed, 0 failed | 6,656 / 0 | 6,663 / 0 |
| opt lib | green | green | 4,180 / 0 | 4,180 / 0 |
| CLI | 0 failed | 114 / 0 | 114 / 0 | 114 / 0 |
| natives, local-call, fsym, fsym CLI, symbol binding, verify gates | green | green | green | green |
| tippy (5 packages) | OK | OK | OK | OK |
| Bridge lane | 127/128 (known L06-P1 `aliased_f32_read`); TLS, unwind, panic hook, trap stub pass | stopped (its checkout changed mid-run) | not run | not run |

`i61` adds origin/main and local `main` through 82dec42fe; `i62` adds local `main`
through 8c428199e (one `lower` commit on refinement representation, origin's bridge
allocation work); `i63` adds local `main` through ae2bc55fb (bridge storage and
iterator repairs) and origin/main through 33eefbf58 (the panic=abort LSDA region rule).
The floor was not re-run for `i62`/`i63`: their deltas over `i61` are one `lower`
commit, the codegen LSDA-region change (covered by the natives lane's EH targets) and
bridge sources; every non-floor lane and tippy were re-run.

This is regression evidence on one host, not proof. The bridge lane's only failure is
the known L06-P1 case, the same as `i56` and `i58`.
