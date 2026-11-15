# Integrated Linux AArch64 gates for the October 15 landing (2026-10-15)

## What lands

On origin/main (merged through `3a249c838`):

- **L02-P13** importer repair round 4: `dso_local` addressing per relocation model
  and integer literals read at their type's width, which removes the importer's
  `0xFADE` address-sentinel wrong code (LD-31, LD-32).
- **L04-P12** trap-guard obligations as a veto layer over `main`'s trap expansion,
  and narrow `I8`/`I16` guard operands (divisor, bounds index and length) tested at
  their width, a native wrong-code fix (LD-35..LD-39). The landing combines `main`'s
  `I128` divisor fold with the narrow extension.
- **Origin's Linux regressions**, round 1 (LD-40..LD-43): the generated C driver
  of `aarch64_source_bound_body` is GCC-safe; the verify-gate tests count checker
  identity misses on a host without an authorized checker; a trait object of auto
  traits alone gets one map-survey key (a rustc crash); the bridge's unit
  constant is `PhantomData`; the fat-`Fn` callee row must match LLVM. Origin's
  independent WS7.3 fixes for the `e2e_aarch64_elf_link` fixture and merged
  signature ids are kept (LD-42 marked superseded).
- **Round 2** (LD-44..LD-46): two lib tests broken by upstream merge resolutions,
  two tippy findings, and a restored `HashMap` import in
  `codegen_license_evidence` (an upstream commit removed it as unused while a
  later merge reintroduced its uses).

Each repair branch had an independent verifier. L02-P13 and L04-P12 land with
the last verifier's residuals recorded (LD-31 and the L04-P12 record's Remaining
section) instead of further rounds.

## Results

Bridge lane, origin/main `dc5517927` alone against the batch at `d04682c46`:

| Target | origin/main | batch |
| --- | --- | --- |
| aggregate | 91 / 38 | 92 / 37 (the same failures less `trait_upcasts`; the fat-`Fn` row renamed) |
| unwind cleanup | 2 / 1 | 2 / 1 |
| panic hook | 1 / 1 | 1 / 1 |
| TLS, trap stubs, ZST fields | pass | pass |

Most aggregate failures are `[TCG-IR-LOWER]` refusals by trust-ir validation
(`OperandTypeMismatch`: a store of `ptr` at `i64`, mixed-width shifts) of bridge
output: fail-closed refusals present on origin/main itself, to be triaged next.

Also failing identically on origin/main alone: the LLVM importer's
`casttest3_imported_program_links_and_runs`, two `aarch64_elf_symbol_binding`
rows (trust-ir now refuses identical duplicate declarations; `[TCG-SECTION-EXEC]`
refuses data placed in `.text`), and two Darwin gate-script tests (two new targets
not classified in the Darwin floor).

The batch passes tippy on 19 packages, the codegen lib suite (4,845 / 0 after
round 2), the trap suites (132 / 0), the workspace type-check with all targets
and the formatting and documentation checks. Logs stay out of tree (host-local:
`/home/ayates/trust-cg-floor-20260922/bridge-base1015`, `bridge-land1015`,
`prop-*-p4.log`, `prop-check-p6.log`). This is regression evidence on one host,
not proof.
