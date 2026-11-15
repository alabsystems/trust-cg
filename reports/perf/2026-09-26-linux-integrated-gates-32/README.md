# Integrated Linux gates in Trust development mode before the thirtieth main push — 2026-09-26

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover the integration `fea7f4134`. It merges, on top of origin/main
`7e85a7fa7`:

- the L06-P13 bridge backend-selection repair (two verifier rounds);
- the L02-P6 audit-2 residuals (a verifier round and a mutant round);
- the Linux leaf-frame fix (a verifier round and a test round);
- panic-free rewrites of the unwrap-ratchet sites in `link_driver.rs`, `elf/dwarf.rs` and the bridge's `slice_tail.rs`;
- ledger updates for L06-P13, L02-P6, L07-P2 and the new gap L03-P13;
- Darwin floor classifications for `flat_gep_semantics` and `aarch64_scalar_cell_link`.

## Why Trust development mode

Since origin/main's AY binary-identity change, trust-cg-verify admits only the AY
bytes that its build compiler ships in `<sysroot>/bin/ay`. A stock Rust 1.97.1
build admits no AY, so `--require-proof-tools` refuses the floor. These runs use
`check_linux_aarch64.py --trust-unverified` with Trust `ae9c2c1da` (the compiler
the owner's floor-driver qualification used, copied to
`/home/ayates/toolchains/trust-ae9c2c1d`). Clean comes from an aterm-style
prefix around that package's own `clean` 0.9.0. No `TCG_*` variable reaches the
compiler: native lanes get `TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1` through a
Cargo target runner (`runner-source/`). This is explicit development
compilation, not Trust-verified compilation.

## Result: no failure beyond origin/main's own

main is not green in this environment. `records/run-base-a559/` and the
`*-base-a559` logs are the same lanes on unmodified origin/main `a559dd62c`, in
the same environment (floor 1,059 tests passed; `a559dd62c` differs from
`7e85a7fa7` only in four vectorizer and Darwin-pin commits). The integration
fails exactly the same tests:

- **Floor (`records/run-i44/`):** 168 targets, 1,072 tests passed, 8 targets
  failing with the same 20 failing tests by name as main:
  - `aarch64_live_frame_effects` (1: `optimized_original_masked_bounds_uses_only_emitted_frame_effects`);
  - `aarch64_raw_dataflow_boundary` (1);
  - `jit_fail_closed_proof_policy` (5), `jit_source_bound_arithmetic` (2),
    `jit_cert_cache_identity_aarch64` (9) and `e2e_cegis_superopt` (4) — proof replay;
  - `e2e_aarch64_eh_linux` (3; these pass on the stock toolchain);
  - `ws2_stack_protector_target` (1).
  `floor-failed-tests.diff` is empty apart from one compiler note line.
- **Codegen/lower library (`lib-i44`):** main's 7 codegen failures only.
- **CLI:** main's `emit_proofs::arithmetic_tests::exact_arithmetic_queries_survive_export_and_metadata_cannot_grant_authority` only.
- **Native suites (LLD and gold required):** main's three `e2e_aarch64_eh_linux` failures only.
- **fsym:** main's `the_map_is_derived_from_the_pinned_trust_ir` only (the trust-ir pin moved without re-deriving the map).
- **Local-call lanes:** main's `batched_fn_pointer_indirect_call_reaches_the_right_function` only (statistical credit withdrawal).
- **Green:** fsym CLI 20; opt library 3,585; symbol binding 67 and relocation model 21 (LLD and gold required, no `SKIP:`); verifier gate targets 5/52/8/32/11.
- **Unwrap ratchet:** OK (380 ≤ 486). main itself fails it on `slice_tail.rs`, fixed here.
- **Linux bridge lane (`records/bridge-i44/`):** `tls_thread_local_linux` 2/2 and `unwind_cleanup_linux` 2/2; `aarch64_c_fnabi_aggregate_linux` fails at the known L06-P1 `[TCG-PROOF-465]` refusal, as on every push. The source fingerprint was the same at all three checkpoints.

`records/gates-i44.status.txt` and `records/gates-base-a559.status.txt` are the
lane-by-lane exit records.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains OPEN.
