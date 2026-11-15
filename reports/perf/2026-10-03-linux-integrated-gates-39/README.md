# Integrated Linux AArch64 gates for the 2026-10-03 integration

## What run `i56` integrates

The integration `5971af1f4` is origin/main `5495c11b4` (trust-ir pin `0f243925`) plus:

- **`fix/main-red-bridge`** (two verifier rounds). Four bridge-lane targets that were red on main on this host are fixed; none of them was wrong code.
  - `panic_hook_differential` and `executable_trap_stub_routes_aarch64`: the runner's `TCG_TEST_BACKEND_*` variables reached trustc. This was a harness bug from `343ff2787`.
  - `tls_thread_local_linux`: `d0d0e4caf` deliberately switched to PIC TLS descriptors. The test now requires LLVM's relocation kinds.
  - 16 aggregate tests: intended backend changes had outdated their expectations. Each newly accepted shape was run against LLVM first.
- **`fix/bridge-duplicate-generic-definitions`** (four verifier rounds). Bridge `extern "rust-call"` tuples and closure-body addresses that rustc's untupled FnAbi would read differently are refused by name (`[TCG-RUST-CALL-ABI]`, `[TCG-ARG-ABI]`).
  - 345 two-crate programs went from 291 wrong cells to 0.
  - Three pre-existing closure-body paths stay open and are listed in LIMITATIONS.
- **`fix/bridge-stale-expectations-after-merge`** (verified). Two bridge-lane expectations followed origin's own changes, after proof against LLVM.
  - The OD-56 variadic refusal (`7d7a6035f`): `call_constant_empty` must now be refused.
  - The dead std iterator rows now compile (`f09e5fa9c`). Two new witness rows keep the trap-stub gate live.
- **`fix/xhost-p13-script-cache-modes`** (two verifier rounds). Every repository script creates its `<cache>/trust-cg` entries privately through `scripts/private_cache.py`.
- **`fix/llvm-import-token-level-reading`** (two verifier rounds) and a `musttail` refusal. The LLVM importer reads tokens as LLVM's lexer does, and refuses by name what its line reader would read differently.
- **Ledger.**
  - L02-P13 and X-HOST-P13 first audits and their repairs.
  - New gap L02-P15.
  - L06-P16 and L06-P1 notes.

**Environment:** Trust development mode (Trust ae9c2c1da, `targo --unverified`), with AY admitted through a private 0700 `XDG_CACHE_HOME`.

## Results

| Lane | Previous integration (`i53`/`i53b`) | `i56` |
| --- | --- | --- |
| Floor (225 targets) | PASS | 2 failing tests, both in `trust_ir_corpus_roundtrip` |
| codegen/lower lib | 0 failures | 0 failures (6,637 passed) |
| CLI | 1 failure (`emit_proofs` arithmetic) | the same 1 |
| natives | 83 passed | 83 passed |
| local-call | 1 failure | 0 failures (fixed on origin) |
| fsym, fsym CLI, opt lib, symbol binding, verify gates | green | green |
| bridge lane | 4 of 5 targets red on main | TLS, unwind, panic-hook and trap-stub pass; the aggregate target fails only the known L06-P1 `aliased_f32_read` [TCG-PROOF-465] (127/128) |

The two floor failures do not come from this integration. origin's `5495c11b4` moved the trust-ir pin to `0f243925` (amendment S). That pin adds `fixtures/compat/template_ident_param.tmbs` (and its JSON twin) to the conformance corpus, and the roundtrip test does not classify that file family. The test file is identical on origin/main, so origin/main fails the same way. Classifying the family is a follow-up.

The scripts unit suite (1,204 tests) adds no failure beyond origin's.

Logs are kept out of tree (host-local: `/home/ayates/trust-cg-floor-20260922/{run,bridge}-i56`, `*-i56.log`). This is regression evidence on one host. It is not proof, Trust-toolchain authority, or release readiness.
