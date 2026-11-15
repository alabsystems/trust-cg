# Integrated Linux AArch64 gates for the 2026-10-02 integration

## Runs compared

**Integration `i53`.** This is origin/main `9ae85ec9c` (trust-ir pin `fb477354`) plus:
- **Ledger correction** (`e1faa3898`):
  - L02-P10 records the merged page-model repair (`d73c3ce37`).
  - L06-P14, L06-P15 and L06-P16 record what main actually does after the 2026-09-29 reconciliation (`1048f47f3`). The wrong values are gone, mostly by named compile-time refusal rather than by the original branch's lowering.
- **`fix/main-red-floorlib`:** three tests that were red on main on this host.
  - **Code bug** `compiler::tests::address_free_core_binds_sparse_definition_after_external_declaration`, introduced by `257feca72`. The Core verification request was captured on the compiling thread inside its environment permit, which invalidated the permit for every address-free compile. It is now captured on the proof-verifier stack.
  - **Stale test** `e2e_aarch64_sequences`: replaceable callees are now judged per explicit object format, and the kept ELF ODR lengths are executed.
  - **Stale test** `symbol_linkage_elf`: the test now pins the Mach-O private-extern spelling of an imported hidden definition.
  - An independent verifier confirmed the branch.
- **`fix/bridge-float-pair-closure-return`:** tests and documentation only.
  - The float-pair closure-return refusal found on the earlier branch does not occur on main. A 1,006-cell independent differential, run at five opt levels, under abort and unwind, with 1 and 16 codegen units, matched LLVM.
  - `rust_call_shims_linux` gains 24 float-pair closure lanes; a mutant that writes the wrong register lane fails them.
  - Two verifier rounds.

**Baseline.** `mainx2` (floor and bridge) plus `mainx2b` (lane re-run with the runner restored), on origin/main `13a7b0ad9`.

**Environment.** Trust development mode (Trust ae9c2c1da, `targo --unverified`, floor `--trust-unverified --require-proof-tools`). AY is admitted through a private 0700 `XDG_CACHE_HOME`.

## Results

| Lane | Baseline `13a7b0ad9` | Integration `i53` |
| --- | --- | --- |
| Floor (225 targets) | 2 failing tests | PASS, 0 failing |
| codegen/lower lib | 1 failure | 0 failures (6,615 passed) |
| CLI (`link_options`, `output_paths`, …) | 1 failure (`emit_proofs` arithmetic) | the same 1 |
| natives (link runtime, TLS IE, EH, CFI, ELF link) | 83 passed | 83 passed |
| local-call | 1 failure (x86 batched fn pointer) | the same 1 |
| fsym, fsym CLI, opt lib, symbol binding, verify gates | green | green |
| bridge lane | 4 of 5 targets fail | identical per target, same counts |

The 4 failing bridge targets are aggregate (103/16), TLS (1/1), `panic_hook_differential` (0/2) and `executable_trap_stub_routes_aarch64`. Triaging them is a separate open task.

The scripts unit suite (1,177 tests) has the same 17 failing tests as origin/main.

Logs are kept out of tree, as the durable-evidence policy requires (host-local: `/home/ayates/trust-cg-floor-20260922/{run,bridge}-{mainx2,i53}`, `*-mainx2b.log`, `*-i53.log`).

This is regression evidence on one host. It is not proof, Trust-toolchain authority, or release readiness.

## Re-check after origin/main moved

origin/main gained 25 commits during the run. They were mostly x86-64 work: body slice 8, zero-extending narrow loads and the loop-head aligner. The trust-ir pin was unchanged at `fb477354`. The merge was clean.

A proportionate re-check ran on the merged tree (`i53b`):
- **Build check:** `targo --unverified check --workspace --all-features --all-targets` passes.
- **Non-floor lanes:** every one has exactly the same failures as `i53`, with slightly more tests passing (lib 6,621, opt lib 4,180).
- **Floor target:** the only one whose test file changed, `panic_fuzz_encode_x86_64`, passes 10/10.
