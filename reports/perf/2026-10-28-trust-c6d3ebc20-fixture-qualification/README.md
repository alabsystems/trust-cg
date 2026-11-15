# C6 kernel-layout fixture qualification, 2026-10-28 UTC

All 118 original cases across the eleven kernel-layout targets passed on
`rustc 1.101.0-dev (c6d3ebc20 2026-10-27) (trustc 0.11.0+gc6d3ebc20)`, host
`aarch64-apple-darwin`. Every compiled case ran in a separate bounded process.
No fixture byte, original test body, native oracle or ABI shim changed.

The measured source is clean commit
`53ad59c59e6f1898f27e5b6e50a56526105e8420`, using TrustIR
`73c5a310165739f972e521a7538a5b32810488c4` and its existing Clean95b dependency.
The exact compiler/host candidate was selected only in the unpublished branch;
this actual run qualifies that pair for the existing corpus. Older admitted
compilers and the legacy classifier remain unchanged.

| Target | Executed cases |
| --- | ---: |
| `e2e_binding_defeq` | 5 |
| `e2e_defeq_cache` | 8 |
| `e2e_eta_struct_ext` | 3 |
| `e2e_ctx_whnf_defeq` | 5 |
| `e2e_fvar_opening` | 4 |
| `e2e_lazy_delta` | 6 |
| `e2e_phase_completion` | 4 |
| `e2e_universe_realnames` | 5 |
| `e2e_tc_stitching` | 5 |
| `e2e_universe_integration` | 1 |
| `e2e_frontend_roundtrip` | 72 |

The maintained runner includes the 66 complement cases omitted by the former
52-capstone-only selection. It checks pinned nonzero populations, retains all
original selected-name assertions, and requires each exact process to report
one named pass, zero failures/ignores and exactly its pinned number of filtered
peers. All 118 individual transcripts passed; the native job terminated 0.

The command was `build-slot -- scripts/run_public_release_codegen_tests.sh
--qualify-kernel-layout-fixtures --proof-gate=require --summary=...`, with the
physical C6 package first on PATH, its genuine Targo, Python 3.12 and one test
thread. The caller initialized and finalized the maintained layout-only summary.
The target directory was `target/fixture-qualification`; retained raw evidence is
under the common Git directory's `qualification/c6-layout-53ad59c59/`.

| Retained input/output | SHA-256 |
| --- | --- |
| Native log, including every case transcript | `155b11ac393807f533991ff3290af1cd26eefc22fbb91da77a8680fee95618a1` |
| Final layout-only summary | `e3a3cff767f4bb5419ab99897c5313fde90dbc9f14c1aa5319d1bdccb0f1be82` |
| Complete policy inventory | `a071aaa1b51d367a1d867406dfb60e0030abea65496fb704cc3f6f7904623456` |
| C6 `bin/trustc` | `98f84d9d95ed69bc0a4f97a64309d12a43b3d4731da55dea8e53e11848cc0b0f` |
| C6 `bin/targo` | `ed1a3f88575deeb873d0cff77496cb209196589219aab82c031e0fab21b516c7` |

Compiler commit: `c6d3ebc2042626ee4a24e77bf33cbf40b916a122`. Genuine Targo
reports `targo 1.101.0-dev (c6d3ebc20 2026-10-27) (targo 0.11.0+gc6d3ebc20)`.
The immutable engineering SDK was measured in place; no global toolchain changed.

The new runner's 104 synthetic controls passed. On the composed C6 candidate,
all 15 native compiler-selection controls, 50 harness controls and the maintained
documentation check passed. These are distinct from the 118 native cases.

Scope: native-versus-JIT agreement for these existing fixtures on this exact
compiler/host. Passing libtest accounting cannot observe an early return inside
a test. The summary is explicitly non-qualifying for full release or proof; its
caller-owned form also records that AY/Clean identities were not populated.
No solver qualification, Clean kernel proof, other compiler/host, compiler-byte
correctness, verified bootstrap or complete Trust objective is established.
The mandatory attested landing train remains a separate requirement.
