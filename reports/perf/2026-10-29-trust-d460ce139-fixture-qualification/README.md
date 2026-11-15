# D460 kernel-layout fixture qualification, 2026-10-29 UTC

All 118 original cases across the eleven kernel-layout targets passed on
`rustc 1.101.0-dev (d460ce139 2026-10-28) (trustc 0.12.0+gd460ce139)`, host
`aarch64-apple-darwin`. Every compiled case ran in its own bounded process.
No fixture byte, original test body, native oracle or ABI shim changed.

The measured source was `6f715c87955cb374bf49464245819cbcefd25850` plus the
retained seven-line unpublished compiler/host candidate. The two candidate
files were unchanged throughout the run: `fixture_toolchain.rs` SHA-256
`e90eba88eb0f6032163cb19c139f316e5500de8bccaaf6ee178688923b51640c` and
`release_trust_compilers.txt` SHA-256
`b9d35270fb0faad3fb5ba000f34ee0ea3bfbb1c3443c37666aefca387d730499`.
The D8 candidate was replaced before execution; its earlier cancelled queue
retains zero qualification credit. Existing qualified compilers and the legacy
selector remain unchanged.

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

The unchanged maintained runner retained every selected-name assertion and
checked each exact transcript for one named pass, zero failures/ignores and
the pinned filtered-peer count. All 118 transcript checks passed; the native
job terminated 0. The 21 maintained `PublicReleaseGateModeTests` also passed
in 49.151 seconds; those are protocol controls, separate from native cases.
After the final compiler pin/report update, all four maintained compiler-list
controls, the workspace formatting check and documentation check also passed.

The native command was `build-slot --mem-gb 24 --
scripts/run_public_release_codegen_tests.sh --qualify-kernel-layout-fixtures
--proof-gate=require --summary=...`, using the immutable D460 SDK first on
PATH, genuine Targo, Python 3.12, one test thread and normal repository
profiles. The caller initialized/finalized the maintained summary and recorded
the resolved toolchain-sysroot AY/Clean identities before any native case
completed. Final drift checks passed. Source bookends, every inventory/case
transcript and commands are retained under the common Git directory's
`qualification/d460-layout-6f715c879/`. The target was
`target/qualification`; no channel, SDK or installed app changed.

| Retained input/output | SHA-256 |
| --- | --- |
| Native log, including every case transcript | `fd949e1b2c96303dde0684f54911e432f030586347d2385f66a9fdbe20593752` |
| Final layout-only summary | `15ed3ab7187ba735769c354ca25d34f6482131941f1c316ede38314a8987a62f` |
| Complete policy inventory | `a071aaa1b51d367a1d867406dfb60e0030abea65496fb704cc3f6f7904623456` |
| Protocol-control log | `f20ae1f2d65cfd6344e8c804f845d27745c9f423045544563efdd580b5fe185d` |
| D460 `bin/trustc` | `a3083d01598b4a2d395e775ff9489095319da21e78b7037007e6d206bb34cff7` |
| D460 `bin/targo` | `c143f6c2e67e62e486e23b65f23896e960cf2d9432574dc9ef879594e518c0d4` |

Compiler source: `d460ce139ff29b65f1c1032fcd099eb06d11c150`. Genuine Targo
reports `targo 1.101.0-dev (d460ce139 2026-10-28) (targo 0.12.0+gd460ce139)`.

Scope: native-versus-JIT agreement for these existing fixtures on this exact
compiler/host. Libtest accounting cannot detect an early return inside a test.
The summary's sole non-qualifying reason is its explicit layout-only scope.
No full release/proof qualification, solver theorem, Clean-kernel proof,
compiler-byte correctness, verified bootstrap or complete Trust objective is
established. The normal attested landing train remains a separate requirement.
