# 29ebb kernel-layout fixture qualification, 2026-11-06 UTC

All 118 original cases across the eleven kernel-layout targets passed on
`rustc 1.101.0-dev (29ebb403d 2026-10-28) (trustc 0.12.0+g29ebb403d)`, host
`aarch64-apple-darwin`. Every case ran in its own bounded process, with one
test thread. No fixture byte, original test body, native oracle or ABI shim
changed. The native job terminated 0 in 480.780 seconds.

The measured source was `db4a7a4d15d5566d55008ab467e1fc374cfe42b6` plus the
seven-line unpublished compiler/host candidate. Both candidate files and all
18,872 tracked file entries were unchanged throughout the run. The candidate
`fixture_toolchain.rs` SHA-256 was
`105be91a47e670a9c689634a5061488e24e46b5cfe960b06b91053ee3821fb1b`;
`release_trust_compilers.txt` was
`79aa1d17f96f7a3981bc86ca84ab3d8bc1a2d3c905e70f11d363bf4112d6d6bc`.
Existing qualified compilers, other hosts and the legacy selector remain
unchanged. Only after the complete native run passed did the ARM Darwin
soundness pin move from D460 to 29ebb.

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

The unchanged maintained runner preserved every selected-name assertion and
validated every exact transcript for one named pass, zero failures/ignores
and the pinned filtered-peer count. A retained audit revalidated all 118
transcripts against each target's complete compiled inventory; no execution
was repeated for that audit.

The 15 maintained native fixture-selector controls passed with zero failures,
ignores or filters. The existing exact-build/host control now also covers
D460 and 29ebb, preserving missing/shortened branded suffix, changed commit
and date refusals and adding altered-brand/trailing-suffix controls. No extra
test target or test count was added. All four compiler-list and 21 public
release protocol controls passed, as did workspace trustfmt, documentation
and diff checks. Those controls are separate from the 118 native cases.

The native command was `build-slot --cpus 8 --mem-gb 24 -- /bin/sh
scripts/run_public_release_codegen_tests.sh --qualify-kernel-layout-fixtures
--proof-gate=require`. It used the installed immutable Trust 16387 SDK,
genuine matching Targo, signed managed CPython 1, the normal repository
profiles, an owned offline Cargo home and an owned target outside the source.
The maintained summary recorded the resolved toolchain-sysroot AY/Clean
identities before any case completed and found no solver drift. No installed
compiler, SDK, channel or app changed.

| Retained input/output | SHA-256 |
| --- | --- |
| Native log, including every case transcript | `faef6bcce3e5d129370f22d0c436c4587e7494c261a4c501bbd85f2d1bbfc5f4` |
| Final layout-only summary | `528e288f61e513fa72834208f6e454ed72ba320f2336a53291fd7063db49dbb4` |
| Complete policy inventory | `a071aaa1b51d367a1d867406dfb60e0030abea65496fb704cc3f6f7904623456` |
| Final native fixture-selector control log | `08b8b1279cd69a520b6b470ae6dff3aa1ea69cea4364ad4d5a69f00cf92b5d3a` |
| Compiler-list and public-release protocol control log | `e11ccbaf4c7bca916952855fa9f04c620d846c6e7b68a70864515a029a673c6b` |
| Trust 16387 `bin/trustc` | `0acc4862fe98d55f71585dd2e651ad166ce789f049d77b78dfe3d11112889c34` |
| Trust 16387 `bin/targo` | `e8592cdacfbd112d38a6f338665c0e130fb10e9fe67c1c0e031acb50bd32fb2a` |

Compiler source: `29ebb403de7a102850d6cb10a62d5cc3baf723ed`. Genuine Targo
reports `targo 1.101.0-dev (29ebb403d 2026-10-28) (targo 0.12.0+g29ebb403d)`.
Source bookends, tools, summary, policy, inventories, all per-case transcripts
and the audit are retained under
`~/.cache/trust-cg-pm1-transport-evidence/layout-29ebb/`. The owned target is
`~/.cache/trust-cg-pm1-kernel-layout-target.noindex`.

Scope: native-versus-JIT agreement for the existing fixtures on this exact
compiler/host. Libtest accounting cannot detect an early return inside a
test. The summary's sole non-qualifying reason is its explicit layout-only
scope. No full release/proof qualification, solver theorem, Clean-kernel
proof, compiler-byte correctness, verified bootstrap, general proc-macro
support or complete Trust objective is established. The ordinary attested
landing train remains a separate requirement.
