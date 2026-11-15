# 29ebb kernel-layout fixture qualification, 2026-11-06 UTC

All 118 original cases across eleven maintained kernel-layout targets passed on
`rustc 1.101.0-dev (29ebb403d 2026-10-28) (trustc 0.12.0+g29ebb403d)`, host
`aarch64-apple-darwin`. Each compiled case executed alone. No existing fixture,
original test body, native oracle, ABI shim or inventory was changed.

The measured source was `feec8dabd2ed17a13585ed33f3f7d080ba8d75aa` plus the
retained two-file unpublished compiler/host candidate, binary-diff SHA-256
`4e4e9e1de4993b68dc448bc00008e2432d50af92ebf810182177293c0e5e7169`. Those candidate files remained unchanged:
`fixture_toolchain.rs` SHA-256 `320e6ef9008d107757914b60b71f41c38e6a6d0dd5d471b10943f07746ff6d0d`;
`release_trust_compilers.txt` SHA-256 `9c78a8f84cbe75e73745137c8bd19f35e7f1ed54f9facf6454e2262858ec2b38`.
Admission and the Darwin soundness pin were finalized only after actual success.
Every older qualified tuple, the legacy selector and the Linux pin are retained.

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

The maintained runner checked each exact transcript for one named pass, zero
failures or ignores, and its pinned filtered-peer count. All 118 checks passed;
native exit was 0 after 528.994 seconds. The first launcher attempt
failed an orchestration assertion before Rust ran because it inspected only
unstaged modifications; it grants no qualification credit. The corrected runner
bound the full tracked HEAD diff before and after execution. An independent
read-only review matched all 118 unique passing names to the eleven inventories.

The runner executed under the normal machine-wide build-slot admission and
ran `scripts/run_public_release_codegen_tests.sh
--qualify-kernel-layout-fixtures --proof-gate=require` with genuine packaged
Trust 16387, normal repository profiles and an owned target. This is an
explicit unverified Rust build lane, not verification of the compiler itself.
The retained environment binds the pinned Lean import inputs, toolchain and
AY/Clean sysroot bytes. No solver drift or exclusions were recorded.

After admission finalization all four `ReleaseTrustCompilerListTests` controls,
workspace formatting and documentation checks passed, with unchanged source.
The retained archive contains source bookends, exact environment and command,
binary diff, all inventories and transcripts, the layout-only summary, and
these final control logs; [its manifest](artifact-manifest.json) binds every
member. The external original evidence and first launcher failure remain under
`$HOME/trust-native-result-aggregate-20261105-nfu/`.

| Retained input/output | SHA-256 |
| --- | --- |
| Native log | `37e4287ecc49d86e397df5ab9725fe5af9ef6f4a04544a04c33c45bc07b6c4c5` |
| Layout-only summary | `ee2620f3f94e17248e5c33331defc71142104755a5b98f66befacaa9733f9d00` |
| Complete policy inventory | `a071aaa1b51d367a1d867406dfb60e0030abea65496fb704cc3f6f7904623456` |
| Retained evidence archive | `5fd642b43f1e5bb0884cd691b4c1599044cf86cbd3ea2ecbd3a22752c9977a7e` |
| Packaged `trustc` | `0acc4862fe98d55f71585dd2e651ad166ce789f049d77b78dfe3d11112889c34` |
| Packaged `targo` | `e8592cdacfbd112d38a6f338665c0e130fb10e9fe67c1c0e031acb50bd32fb2a` |

Compiler source: `29ebb403de7a102850d6cb10a62d5cc3baf723ed`. Genuine Targo
reports `targo 1.101.0-dev (29ebb403d 2026-10-28) (targo 0.12.0+g29ebb403d)`.

Scope is native-versus-JIT agreement for these existing fixtures on this exact
compiler/host. Libtest cannot detect an early return inside a passing test.
The summary remains `qualifying: false`, with its sole reason explicitly
stating layout-fixture qualification only. This establishes no full release,
solver theorem, Clean-kernel proof, compiler correctness, verified bootstrap
or complete Trust objective. The ordinary attested landing train is separate.

An [independent qualification run](independent-pm1-qualification.md) records its own source, timing and evidence identities.
