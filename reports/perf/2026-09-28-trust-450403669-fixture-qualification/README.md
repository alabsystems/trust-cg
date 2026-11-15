# Installed Trust compiler fixture qualification (450403669), 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

All 118 tests of the eleven layout-gated `trust-cg-codegen` integration targets
pass on the exact compiler `rustc 1.99.0-dev (450403669 2026-09-24) (trustc
0.10.0+g450403669)` (the installed atpkg Trust package on this Mac, host
`aarch64-apple-darwin`), with the EXISTING current (`*.trust.tir`) fixtures. No
fixture was regenerated and no fixture byte, native oracle, ABI shim or test
body changed. Measured on this branch over trust-cg `e3b6053a8`, and again
with the branch's code over `0756ded44` (2026-09-29): the same 118 PASS, with an
identical `summary.txt` and a slowest test of 38.35 s.

Why: the root workspace pins `channel = "trust"`, and on this host that
toolchain is 450403669, not the 321aaeda7 compiler
[the earlier qualification](../2026-09-28-trust-321aaeda7-fixture-qualification/README.md)
admitted. `crates/trust-cg-codegen/build.rs` refuses every compiler that
`fixture_toolchain.rs` does not certify, so all eleven targets stopped at their
`compile_error!` under it (measured: `e2e_binding_defeq` does, at `e3b6053a8`
and at `0756ded44`).

How: with this exact compiler and target admitted
(`qualifies_current_kernel_fixtures`, an exact compiler/target pair rather than
a compiler-only identity), `targo --unverified test --locked -p
trust-cg-codegen --all-features` built the eleven targets (exit 0), then
`run_fixture_targets.sh` ran each listed test in its own `targo --unverified
test ... --exact <name> --include-ignored --test-threads=1` process. It is the
earlier qualification's runner with the per-test alarm raised from 600 to 1800
seconds because this host ran at load 50-60 during the run. The slowest test
reported `finished in 28.94s`, so the original limit would not have changed any
verdict. `summary.txt` is its output (118 PASS,
0 FAIL): the kernel-JIT targets (`e2e_binding_defeq`, `e2e_ctx_whnf_defeq`,
`e2e_defeq_cache`, `e2e_eta_struct_ext`, `e2e_fvar_opening`, `e2e_lazy_delta`,
`e2e_phase_completion`, `e2e_universe_integration`, `e2e_universe_realnames`),
`e2e_tc_stitching`, and all 72 `e2e_frontend_roundtrip` cases.

Identities of the `0756ded44` run: compiler commit
`450403669e57033b254cab61ee5bdb5cd978ae99` (`trustc -vV`), installed at
`$HOME/toolchains/trust-45040366` (`bin/trustc` SHA-256
`03b6f91632170ade002537d8de91e6fb7e38ebf5cb832e8d746db66edb0347c6`,
`lib/librustc_driver-ebb292d8a3269891.dylib` SHA-256
`beeb6bf5f2f244c2ae851251bf3533d6e46608a6b907724cabd725baccdf9a01`); TrustIR
`8e81e98aa92d78934548ec435218ce530294f2c5` (`Cargo.lock`). The eleven test
executables it ran (SHA-256) are below. A `targo tippy` run in the same target
directory during that run re-ran the build script, so `e2e_frontend_roundtrip`
was relinked from the same source while its cases ran; all 72 of its cases were
then run again, one per process, on the executable listed (72 PASS).

| Target | SHA-256 |
| --- | --- |
| `e2e_binding_defeq` | `6483b9fb810be9236b607af2649871f42c20802901befaa1f28891c909f318c1` |
| `e2e_ctx_whnf_defeq` | `19ac8c0a2d45776c594ef4540b0b24f25d038cb379e6148c069e1dd94b7a405e` |
| `e2e_defeq_cache` | `fcc13e426449b90f8785e4cd7bd9ecd06f221b23f64c9eec30bb86a384d6fbee` |
| `e2e_eta_struct_ext` | `a9f2f5fd93d002b7042105481b30a14d218327ffdf21fa07133d81ce5fb25aee` |
| `e2e_frontend_roundtrip` | `62a77d29423ae431474e841663200a18eb02eff409940d1138a82439039f56a3` |
| `e2e_fvar_opening` | `8a12afbdc5124ae15c28e3eca92caac3a195cfae3144245d72cbbe597bcf6eb6` |
| `e2e_lazy_delta` | `1115a92fb3e352228b3ca82e06d21c904f03092c7cb9481b880ec6a24d0e2c5c` |
| `e2e_phase_completion` | `e924490a33420691bcfa48a8c3718c6f64ef3e50e75dc8b869b6e1872dd3708f` |
| `e2e_tc_stitching` | `51b9743aefb33509493a4e5fc6a2590b85d4e45ed6f744e3c310037d10209a42` |
| `e2e_universe_integration` | `5c52ce39faae816e63034ae77e09f4a441c65e394dc3664de39fa0796882669e` |
| `e2e_universe_realnames` | `e269f58dd0e4c08d545789cd9c7ea1d6d694ab67b4bec2635307c2a267f67785` |

Scope: the native-versus-JIT agreement is test evidence that this compiler's
`repr(Rust)` layout of the kernel types matches the fixtures on this target; it
is not a proof, and it does not generalize to any other compiler revision or
target. The admission is exact on both, and a Trust update must repeat this run
before its identity joins `fixture_toolchain.rs`.
