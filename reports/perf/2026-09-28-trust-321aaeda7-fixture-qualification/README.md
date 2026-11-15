# Installed Trust compiler fixture qualification, 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

All 118 tests of the eleven layout-gated `trust-cg-codegen` integration targets
pass on the exact compiler `rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc
0.1.0)` (commit `321aaeda75478038420d97830f14724c33c8dc39`, host
`aarch64-apple-darwin`, the installed atpkg Trust package), with the EXISTING
current (`*.trust.tir`) fixtures. The 52 release capstones of
`scripts/run_public_release_codegen_tests.sh` are among them. No fixture was
regenerated and no fixture byte, native oracle, ABI shim or test body changed.

Why: ALab systems build with Trust (owner directive 2026-09-28), so the root
workspace now pins `channel = "trust"` and `targo` compiles it with this
compiler. `crates/trust-cg-codegen/build.rs` refuses every compiler that
`fixture_toolchain.rs` does not certify, so all eleven targets stopped at the
compile-time guard until this qualification ran.

How: an isolated diagnostic added this identity to the current-fixture class,
built every `trust-cg-codegen` test target with `targo --unverified test
--locked -p trust-cg-codegen --all-features --no-run` (exit 0), then ran
`run_fixture_targets.sh`: each listed test in its own `targo --unverified test
... --exact <name> --include-ignored --test-threads=1` process under a
600-second alarm, the isolation the release helper uses for the capstones.
`summary.txt` is its output (118 PASS, 0 FAIL): the kernel-JIT targets
(`e2e_binding_defeq`, `e2e_ctx_whnf_defeq`, `e2e_defeq_cache`,
`e2e_eta_struct_ext`, `e2e_fvar_opening`, `e2e_lazy_delta`,
`e2e_phase_completion`, `e2e_universe_integration`, `e2e_universe_realnames`),
`e2e_tc_stitching`, and all 72 `e2e_frontend_roundtrip` cases.

Scope: the native-versus-JIT agreement is test evidence that this compiler's
`repr(Rust)` layout of the kernel types matches the fixtures; it is not a
proof, and it does not generalize to any other compiler revision. A Trust
update must repeat this run before its identity joins `fixture_toolchain.rs`.
