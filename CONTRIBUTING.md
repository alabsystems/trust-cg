# Contributing to trust-cg

Thanks for helping improve trust-cg. Correctness changes, new lowering
coverage, smaller reproducers, proof/checker work, documentation corrections,
and reproducible benchmark packets are all useful contributions.

## Before starting

Read [`README.md`](README.md) for the project model and
[`ARCHITECTURE.md`](ARCHITECTURE.md) for crate ownership and policy boundaries;
[`LIMITATIONS.md`](LIMITATIONS.md) states the current supported envelope. A path
that fails closed is not automatically a bug: accepting it requires the
semantics, target behavior, validation, and evidence policy to be implemented
together.

## Build and test

Build with an installed Trust package: the root `rust-toolchain.toml` pins
`channel = "trust"`, and `targo` builds with its own package's `trustc`:

```bash
targo --unverified --version
targo --unverified check --locked --workspace --all-targets --all-features
targo --unverified test --locked -p trust-cg-cli
targo --unverified test --locked -p trust-cg-verify --features core-byte-replay
scripts/check_fmt.sh
scripts/check_tippy.sh
python3 scripts/check_documentation.py --check
```

`targo --unverified` makes no verification claim about the build; `targo trust`
is the verified lane.

Cargo silently skips a target whose `required-features` are off, so the
feature flags above are not optional: without `core-byte-replay`,
trust-cg-verify's `core_byte_store` and `core_byte_writer` integration targets
are neither built nor run and the command still succeeds, and `--all-targets`
without `--all-features` does not type-check them. The full matrix enables each
target's features and refuses a plan that selects a feature-gated target
without them.

The live-AY batch group (`ay_bridge::tests::test_ay_batch_verify_*`, whole
proof categories through the external AY solver, one obligation at a time)
dominates a `trust-cg-verify --lib` run, so it runs only with `--features
live-ay` (`targo --unverified test --locked -p trust-cg-verify --lib --features
live-ay -- ay_bridge::tests::test_ay_batch_verify_`); without the feature each
of its tests is listed as ignored with that reason. The full matrix runs it as
the `lib-live-ay` shard and the release gate's `--all-features` lanes include it.

The rustc-private bridge and cargo-fuzz harness are separate workspaces and are
not covered by root workspace checks.

Run the narrowest relevant tests while iterating, then broaden before opening a
pull request. Target-specific changes should include the matching object,
link/run, differential, and negative fail-closed coverage where available.

The broader local matrix is:

```bash
scripts/run_full_test_matrix.sh
```

The matrix covers every workspace package and integration-test target and is
fail-closed; `--report-only` always exits 0 and is for measurements only. Its
qualified pass count excludes runtime SKIPs, and it keeps every shard log.
Leave `RUST_TEST_NOCAPTURE` unset or set it to `0`. On a single host it is
non-green by construction. `scripts/full_test_matrix_hosts.py` partitions the
same suites per host, and `python3 scripts/run_darwin_full_test_matrix.py`
runs the Darwin required set
(docs/testing/full-test-matrix.md). Its
`--check` fails on an `#[ignore]` its `IGNORED_TESTS` table does not list and
on a stale or invalid table entry; it classifies a new target from its
file-level `cfg` alone (by default for both hosts), so a new target or test
that prints a runtime skip on one host passes `--check` and fails that host's
run until it gets a `SUITE_CLASS` or `TEST_CLASS` entry with a reason.

Changes to the proof or soundness boundary should also run the
cross-repository soundness gate; its prerequisites are in
[`SOUNDNESS_CHECK.md`](SOUNDNESS_CHECK.md).

Codegen subprocess tests should use the shared supervisor in
[`tests/common/rosetta.rs`](crates/trust-cg-codegen/tests/common/rosetta.rs).
Its polling deadline is not a bound on OS spawn/filesystem calls. After timeout
it requests termination and polls once; it does not block waiting for reaping.
Read `timed_out` and the termination observations, not just the numeric status:
a timeout status may be synthetic, and kernel-blocked or escaped children can
remain alive. Do not rerun EH/Rosetta cases on an unhealthy host. The separate
thread watchdog cannot cancel a Rust worker and still needs process supervision.

## Correctness changes

- Add a regression that fails before the fix and passes afterward.
- Preserve an independent oracle for suspected wrong-code bugs.
- Add or strengthen a fail-closed negative test when new unsupported shapes are
  discovered.
- Do not relabel statistical evidence as formal evidence.
- Do not weaken a gate, timeout policy, denominator, corpus, or assertion to
  make a change pass.
- Keep target, optimization level, ABI, object format, and proof policy explicit
  in tests and reports.

## Performance changes

Follow [`metrics-contract.md`](metrics-contract.md). Preserve the source and
reference revisions, inputs, host, resource envelope, repetitions, raw rows,
wrong/invalid counts, and checker verdicts. Performance improvements do not
justify accepting a correctness regression.

## Style

- Format changed Rust code with `targo fmt` and run the relevant
  `targo tippy`/test gates. `scripts/check_fmt.sh` is the root-workspace formatting
  gate; keep unrelated formatting churn out of focused fixes.
- Prefer small, reviewable commits with a clear semantic contract.
- Keep public claims scoped to executable evidence.
- Add one short `CHANGELOG.md` entry per user-visible change under
  `[Unreleased]` (Fixed/Added/Changed/Removed): what changed, and for a fix
  whether it was wrong code. Measurements, audit rounds, commit hashes and
  report links belong in the commit message and `reports/`, not the changelog.
- Explain current invariants and failure boundaries in comments. Preserve old
  investigations as dated archive reports; do not maintain session journals
  or unverified test/performance totals in source comments.
- Preserve third-party notices and exact provenance when updating vendored
  material; see [`THIRD_PARTY.md`](THIRD_PARTY.md).

By contributing, you agree that your contribution is licensed under the
repository's Apache-2.0 license.
