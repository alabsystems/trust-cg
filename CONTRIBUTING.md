# Contributing to trust-cg

Thanks for helping improve trust-cg. Correctness changes, new lowering
coverage, smaller reproducers, proof/checker work, documentation corrections,
and reproducible benchmark packets are all useful contributions.

## Before starting

Open an issue before a large architectural change so the intended semantic and
proof boundary can be agreed first. Small bug fixes and documentation changes
can go directly to a pull request.

Read [`README.md`](README.md) for the project model and
[`LIMITATIONS.md`](LIMITATIONS.md) for the current supported envelope. A path
that fails closed is not automatically a bug: accepting it requires the
semantics, target behavior, validation, and evidence policy to be implemented
together.

## Build and test

Use rustup with the root `rust-toolchain.toml`; the release branch pins the
supported stable toolchain:

```bash
cargo check --locked --workspace --all-targets
cargo test --locked -p trust-cg-cli
cargo test --locked -p trust-cg-verify
```

Run the narrowest relevant tests while iterating, then broaden before opening a
pull request. Target-specific changes should include the matching object,
link/run, differential, and negative fail-closed coverage where available.

The broader local matrix is:

```bash
scripts/run_full_test_matrix.sh
```

The matrix is exhaustive over current workspace packages and integration-test
targets and is fail-closed by default. `--report-only` is reserved for
non-gating historical measurements.

The cross-repository soundness gate has additional prerequisites documented in
[`SOUNDNESS_CHECK.md`](SOUNDNESS_CHECK.md). It is expected for changes to the
proof or soundness boundary.

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

- Format every Rust file you change and run the relevant Clippy/test gates.
  Some generated and snapshot-style sources in the initial release are not
  normalized by the current repository-wide rustfmt configuration, so do not
  mechanically reformat unrelated files as part of a focused change.
- Prefer small, reviewable commits with a clear semantic contract.
- Keep public claims scoped to executable evidence.
- Preserve third-party notices and exact provenance when updating vendored
  material; see [`THIRD_PARTY.md`](THIRD_PARTY.md).

By contributing, you agree that your contribution is licensed under the
repository's Apache-2.0 license.
