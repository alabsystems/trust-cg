# rustc_codegen_trust_cg

`rustc_codegen_trust_cg` is the experimental nightly-rustc bridge for
[trust-cg](../../README.md). It lowers a bounded subset of monomorphized rustc
MIR into trust-ir and uses trust-cg to produce native code.

> **Status — v0.1.0 research preview.** This bridge is an evaluation surface,
> not a general Rust codegen backend or a replacement for LLVM, Cranelift, or
> rustc's production backends. It accepts selected MIR, layout, ABI, runtime,
> and target shapes and deliberately rejects many others. Read the
> [v0.1.0 limitations](../../LIMITATIONS.md) before evaluating generated code.

## Why this is a standalone crate

The root trust-cg workspace uses the repository's release toolchain. This crate
instead:

- uses unstable `rustc_private` APIs;
- is built as a `dylib` for `rustc -Zcodegen-backend=<path>`;
- pins its own dated nightly and rustc development components in
  [`rust-toolchain.toml`](rust-toolchain.toml); and
- has an empty `[workspace]` table in [`Cargo.toml`](Cargo.toml), so its
  nightly-only requirements do not affect the root workspace.

The rustc-internal API and dylib ABI are unstable. A toolchain-pin change must
be accompanied by a clean bridge rebuild and its focused regression tests.

## Build

Install [rustup](https://rustup.rs/) and a native linker. From the repository
root, the availability probe verifies the pinned nightly and its required
components, then performs a locked release build:

```bash
scripts/run_full_test_matrix.sh --check-rustc-backend-env
```

For a direct build, enter this standalone crate so rustup selects its local
toolchain file:

```bash
cd crates/rustc-codegen-trust-cg
cargo build --release --locked
```

The resulting backend is
`target/release/librustc_codegen_trust_cg.dylib` on macOS or
`target/release/librustc_codegen_trust_cg.so` on Linux.

## Minimal invocation

Still in the crate directory, compile the included smoke program with the
pinned rustc:

```bash
BACKEND="$(find target/release -maxdepth 1 -type f \
  \( -name 'librustc_codegen_trust_cg.dylib' \
     -o -name 'librustc_codegen_trust_cg.so' \) \
  -print -quit)"
test -n "$BACKEND"

rustc --edition=2021 \
  -Copt-level=0 \
  -Zcodegen-backend="$BACKEND" \
  examples/hello.rs \
  -o target/trust-cg-hello
```

[`examples/hello.rs`](examples/hello.rs) intentionally loops forever. Producing
the executable exercises backend loading, MIR admission, object emission, and
linking; the integration test runs it under a bounded timeout.

This command uses the pinned stock sysroot. It does not rebuild `core`, `alloc`,
or `std` with trust-cg and is not self-hosting evidence.

## Supported surface and fail-closed boundary

The current contract is the conservative
[`rustc-mir-coverage-inventory.md`](../../rustc-mir-coverage-inventory.md).
It classifies mono items, rustc ABI/layout facts, MIR statements, rvalues,
terminators, and intercepted `core`/`std` calls as supported, partial, or
fail-closed. The
[`trust-cg replacement-readiness ledger`](../../trust-cg-full-replacement-ledger.md)
records the broader blockers.

In particular:

- the bridge does not consume rustc's complete `FnAbi`/`PassMode` model;
- MIR places, projections, aggregates, statics, TLS, trait objects, drops,
  unwinding, coroutines, assembly, runtime integration, and target ABIs are
  covered only on named, bounded paths;
- the x86-64 and AArch64 evidence is asymmetric and host-dependent; and
- unsupported shapes are expected to stop compilation with a named diagnostic,
  including dedicated `TCG-*` guards, instead of receiving a guessed lowering.

Fail-closed checks are regression boundaries, not a proof that an alpha backend
contains no crashes, hangs, or wrong-code bugs. An unlisted Rust program must
not be assumed supported merely because it compiles.

### `StepBy` rule

The modeled `std::iter::StepBy` path is available only at
`-Copt-level=0` with the pinned compiler's default MIR-inlining settings. The
bridge rejects `StepBy` at O1, O2, and O3, and also rejects O0 sessions that
explicitly enable normal MIR inlining. Inlined standard-library methods can
observe internal iterator state that the bridge represents differently.

At default O0, modeled consumers and direct `next` use remain available.
Unmodeled state-observing methods such as `size_hint` still fail closed. The
dedicated optimization-level diagnostic is `TCG-STEPBY-OPT-LEVEL`; the
unmodeled-method diagnostic is `TCG-STEPBY-METHOD`.

The optimized-session guard searches monomorphized local type graphs for
`StepBy` nested inside aggregates and closure state. Its depth and unique-type
budgets also bound legal recursively expanding generic types. If either budget
is exhausted, codegen fails closed with `TCG-STEPBY-TYPE-SCAN`; consequently,
an optimized program that does not use `StepBy` can be conservatively rejected
when its type graph exceeds those limits.

## Tests and evidence

Run focused load, execution, and rejection tests from this crate:

```bash
cargo test --release --locked --test hello_loop
cargo test --release --locked --test unsupported_program
```

On an x86-64 host with the pinned target standard library, the `StepBy`
boundary has a dedicated positive/negative regression:

```bash
cargo test --release --locked \
  --test m99_iter_adapters_x86 \
  step_by_is_supported_only_at_default_o0 -- --exact
```

The complete bridge suite is:

```bash
cargo test --release --locked
```

Many integration tests are target-aware and skip when their required host,
target standard library, emulator, or platform tools are unavailable. A skip
does not establish target coverage. Treat the named test, its recorded
preconditions, and the coverage inventory together as the evidence for a
feature.

The root [README](../../README.md) explains trust-cg's evidence levels. Passing
bridge differential tests establishes regression evidence for the tested
programs; it is not an end-to-end formal proof of arbitrary Rust source,
rustc's MIR production, the stock sysroot, linking, or every emitted byte.

## Reporting a bridge bug

Open a [trust-cg issue](https://github.com/alabsystems/trust-cg/issues) with
the repository revision, pinned rustc version, host and target triples,
optimization and MIR flags, the smallest reproducer, the expected result, and
the full `TCG` diagnostic. For suspected wrong code, include an independent
LLVM/rustc result and preserve any target-specific runtime preconditions.
