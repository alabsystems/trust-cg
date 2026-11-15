# Compact owned adapter output, without deep metadata clones

2026-09-07. Base: `8181f41d25b0e68e508a847807379c2eb415efee`,
TrustIR `f572adaf04f55edd6ae9e243586caebfcc3bc660`.

## Scope and ownership

Every production caller constructs one private TrustIrAdapter per function.
Previously its successful return deep-cloned eight owned output channels:
stack slots, debug locals, debug-value bindings, value-type hints, ordinary
pure-callee names, libm-pure names, EH structure, and the complete ProofContext.
The adapter was then dropped. The module caller needs only the separate
exact/imported-call counts and authorization rows after translation.

The new private handoff finalizes refinements first, then transfers the eight
outputs. Exact/imported-call authorizations are untouched and still undergo
the existing module report construction/replay. Public API signatures,
prerequisite validation, emitted instructions, proof policies, and dependency
pins are unchanged. An independent source review checked all successful
callers, the nested inference-only adapter, early-error test consumers and
the refinement recorder before accepting this ownership change.

A plain move has a memory tradeoff: Vec::clone normally discarded builder
slack, whereas moving an amortized-growth Vec retains its capacity. The final
implementation therefore compacts the actual growable row buffers before
transfer. This includes stack/debug rows, EH calls/landing pads and nested
catch lists, every value-proof/value-fact list, function proof/fact lists,
noalias/diagnostic rows, synthesized obligation/formula rows and capability
rows. The generic compactor needs no Clone bound; it moves elements through
an exact-length boxed slice. Empty buffers release their capacity.

Shrinking can reallocate and copy an outer element buffer. This is **not** an
O(1) finalization claim. It avoids recursively cloning nested payloads and
their separate allocations. Hash tables and nested payload objects are moved
as-is; this does not eliminate all spare capacity in strings, types or other
nested data. Refinement tables are already fresh snapshots from the actual
module. No isolated timing/allocation benchmark, end-to-end compiler speedup,
peak-RSS reduction, or TLC/MCC dominance is claimed from these source changes.

## Regression evidence

Three new controls exercise the actual private handoff and public translation:

- Already compact buffers retain their allocations across all eight channels;
  nested proof/refinement contents and pending call rows survive adapter drop.
- A non-Clone, drop-counted payload is moved without early/double destruction;
  deliberately oversized non-ZST row buffers finish with capacity equal to
  length, including nested proof/fact and EH rows.
- A real refined identity function reaches the late refinement recorder and
  retains its declared predicate, signature and debug source through both the
  private adapter and public validated wrapper.

Seeded ownership-test metadata does not assert that the synthetic test
function or its pending call rows carry valid executable authority. Existing
real direct-call, indirect-call, function-address and target-authority tests
exercise their unchanged replay boundaries.

| Selection | Session | Result | Compile | Gate wall | Reservation / sampled peak GB |
| --- | --- | --- | --- | --- | --- |
| Final focused ownership controls | 13043 | 3 passed | 3.85s | 4s | 2 / short sample |
| Full default lower crate | 44582 | full command passed; 1780 library tests | 9.48s | 25s | 3 / 0.41 |
| Full all-feature lower crate | 58842 | 2197 passed: 1787 library + 410 integration | 14.52s | 29s | 3 / 1.60 |
| Actual local-page JIT and callback ABI/clobber | 9889 | 6 passed | 17.66s | 25s | 4 / 2.26 |
| Complete artifact-cache selection | 81990 | 43 passed | 10.33s | 12s | 4 / 1.84 |

Selections overlap; do not sum them as distinct coverage. The default full
output was truncated, so its complete integration tally is not independently
retained here. The all-feature run preserves every summary: eighteen
integration binaries, zero doctests and no failed/ignored/filtered tests. Its
library tests take 5.61s. Native selections take 4.60s and 0.26s respectively.
The first focused compile failed only because an extra test `.into()` left a
generic string argument ambiguous; removing those conversions fixed it.
The earlier two-test plain-move version passed before the capacity audit;
only the final compacting source is described by the rows above.

All Cargo commands use stock Rust 1.97.1, locked dependencies, two build jobs,
serial tests, unset compiler wrappers, empty Rust/rustdoc/encoded flag
overrides and no Rayon override. These are Rust regression checks, not Trust
verification of the compiler implementation. Gate samples are five-second
descendant-tree RSS samples, not an unsampled process maximum. Short samples
do not establish memory footprints; a comparable changed-source lowering
gate can use 3 GB, and the native build uses 4 GB.

```sh
env -u RUSTC -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
  RUSTFLAGS= RUSTDOCFLAGS= CARGO_ENCODED_RUSTFLAGS= \
  PATH=$HOME/.rustup/toolchains/1.97.1-aarch64-apple-darwin/bin:/usr/bin:/bin:/usr/sbin:/sbin \
  CARGO_TARGET_DIR=$HOME/trust-cg/target \
  $HOME/clean/scripts/heavy_gate.sh run 3 LABEL -- \
  cargo test --locked -j2 -p trust-cg-lower --all-features \
  -- --test-threads=1 --quiet
```

Native selection substitutes `-p trust-cg-codegen --test
ty_callback_abi_call_clobber --test local_function_address_jit` and gate4.
Cache selection substitutes `-p trust-cg-codegen --lib artifact_cache` and
gate4; its tests take 0.07s. A comparable cache rebuild can use gate3.

## Frozen source SHA256

```text
14c285431978453d3f9443cbe728725d48b0b5dbabe46b5e90d25631903ca01b  crates/trust-cg-lower/src/adapter.rs
6e31ac4004a67911937699bcd45db519a1330b97f9c8f8b53feaad8a6e62c314  crates/trust-cg-lower/src/adapter_output_handoff_tests.rs
```
