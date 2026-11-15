# Linux kernel fixtures

The TC stitching inputs are unedited MIR closure emissions for `tc_proj_root` (136 members) and
`tc_whnf_route_root` (89 members) from `tests/slices/clean_tc_stitch_slice.rs`.
Both carry the `aarch64-unknown-linux-gnu` target. Each was emitted twice with
identical bytes, validated with zero errors, and parsed again successfully.

[provenance.json](provenance.json) records the source and artifact hashes, exact
compiler, TrustIR and Clean revisions, and generation profile for TC stitching.
[kernel-provenance.json](kernel-provenance.json) binds the 19 additional
closures for the other nine targets. The compiler is Trust
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`. The generator carries TrustIR's
module-wide global identity repair, published as
`e75f566c26149f3fe2659aedbaab0ff55b1f467d`; the metadata records its exact
base, source hashes and binary hash at generation time, when the root consumer
pinned TrustIR `be4018498bc33a9416c4e9ebec317b762f0d7751` (the
`consumer_trust_ir_revision` both provenance files record).

Build `frontend/trust_ir_mir` in the repaired TrustIR checkout using the matching
compiler-private metadata and LLVM SDK. With `TCROOT`, `PRIVATE`, `SDK`,
`IRROOT` and `GEN_TARGET` naming those local directories:

```sh
RUSTC="$TCROOT/bin/trustc" RUSTDOC="$TCROOT/bin/trustdoc" RUSTC_BOOTSTRAP=1 \
CARGO_TARGET_DIR="$GEN_TARGET" CARGO_INCREMENTAL=0 \
RUSTFLAGS="-Lall=$PRIVATE/aarch64-unknown-linux-gnu -Lall=$PRIVATE/host -Lnative=$SDK/lib" \
LD_LIBRARY_PATH="$TCROOT/lib:$TCROOT/lib/rustlib/aarch64-unknown-linux-gnu/lib" \
"$TCROOT/bin/targo" --unverified build --locked --offline -j 2 \
  --manifest-path "$IRROOT/frontend/Cargo.toml" --bin trust_ir_mir
```

From the trust-cg root, generate each root into a fresh directory `OUT`:

```sh
RUSTC="$TCROOT/bin/trustc" \
LD_LIBRARY_PATH="$PRIVATE/lib:$TCROOT/lib:$TCROOT/lib/rustlib/aarch64-unknown-linux-gnu/lib" \
RUST_MIN_STACK=16777216 "$GEN_TARGET/debug/trust_ir_mir" \
  "$PWD/crates/trust-cg-codegen/tests/slices/clean_tc_stitch_slice.rs" \
  --crate-name clean_tc_stitch_slice --crate-type=lib --edition=2021 \
  --target aarch64-unknown-linux-gnu --sysroot "$TCROOT" \
  -C panic=abort -C overflow-checks=off -C debug-assertions=off \
  --mir-emit-closure tc_proj_root "$OUT/proj.tir"
```

Repeat with `tc_whnf_route_root`, then repeat both emissions and compare their
bytes. Run every listed `e2e_tc_stitching` test separately with the same Trust
compiler and `--exact --test-threads=1`; the test header explains the process
isolation requirement. The generation and qualification runners, logs and
results are retained in the
[qualification report](../../../../../reports/perf/2026-09-25-linux-kernel-fixtures/README.md).
That report lists all ten targets and 52 passing cases, and retains the first
18 failures that exposed the frontend global-numbering defect. All 21 closure
inputs were emitted twice with the repaired generator and qualified again.

The generator build uses Targo's explicit unverified development lane.
Native/JIT agreement is test evidence, not a compiler proof. The exact compiler
and target gate selects the regenerated inputs in this directory.
The separate [frontend qualification](../../../../../reports/perf/2026-09-25-linux-frontend-fixtures/README.md)
passes all 72 `e2e_frontend_roundtrip` cases with its existing fixtures on the
same exact compiler/target pair. That target opts into the predicate without
using new files from this directory. The codegen all-targets check passes.
