# Flat TrustIR GEP repair — Linux AArch64 and WebAssembly, 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The repair preserves TrustIR's `base + sum(indices) * sizeof(pointee_ty)`
contract in native and wasm lowering. Every index strides the whole pointee;
field projections use `ExtractField`/`InsertField` or explicit byte offsets.
An empty wasm index list preserves the base instead of panicking. Native
strides retain packed and producer-declared layouts. The LLVM importer still
resolves LLVM's type walk into byte offsets before producing TrustIR.

The qualifying candidate is `4ec1eee161775dbb5d0eb3831a1c7b687af00215`,
which includes main `5735f62ae632ea9d51e2127890306a00af9f5d8c` and pins
TrustIR `29744d5f950da6f65360ba6d64efc73f79371ca6`. The baseline is
`d64dcdeb2db661d0ce69df2fec8820db24254505` with the same two new test files
copied in. Exact overlays, source identities, tool hashes, commands, bounded
execution results, and complete logs are retained under `records/`.
`inventory.json` binds compressed and original bytes; gzip timestamps are zero.

## Results

The fourth attempt passed every requested check with source and tools unchanged:

- Baseline: the expected 12 native and 4 wasm failures, with 3 passing controls.
  A constant second index returns native address 4104 instead of 4112 and
  wasm address 4100 instead of 4104. Dynamic aggregate/scalar indices are
  wrongly refused, nested-array strides disagree, and empty wasm GEP panics.
- Candidate: 14 native tests, **528 native calls at O0–O3**, and 5 wasm tests,
  **85 calls in Node v24.21.0**. Ten native pointee shapes include scalar,
  tuple, struct, record, nested array, packed, declared, closure and two enum
  layouts. Controls retain empty/single indices, narrow index carriers and
  the reference interpreter's negative-index UB boundary.
- Related layout suites: aggregate operations 14, declared layouts 33,
  packed strides 10, and TrustIR conformance 6 tests.
- Native packed-field regressions 6 and the changed nested-matrix test 1.
- Wasm lowering 51, wasm validation/runtime 22, LLVM GEP import 26.
- The wasm example checks; root formatting and documentation checks pass.

There are **188 passing candidate Rust tests** in these commands, with no
ignored tests or runtime skips. The matrix, wasm library and LLVM import
commands deliberately filter unrelated tests; their filtered counts remain
in the receipt. Cargo uses 2 build jobs and 1 test thread. Each command is
supervised under a 16 GiB, zero-grace process-group RSS bound and one-hour
limit. No resource breach, timeout, cancelled or truncated result occurred.
The native target is added to the maintained Linux floor with 14 required
passes, raising that inventory to 167 targets. This record does not claim a
full 167-target floor run.

## Reference boundary and retained failed attempts

All 132 native input cases have independent closed-form address expectations.
The pinned TrustIR interpreter also executes 110 of them. Its record and
closure types have no byte layout: the remaining 22 cases assert that exact
error and compare native execution with layout arithmetic. They are not
reported as interpreter/native equivalence. Packed/declared struct fixtures
supply explicit size, alignment and field offsets for both consumers.

The first attempt stopped at invalid test assumptions: missing struct layouts
and unsupported record/closure interpretation. The second corrected those
fixtures and obtained genuine baseline counterexamples, but a shared Cargo
target directory reused baseline artifacts for the candidate. Its candidate
result is invalid as repair evidence and remains recorded as a failure.
The third used a fresh, separate candidate build directory: both new targets
passed, then related fixtures failed to compile because their `ExtractField`
constructors used `value`/`index` instead of `aggregate`/`field`. The fourth
fixes those constructors and reruns the complete requested campaign, keeping
baseline and candidate build directories separate. Native test wrappers were
expanded so the maintained floor can count and pin all 14 tests.

## Reproduce

Use stock Rust 1.97.1 and a supported native AArch64/x86-64 Linux/macOS host;
this retained execution was Linux AArch64. Put Node on PATH for actual wasm
execution. Allocate a distinct Cargo target directory for each source tree.
The exact commands and local tool identities are in the fourth receipt; the
primary command is:

```sh
cargo test --locked -p trust-cg-codegen --test flat_gep_semantics --test flat_gep_wasm -- --nocapture --test-threads=1
```

The native tests explicitly permit unlicensed JIT fixtures and perform no
memory dereference. These are finite execution regressions, not emitted-code
proofs, Trust-verified self-hosting, installed-toolchain promotion, pointer
validity proofs or whole-system completion. Negative indices and overflowing
source offsets remain outside TrustIR's defined execution domain.
