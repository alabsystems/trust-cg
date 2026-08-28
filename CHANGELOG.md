# Changelog

All notable public changes to trust-cg are recorded here. The project follows
[Semantic Versioning](https://semver.org/) for release identifiers, while the
0.x APIs and file formats remain unstable.

## [Unreleased]

### Added

- `--target wasm32-unknown-unknown` (alias `wasm32`): a closed-module
  WebAssembly lane taking exactly one trust-ir module to raw `.wasm` bytes,
  with named refusals for the object/linker/optimization/proof options that do
  not apply to it. It runs no optimization, register allocation, or object
  path, and emits no proof certificates. See [`LIMITATIONS.md`](LIMITATIONS.md).
- Node-based differential and CFG-fuzz oracles for the wasm lane, plus its
  encoding, CFG-structural, and memory/call-ABI obligation families in
  `scripts/soundness_check.sh`. These are necessary structural conditions; they
  do not make the wasm lane verified.

## [0.4.0] - 2026-08-21

### Fixed

- AArch64 register allocation treated X8, the AAPCS64 `sret` pointer, as
  allocatable, producing wrong code at O0–O3.
- Twelve fail-closed recognition gates from two optimizer audit rounds, each
  closing a demonstrated miscompile, one of them an NZCV flag-liveness defect.
- Further optimizer fail-closed repairs: copy-chain resolution now requires a
  single reaching def, and LICM requires an insertion point on the entering
  path and an invariant load dominating every latch.
- `mac-reg-block` miscompiled matmuls over non-8-byte elements; `neon-reduce`
  overwrote the accumulator instead of folding the vector drain into it.
- `sret` and target-ABI selection on AArch64, and ABI return-register ordering
  in the scheduler.
- Vendored `drat-trim` failed to build under strict C99 on glibc.

### Added

- An AArch64 ELF relocation proof lane with `Certified` composition, emitted
  TLS rows bound to replayed object authority, and an artifact-level relocation
  row digest.
- Build-embedded portable canary certificates that replay without AY.
- A per-shape differential gate for the `rustc` bridge, checked against rustc's
  LLVM backend at O0–O3.

### Changed

- Optimizer and encoder performance work on both primary targets: x86 immediate
  step collapse into LEA, loop-aware spill weighting on by default, extended
  loop rotation, dominated zero-test resolution, NEON fill/map/array lanes.
- Compile-time work retiring the remaining `def_path_str` classifiers and the
  first-item warmup.
- trust-ir, AY, and Clean pinned at their release frontier.

## [0.3.0] - 2026-08-18

### Fixed

- Post-index address formation had a latent W/X sub-register blindness and a
  second, drifted copy of the register-overlap predicate.

### Added

- A runtime-trip partial-unroll tier, correct and measured but not enabled.
- Partial-unroll diagnostics now report not-recognized loops, not only declined
  ones.

## [0.2.0] - 2026-08-17

### Fixed

- 128-bit register-offset loads and stores were encoded as 64-bit.
- The differential oracle executed `PRFM` as a 64-bit load and accepted `LD1`/
  `ST1` `1D` forms that the target refuses as unallocated.
- The stack-protector canary is now hoisted above every local.

### Added

- AArch64 native and packed-FP vector lowering, and fail-closed vector-type
  support in the importer.
- Loop optimization: a partial (factor) unroller, call-bearing exact-trip full
  unroll, bounded-trip diamond unroll, multi-exit bounded unroll, innermost-loop
  layout preference, and single-block scan-loop rotation.
- Post-RA scalar post-index address formation, on by default.
- Complete AArch64 opcode-inventory and shifted-opcode coverage tests, and an
  exact opcode strategy census.
- Support for the trust-ir boolean connectives `BAnd`/`BOr`/`BXor`.

### Changed

- Proof and certificate authority hardening: exact proof-corpus cardinality,
  strict AY transcript authority, hard failure on rejected proof authority, and
  lattice replay sealed against carrier substitution.
- Compile-time work on the per-compile path-trimming machinery and lazy post-RA
  overlap masks.

## [0.1.0] - 2026-08-12

Initial research-preview source release.

### Included

- AArch64 and x86-64 compiler backends with AOT object emission and JIT paths.
- Experimental RISC-V 64 lowering and encoding.
- Binary tMBC input plus text and JSON debugging formats.
- Proof obligations, evaluator and solver-backed verification lanes,
  strict `tcg-lrat-cert-v2` canary certificates, structured proof artifacts,
  and fail-closed proof-required compilation.
- Differential, triple-oracle, fuzz, target, object, and soundness test
  infrastructure.
- The SAT-Competition 2026 trust-cg-sat experiment and reproducible benchmark
  material.
- A source-only workspace distribution with exact dependency identities,
  fail-closed publication mapping, and flattened, licensed MicroSAT and
  drat-trim sources.

### Release status

This is an alpha research release, not a production compiler or full Rust
backend. See [`LIMITATIONS.md`](LIMITATIONS.md).
