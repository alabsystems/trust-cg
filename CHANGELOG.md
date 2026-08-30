# Changelog

All notable public changes to trust-cg are recorded here. The project follows
[Semantic Versioning](https://semver.org/) for release identifiers, while the
0.x APIs and file formats remain unstable.

## [Unreleased]

### Fixed

- x86-64 O0 wrong code: the formal-argument fixup sank a live-range split
  connector below a parallel-copy group that overwrote its source register
  (six or more GPR arguments), and the first repair over-rotated by hoisting
  connectors above the stack-argument loads they depend on; barriers are now
  emitted only on a true source overwrite.
- x86-64 O0 wrong code: spill materialization aliased destination and
  left-hand operand to one scratch register when the right-hand operand was
  the destination vreg (`AddRR vX, vY, vX` with everything spilled), computing
  `p2 + p2` where `p3 + p2` was required.
- Optimizer recognition gates, each closing a demonstrated miscompile and
  each fail-closed: the x86-64 vectorizer requires the counter to enter the
  loop as a literal 0 from the preheader; the vectorizer refuses a non-`RBIT`
  instruction or a compare idiom at the wrong plan-wide element arrangement;
  `neon-fpred` requires the accumulator to enter as `+0.0`; the x86-64
  unroller refuses an invariant constant whose vreg meets a hidden
  (`Xchg`/`Cmpxchg`-class) def; the x86-64 pure-call hoist refuses a
  preheader splice point where `RFLAGS` is live across the call; AArch64
  `strided-store-unroll` refuses an early normal exit from the loop body and
  decides divergence by an opcode whitelist rather than "no `Ret`" (a
  `TailCall` is not a return); and the single-test `cbz` rotation refuses a
  body whose conditional also targets the header.
- x86-64 guard-carrier canaries: the per-kind memo now records the
  condition it validated and fails closed when a later request for the same
  kind names a different condition (salvaged from a retired Codex branch).
- The public-clone release gate parses `benchmarks/beat-llvm/run.py` before
  trusting it, so a syntax error in the differential harness fails the gate
  instead of silently producing no evidence (salvaged from a retired Codex
  branch, with unit tests).
- 20 production panic-family sites that landed after the 2026-08-26 audit
  baseline classified and repaired per the audit's own categories.
- A test that skips for a missing solver, checker, toolchain, target or C
  compiler now prints `SKIP <test>: <reason>` instead of passing silently
  (154 sites across `trust-cg-verify` and the AArch64 link-and-run tests).

### Added

- x86-64, on by default: variable-count rotate `RolRCl` joins the proof
  perimeter and the bridge's 7-instruction variable-rotate expansion fuses to
  it (admission-gated); loop-exit branch inversion; frame-address spill fold,
  rematerialized LEA hop and dead self-copy elision; the flags-deadness scan
  continues through partial writers and `x7` lowers as two LEAs.
- x86-64 opt-in experiments: the two-address expand last-use gate and its
  call-shaped variants (refuted as defaults by paired A/B), and cold-arm
  sinking (`TCG_X86_COLD_ARM_SINK`, an opt-in soak pending real workloads).
- AArch64 post-RA: the narrow zero-extend collapse deletes a provably
  redundant `MOV`/`UXTW` pair and admits copy pseudos.
- AArch64 block layout, each behind its own kill switch: trap-sink,
  dominated `cbz` threading, and single-test do-while rotation.
- Seven adversarial kill-at-def tests for the AArch64 pre-RA coalescer's
  logical and shifted producers.
- `fuzz/repros/`: the differential-fuzz repro corpora, with runners that work
  from any checkout, and a README saying what each corpus pins.

### Changed

- Eight Codex-era remote heads pushed on 2026-08-29 were audited, two hunks
  salvaged, every tip archived under an annotated tag and a verified bundle,
  and the heads retired (`docs/remote-branch-retirement-2026-08-29.md`).
- Rotates and memory-RMW opcodes are modeled in `writes_flags`.
- Dependency pins advanced to the released trust-ir 0.10.0 and then 0.11.0
  and AY 0.19.0; the soundness lock re-pinned; the publication mapping carries
  the compile-artifact cache partition identities.
- Per-pass timing and dump labels are built only when a consumer is enabled.
- `trust-cg-test ratchet warnings` is the single warnings-ratchet
  implementation; `TCG_SOLVER_PATH` is wired to what the code reads.
- `publish/DECISIONS.md` describes the current tree and dependency tuple;
  `CLAUDE.md`'s publication block is the generator's output again;
  `benchmarks/README.md` indexes the benchmark directories.

### Removed

- Dependencies nothing used (`clap_mangen`, `thiserror`, `tracing`, `blake3`,
  `constant_time_eq`, `arbitrary` and unused workspace crates); the three
  lockfiles stay `--locked`-clean.
- 38 dead definitions that `#[allow(dead_code)]` was hiding.
- The shell twins of the warnings and test ratchets, and the scripts that
  could not run (`scripts/fuzz/bench_ext.py`, `bench_prod.py`,
  `ws2_sweep.sh`, `dylib_load_bench.sh`, `tools/perf_sweep.py`).
- The seven root-level `.fuzz-*` directories (moved to `fuzz/repros/`).

## [0.5.0] - 2026-08-28

### Fixed

- Float-to-narrow-integer `as` casts (`i8`/`i16`/`i32`/`u8`/`u16`/`u32`) did
  not saturate: an out-of-range float produced a truncated value at every
  optimization level. Wrong code, reachable from ordinary Rust.
- AArch64 ABI: 16-byte-aligned GPR arguments now start on an even register
  (AAPCS64 C.8), an `i128` passed on the stack carries both of its words on
  both sides of the call, and Darwin `i128` register placement is honored.
- AArch64: a struct or array field offset past 4095 is now lowered through
  the total add-immediate form instead of failing in the encoder at O0/O1.
- The AArch64 symbolic-CFG authority check fired on `Trap*` guard carriers,
  refusing every program carrying an `InBounds` or `ShiftInRange` annotation.
- Vectorizer recognizer tiers: the carrier-drift soundness holes opened by the
  carriers-are-reads redesign are closed fail-closed across the tiers.
- Optimizer idempotence: `mac-reg-block`, `neon-fill`, `neon-bytesum` and nine
  more loop vectorizers re-fired on their own remainder loop every fixpoint
  iteration. Every loop-building pass now passes a second-run pin, and the
  x86-64 vectorizer runs once per function at O3, on the raw post-ISel shape
  its legality arguments assume.
- `rustc` bridge hard declines removed for `for` loops over const-folded
  ranges, aggregate-to-aggregate transmutes, whole-aggregate moves from
  projected memory-backed sources, and `&mut`-returning functions at O0/O1.
- `rustc` bridge emits canonical trust-ir: bool constants carry
  `Constant::Bool`, same-width integer reinterpret copies lower to `Bitcast`,
  constant shift amounts take the shifted value's type, vtable globals
  declare their aggregate type and are addressed by `GlobalAddr`, vtable-shim
  by-pointer receivers agree with their signature, `target_info` is stamped
  on modules entering merge, and merge admits `FatPtrKind::ContainerLen`.
  Dynamic bounds-check identity fails closed.
- Verification: the C flag is derived from the adder carry-out and the `UGE`
  proofs are back; a dead `Copy` of a carried-unchanged parameter no longer
  fails the loop-completeness gate; compiled `Var` slots are numbered by
  distinct input name; the FP evaluator's `FCMP` name parser fails closed and
  knows the wasm spelling; the session cache is bound to exact SMT2 bytes;
  AArch64 `ROR` immediates are reconstructed; return-register sinks are
  authenticated.
- The compile-artifact cache binds its unchecked-default identities to the
  dependency cohort and advances them with the manifest pins, so an artifact
  cannot replay across a dependency change.
- Windows codegen portability restored; JIT feature names compared by value.
- 153 production panic-family sites classified and repaired per the panic
  audit's own categories.
- Gate scripts: the Clean stock-cargo soundness lane was Darwin-only; one
  dependency graph is required across the standalone locks; `check_fmt`
  could not run on the pinned toolchain; the publication private-source
  assertion could not fail; the test suite no longer shells out
  `kill -KILL -<pid>`, which util-linux turns into `kill(-1)`.

### Added

- `--target wasm32-unknown-unknown` (alias `wasm32`): a closed-module
  WebAssembly lane taking exactly one trust-ir module to raw `.wasm` bytes,
  with named refusals for the object/linker/optimization/proof options that do
  not apply to it. It runs no optimization, register allocation, or object
  path, and emits no proof certificates. See [`LIMITATIONS.md`](LIMITATIONS.md).
- wasm lane: an import section and index space, memory policy, and islands
  living inside a host's memory under the `trust:island/abi@1` namespace;
  narrow types, sub-word memory, data segments and `br_table`; encoding,
  CFG-structural and memory/call-ABI obligation families in
  `scripts/soundness_check.sh` (necessary structural conditions, not a proof);
  node-based differential and CFG-fuzz oracles; island generator examples
  with a three-way differential runner over the shipped bytes; and
  `scripts/pure_lane_wasm.sh`, real Rust to wasm with no LLVM in the chain.
- `rustc` bridge shapes: constant-range subslices of arrays, `Vec` and `str`
  at O1 (all range kinds); const-pointer scalar, aggregate and enum/union
  reference call arguments at O1; `mem::swap` of aggregates; the discriminant
  of a projected fieldless enum (`match (state, input)`).
- x86-64 optimizations, on by default, each with a `TCG_NO_X86_*` kill switch:
  the c-row-in-register saxpyq tier, saxpyq x4 unroll with scalar `IMUL`
  products, 4-wide heap-sumq, LEA displacement fold, latch-advance collapse,
  small-constant `IMUL` strength reduction, function-wide constant-guard
  elimination, the masked-range guard tier, post-fixup XMM bridge-copy
  collapse, and memory-destination RMW fusion gated on the live
  reconstruction discharge.
- x86-64 opt-in experiments, measured and refuted as defaults: the
  commutative dying-source-first swap and the loop-rotation admission port.
- AArch64: packed `llvm.fmuladd.v4f32`/`.v2f64` imported as a native vector
  form with a tied-destination `FMLA` lowering, FP splats admitted by the
  importer, register-form `<2 x f64>` lane extract, the runtime-trip partial
  unroll gated on profile hotness, and call-crossing callee-saved hints wired
  into production.
- `rustc` bridge runtime: body-wide `assume` scratch elision, and `Vec::new`
  uses rustc's `RawVec` minimum non-zero capacity.
- Proof perimeter: `PUNPCKLQDQ` and memory-destination `XorMR`/`AddMR`
  (+SIB) join via reconstruction with no allowlist; certified removal of dead
  NZCV writes; `TST`-fed branches cite the `TST` obligation; opt-in precise
  `CMP`/`B.cond` citations (`TCG_PRECISE_CITATIONS=1`); a golden fixture
  pinning every certificate walk query's resolution; the static proof corpus
  audited from 1,877 to 1,907.
- JIT artifacts attest the selected host codegen profile.
- Test infrastructure: shape-coverage programs s26–s71 (trait objects,
  closures, iterators, u128, packed, float and signedness boundaries) with a
  ratchet on oracle builds and declines; `abi-xback` varies return types and
  fails closed on missing coverage; an in-repo 54-compile completeness gate;
  idempotence pins over every firing shape of the vectorizers and second-run
  pins for the remaining passes; layout-twin agreement over 5,000 random
  nested types; the alias-closure/overlap relation pinned over the whole
  encoding space; call-boundary ABI variant pins; benchmark evidence rejects
  stale or incomplete runs; `TCG_DIAG_CHANGED` reports silent mutation; a
  Trust default-authority gate.

### Changed

- Compile time, measured on the 18-program corpus: proofs-on warm compile
  went from 2.284x LLVM -O2 (first AArch64 evidence row, 2026-08-25) to
  1.008x vs -O2 and 0.995x vs -O3 in the latest headline-eligible ledger row
  (2026-08-26; cold 1.005x; runtime geomean 0.878x vs -O3; 18/18 match). The
  levers: the sweep lane (kind-parallel pre-warm, chunked and lane-batched
  sweeps, a u128 batched evaluator for the wide obligations, the speculative
  init sweep, asynchronous pre-warm), the per-box certificate cache on by
  default, memoized registry queries, the proof database and the fixed
  modules off the critical path, the register-allocation validator's
  per-instruction transfer precompiled once per function, the analysis cache
  carried across fixpoint iterations, a bounded global rayon pool sized by
  work, demand-driven bridge lowering, merge validating merged-first,
  per-wave NZCV liveness, and constant-factor work across the optimizer
  passes.
- Dependency pins: trust-ir at its v38 revision (`ContainerLen`), AY 0.17.0;
  the soundness lock and the compile-artifact cache identities re-pinned with
  them. The tracked toolchain remains Rust 1.97.1; Trust verification is an
  explicit, checked gate rather than a default-lane claim.
- The CEGIS cache uses an in-tree wire format (VERSION 6) instead of
  `rmp-serde`; its Layer A Alethe exemption is retired.
- Docs: v0.1.0-era staleness retired across the public surface
  (`LIMITATIONS.md` de-versioned with a WebAssembly section, `ROADMAP.md`
  points at the ledger instead of restating numbers), the promote tier
  described as it actually works, the trust-ir dominator patch retired after
  landing upstream, and repository links point at `alabsystems`.

### Removed

- `rmp-serde` and `rmp` from the shipping dependency closure.
- The staged trust-ir dominator patch under `patches/`.
- The CEGIS Alethe-gap test exemption.

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
