# trust-cg v0.1.0 limitations

trust-cg v0.1.0 is a research preview. It is suitable for evaluating the
architecture, compiling the documented trust-ir subset, exercising the test
and proof infrastructure, and developing the Trust toolchain. It is not a
production compiler or a drop-in replacement for rustc, LLVM, or Cranelift.

This file is the concise user-facing limit statement. The executable
inventories in [`rustc-mir-coverage-inventory.md`](rustc-mir-coverage-inventory.md)
and [`trust-cg-full-replacement-ledger.md`](trust-cg-full-replacement-ledger.md)
contain the conservative engineering detail. If a broad statement conflicts
with one of those inventories or with a fail-closed runtime check, the narrower
claim wins.

## Correctness and proof scope

- There is no complete, machine-checked end-to-end theorem from arbitrary
  trust-ir input to every emitted machine-code byte.
- The default verifier exhaustively evaluates small-width obligations but uses
  edge cases and pseudorandom samples for many 32/64-bit obligations.
  Statistical success is regression evidence, not proof over all inputs.
- Solver-backed paths prove supported encoded obligations. They do not
  automatically prove that the encoding covers an entire compiler pass, ABI,
  object writer, runtime, or unsupported semantic surface.
- Proof coverage is not uniform across targets, opcodes, optimizations,
  register allocation, object relocations, debug/unwind data, and JIT
  publication.
- `--emit-proofs` is intentionally stricter than ordinary compilation. It can
  reject a module that compiles without proof emission when any required
  opcode or relocation lacks promotable authority.
- Emitted `.cert` and function-level sidecars record evidence and provenance;
  emission alone is not independent certification. Current unsigned exports
  do not cross the trust-cg/AY trust boundary merely by existing.
- Selected SAT-blasted obligations and canaries have independent `drat-trim`
  replay. That checker path does not cover every compiler obligation.
- The Lean development proves selected models and forward-simulation/encoding
  results. It still contains classified proof gaps and explicit trusted axioms.
- Differential and triple-oracle tests cover named corpora. Passing them does
  not prove the absence of miscompilations outside those corpora.

Unsupported input is intended to fail closed, but v0.1.0 is alpha software:
bugs, crashes, hangs, and wrong-code defects may still exist. Do not use its
output for safety-, security-, financial-, or mission-critical systems.

## trust-ir coverage

The accepted trust-ir surface is incomplete. Important gaps include:

- complete aggregate, record, enum/union, vector, sequence, closure, and
  reference-counted-value semantics;
- full constant, global, relocation-bearing initializer, TLS, and zero-fill
  handling;
- complete calls, indirect calls, casts, pointer provenance, atomics, memory
  ordering, volatile access, allocation/deallocation, and lifetime operations;
- complete dialect, parser/binary, proof metadata, source provenance, and
  interpreter parity; and
- uniform ABI/layout handling for every accepted type at every function
  boundary.

Module-scoped `Ty::Refine` inputs are validated with trust-ir's refinement
rules. v0.1.0 lowers the representation-identical base carrier only for the
identity/signature pass-through subset; most ordinary operations that consume
refined values still fail closed. The predicate is not optimization authority,
and table-only type helpers reject refinements because they lack the containing
module needed for validation. Recursive type-table expansion is capped at 128
levels and fails closed beyond that limit.

`Constant::Bytes` is executable as a complete top-level function-body
`[u8; N]` constant when its element type, length, and optional UTF-8 claim
validate. Nested Bytes fields and Bytes global initializers are not lowered in
v0.1.0; module batching defers those forms instead of turning a per-function
failure into a whole-batch fallback.

The imported global-address compatibility ABI reserves the positive bit-pattern
interval `0xFADE_0000_0000_0000..0xFADF_0000_0000_0000` only in top-level
function-body `Constant::Int` values declared as a supported thin
pointer/reference carrier (`Ty::Ptr`, `Ty::Ref`, `Ty::RefMut`, `Ty::PtrConst`,
or `Ty::PtrMut`) or the legacy `Ty::I64` address carrier. In `Ty::U64`,
`Ty::U128`, `Ty::Usize`, and other declared types, the same bit patterns remain
ordinary numeric data. `Ty::Rc` and `Ty::Func` are not stub carriers. Nested
constants and switch cases are never decoded as address stubs; module batching
fails closed on tag-shaped values in those untyped positions rather than
guessing.

The text and JSON formats are review/debug surfaces in this release. Binary
tMBC is the canonical tool-to-tool input, but none of these formats has a
promised long-term compatibility window yet.

Volatile scalar loads and stores use distinct side-effecting machine opcodes on
the AArch64 and x86-64 paths for the supported integer, floating-point, and
128-bit vector widths. Volatile `I128`/`U128` is deliberately rejected: those
values use two 64-bit GPR limbs, and splitting one source-level volatile event
into two architectural accesses would be observably wrong for MMIO. This
restriction is separate from atomicity; the broader atomic and memory-ordering
surface remains incomplete.

## Targets and object formats

### AArch64

AArch64 has active AOT and JIT paths with Mach-O and ELF support. Coverage is
incomplete for platform ABI differences, aggregates, relocations and their
proof authority, TLS models, unwind/exception handling, debug info, atomics,
SIMD/NEON, target features, and full instruction selection.

The AArch64 in-memory JIT rejects functions carrying invoke/landing-pad
exception-handling metadata. Registering frame-walk information alone is not
enough: cleanup and catch selection also require the matching personality and
LSDA. AOT and plain non-EH JIT paths remain separate from this fail-closed
boundary.

Ordinary AArch64 compilation uses canonical shift-zero MOVZ/MOVN seeds plus
MOVK halfword repairs for wide constants. The opcode-wide proof gate does not
yet credit contextual MOVK semantics or the 32-bit W-form MOVN semantics, so
proof-required compilation reports those instructions as unverified instead of
claiming complete constant-materialization coverage.

### x86-64

x86-64 has active AOT and JIT paths with ELF, Mach-O, and COFF support. Coverage
is incomplete for the SysV and Win64 ABIs, aggregates, all relocation classes,
TLS, unwind/exception handling, debug info, atomics, SIMD/AVX feature policy,
and parity between object and JIT paths. Thirty-two-bit x86 targets are not
supported.

### RISC-V 64

RISC-V 64 is experimental. It has real lowering and encoding infrastructure,
but does not have the semantic breadth, proof emission, ABI/object maturity,
or validation depth of the primary targets.

Wasm-related code is a library/research surface, not a target accepted by the
v0.1.0 `trust-cg` CLI.

## Rust integration

The `crates/rustc-codegen-trust-cg` bridge uses a pinned nightly toolchain and
is not part of the root workspace. It accepts a bounded MIR/layout/ABI subset
and deliberately rejects many Rust programs. Missing areas include complete
MIR statements and terminators, `TyAndLayout`/`FnAbi`, mono items, statics and
vtables, aggregates and DSTs, runtime/lang items, panic/unwind, drop semantics,
inline assembly, debug/profiling hooks, and broad ecosystem validation.

The bridge's modeled `StepBy` iterator surface is limited to
`-Copt-level=0` with the default MIR-inlining settings. Codegen optimization
levels O1–O3, or nightly flags that enable normal MIR inlining at O0, reject
`StepBy` before lowering because an inlined standard-library method can observe
state the bridge represents differently. At supported O0 settings, modeled
consumers and `next` remain available; unmodeled methods such as `size_hint`
still fail closed.

At O1--O3 the admission check conservatively traverses each monomorphized
local type graph to find `StepBy` values hidden inside aggregates and closure
state. That traversal has fixed depth and unique-type budgets. A legal
expanding recursive generic can exceed a budget even when it contains no
`StepBy`; the bridge then rejects the program with
`TCG-STEPBY-TYPE-SCAN` instead of risking an unbounded compiler scan. This is a
known false-positive, fail-closed boundary.

It is not a general Rust codegen backend in v0.1.0.

## Optimization and performance

- O0 is the conservative evaluation baseline. O1–O3 exist and are actively
  tested, but confidence and coverage vary by pass, target, and input shape.
- CEGIS, PGO, vectorization, heterogeneous dispatch, Metal/CoreML, and ONNX
  components include real implementations, but several are opt-in or research
  tracks rather than supported end-to-end product paths.
- The two-pass AOT PGO path is supported only for AArch64 at O2 or O3. GEN and
  USE requests for another target or optimization level fail closed. PGO
  compilation also rejects non-mode `TCG_*` and `TRUST_CG_*` controls so hidden
  compilation settings cannot disagree between GEN and USE.
- The v3 `.sites` sidecar carries a compatibility digest over the imported
  input, published producer/schema identity, target, optimization/CEGIS
  settings, and a stable digest of the bytes read from the path returned by
  `current_exe`. That executable digest is non-cryptographic and the path can
  be replaced around the lookup/read; it is a compatibility discriminator, not
  proof of the running process image or a security boundary. A separate
  checksum covers the ordered site rows and detects accidental corruption or
  reordering, but it is also non-cryptographic and can be recomputed.
- The AOT PGO runtime writes a headerless array of little-endian `u64` counters.
  It permits one same-path writer, rejects symlink targets and any process that
  forks after setup, and fails closed on requested-output setup, write, close,
  or rename errors. Startup truncation makes ordinary abnormal exits fail the
  raw-length check, while a normal non-forking run installs its complete dump
  by atomic rename. Neither the sidecar checksums nor the raw file authenticate
  an unrelated, deliberately reconstructed same-length pair, so each
  `.sites`/`.raw` pair must be managed as one generation and treated only as
  performance guidance, never correctness or security authority.
- No aggregate compiler-performance claim is made for v0.1.0.
- SAT-Comp and microbenchmark measurements apply only to the documented
  binaries, inputs, hosts, resource envelopes, and checker results. They do not
  imply end-to-end superiority over LLVM, Cranelift, or production SAT solvers.

See [`metrics-contract.md`](metrics-contract.md) for the evidence required to
publish a new performance comparison.

## Distribution and compatibility

- v0.1.0 is a source-workspace release, not a crates.io package set.
- It builds against exact revisions of companion Trust repositories. Those
  revisions must be present in the public release graph for an anonymous clone
  to build.
- The root workspace pins Rust 1.97.1 in `rust-toolchain.toml`. The optional
  rustc backend is a separate workspace with its own pinned nightly toolchain.
- The Rust library APIs, proof schemas, diagnostics, and text/debug formats are
  not stable yet.
- There are no official prebuilt binaries or package-manager distributions.
- The main soundness gate is deliberately local and cross-repository. This
  repository does not currently use GitHub Actions as a substitute for that
  pinned constellation check.

## Trusted base

Depending on the selected path, the trusted base includes Rust and C compiler
toolchains, trust-cg implementation code not covered by a complete theorem,
the trust-ir semantic encoding, solver/bit-blaster code, proof serializers,
object/linker/runtime behavior, target specifications, and hardware or emulator
oracles. Independently replayed certificates reduce the trusted base only for
the exact claim and artifact the checker accepted.

[`SOUNDNESS_CHECK.md`](SOUNDNESS_CHECK.md) documents the repository's pinned
cross-project gate and separately reported solver-capacity pending work. Treat
that as an engineering soundness program, not as a claim that all residual
trust has been eliminated.

## Reporting a limitation or wrong-code bug

Open an [issue](https://github.com/alabsystems/trust-cg/issues) with:

- the trust-cg revision and `trust-cg --version` output;
- host and requested target triples;
- optimization level, input format, and relevant environment controls;
- the smallest input that reproduces the problem;
- expected and actual behavior; and
- `--trace --metrics` output when available.

For a suspected miscompilation, preserve the original input and independent
oracle result. Do not reduce away the behavior that distinguishes them.
