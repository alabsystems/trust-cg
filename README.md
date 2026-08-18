<div align="center">
  <h1>trust-cg</h1>
  <p><strong>Lower trust-ir. Emit native code. Inspect the evidence.</strong></p>
  <p>A proof-oriented compiler backend in Rust for AArch64 and x86-64,
  with an experimental RISC-V 64 path.</p>
  <p>
    <a href="#quick-start">Quick start</a> ·
    <a href="#understand-and-check-the-evidence">Check the evidence</a> ·
    <a href="#use-trust-cg">Use trust-cg</a> ·
    <a href="#capability-grid">Capabilities</a> ·
    <a href="LIMITATIONS.md">Limitations</a> ·
    <a href="#benchmarks-and-sat-comp-2026">Benchmarks</a> ·
    <a href="#roadmap">Roadmap</a> ·
    <a href="https://github.com/alabsystems/trust-cg/issues">Issues</a>
  </p>
</div>

## What is trust-cg?

trust-cg translates [trust-ir](https://github.com/alabsystems/trust-ir)
modules into native object code. Its pipeline includes validation, instruction
selection, optimization, register allocation, machine-code encoding, object
emission, and JIT support. Verification is part of the pipeline rather than a
separate afterthought: lowering rules carry proof obligations, evidence records
its strength, and proof-required modes reject output that cannot satisfy their
configured authority policy.

```text
  trust-ir (.tmbc; text/JSON for debugging)
                         │
                         ▼
        validate → lower → optimize → register allocate
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
     Mach-O / ELF / COFF       in-process JIT
              │                     │
              └──────────┬──────────┘
                         ▼
       traces, proof reports, and optional sidecars
```

> **Status — v0.1.0 research preview.** trust-cg compiles a useful, tested
> subset of trust-ir, but it is not a production compiler, a full Rust backend,
> or a complete formal verification of every emitted binary. ABI, aggregate,
> relocation, unwind, SIMD, atomic, and proof coverage are still incomplete.
> The default wide-integer verification lane includes statistical checks, which
> are testing evidence rather than mathematical proof. Read
> [`LIMITATIONS.md`](LIMITATIONS.md) before depending on a particular path.

## Quick start

Build trust-cg from source with rustup; `rust-toolchain.toml` selects the pinned
Rust 1.97.1 release toolchain. The runnable example also needs a host C
compiler; it is tested on macOS and Linux.

```bash
git clone https://github.com/alabsystems/trust-cg.git
cd trust-cg
cargo build --release --locked -p trust-cg-cli --bin trust-cg
```

Compile the included text-format trust-ir module for the current host, link it
to a small C driver, and run it:

```bash
HOST_TARGET="$(rustc -vV | sed -n 's/^host: //p')"

target/release/trust-cg \
  --format=text \
  --target "$HOST_TARGET" \
  -O0 -c examples/return_42.trust_ir \
  -o target/return_42.o

cc examples/return_42.c target/return_42.o -o target/return_42
target/return_42
```

The program prints:

```text
42
```

Run the focused CLI tests:

```bash
cargo test --locked -p trust-cg-cli
```

## Understand and check the evidence

“Verified” is not one binary property in trust-cg. Evidence is recorded at
different strengths, and those strengths must not be conflated:

| Lane | What it establishes | Command or entry point |
| --- | --- | --- |
| Exhaustive evaluator | Equality over the complete bounded input space used by a small-width obligation. | `cargo test --locked -p trust-cg-verify` |
| Statistical evaluator | Equality on edge cases and sampled 32/64-bit inputs. Useful regression evidence, **not a proof over all inputs**. | Included in the default verifier tests. |
| Solver discharge | A supported SMT obligation was proved over all represented inputs by the external AY solver. Timeouts and `unknown` are not proofs. | `scripts/check_proof_gate.sh` |
| Certificate-required compilation | Every required report for that compilation was promoted under the configured policy; missing, unknown, timed-out, or unsupported evidence rejects publication. | `trust-cg --emit-proofs=<DIR> ...` |
| Independent replay | A separately implemented checker accepted a supported serialized artifact. This is available only on named paths, not for every emitted certificate. | Vendored `drat-trim` gates and the cross-repo soundness suite. |

Run a short solver-backed smoke check after placing `ay` on `PATH`:

```bash
scripts/check_proof_gate.sh \
  --test representative_arithmetic_is_formally_verified
```

The full proof-database gate is substantially slower:

```bash
scripts/check_proof_gate.sh \
  --test full_database_is_formally_verified
```

Per-compilation proof output is fail-closed. For example:

```bash
target/release/trust-cg \
  --target "$HOST_TARGET" \
  -O0 -c module.tmbc \
  --emit-proofs=target/module-proofs \
  -o target/module.o
```

On a supported path this writes SMT-LIB obligations, structured certificate
records, and function-level sidecars. Emitting a record does not by itself make
the result independently certified. Current unsigned exports identify their
authority accordingly, and relocation or opcode coverage gaps cause the command
to fail rather than silently claim a complete proof.

The broadest repository gate is [`scripts/soundness_check.sh`](scripts/soundness_check.sh).
It runs the pinned trust-cg and Clean checks and records the companion
[AY](https://github.com/alabsystems/ay) revision as evidence provenance. It
is a local, cross-repository release-engineering gate and therefore requires
sibling checkouts; see [`SOUNDNESS_CHECK.md`](SOUNDNESS_CHECK.md) for its exact
trust boundary and prerequisites.

The Lean development under [`formal/lean`](formal/lean) proves selected
forward-simulation and encoding properties. It still contains classified proof
gaps and explicit axioms, so v0.1.0 does not claim a CompCert-style end-to-end
theorem for the entire compiler.

## Use trust-cg

The `trust-cg` executable accepts one or more trust-ir modules:

```text
trust-cg [OPTIONS] <INPUT>...
```

### Input formats

| Format | Flag | Intended use |
| --- | --- | --- |
| Binary tMBC (`.tmbc`) | Default | Canonical tool-to-tool input. |
| Human-readable trust-ir (`.trust_ir`) | `--format=text` | Debugging, review, and small examples. |
| JSON | `--format=json` | Debugging and external-tool integration. |
| Extension/magic detection | `--format=auto` | Compatibility with mixed legacy fixture trees. |

Compile one binary module to an object file:

```bash
trust-cg -O0 -c --target aarch64-apple-darwin \
  input.tmbc -o input.o
```

Compile several modules in parallel and invoke the system linker:

```bash
trust-cg -O0 --target x86_64-unknown-linux-gnu \
  app.tmbc support.tmbc -o app
```

Inspect intermediate behavior and machine-readable metrics:

```bash
trust-cg -O0 -c input.tmbc -o input.o --trace --metrics
trust-cg -O0 -c input.tmbc -o input.o --fsym=warn \
  --fsym-report-json=fsym.json
```

Dump a binary module to the reviewable text form:

```bash
trust-cg -O0 -c input.tmbc -o input.o \
  --emit-trust_ir=input.trust_ir
```

Use `trust-cg --help` to see the options in the binary you built. The Rust
crates are usable in-tree, but their public APIs are not stable in v0.1.0; the
CLI and file formats are the intended evaluation surface for this release.

## Why trust-cg?

| Design choice | What it provides |
| --- | --- |
| Proof-aware input | trust-ir can carry the facts and provenance that justify later transformations instead of requiring the backend to rediscover all source-level intent. |
| Explicit evidence strength | Exhaustive, statistical, solver-proven, and independently replayed results remain distinguishable. |
| Fail-closed proof modes | A proof-required build can reject an unsupported opcode, relocation, or missing report before publishing an artifact. |
| Inspectable stages | Typed IRs, compilation traces, proof reports, and deterministic sidecars make lowering decisions auditable. |
| Differential validation | Native results are compared with independent trust-ir and clang/LLVM execution paths on supported corpora. |
| One multi-target pipeline | AArch64 and x86-64 share validation, lowering, optimization, register allocation, and evidence infrastructure while retaining target-specific ABI and encoder checks. |

The long-term architecture splits responsibility between the producer and the
backend: a frontend proves that its trust-ir represents the source program and
attaches optimization-authorizing facts; trust-cg preserves the accepted
trust-ir semantics while lowering to machine code. v0.1.0 implements important
parts of that composition, but not every pass and output format has complete
proof coverage yet. Missing proof metadata is therefore either a reason an
optimization does not fire or, on proof-required paths, a compilation error—it
must never be presented as stronger evidence than it is.

The v0.1.0 opcode evidence inventory pins accepted/deferred classifications for
every inventoried backend: AArch64 155/248 accepted (93 explicit RED rows),
x86-64 163/192 (29 RED), RISC-V 14/17 (3 RED), and WebAssembly 109/111
(2 RED). These ratios measure accepted obligation coverage over emitted
value/effect inventories, not compiler correctness or formal-proof coverage. In
particular, a default `Statistical(N)` Valid result is regression evidence, not
a formal proof. The inventory test passes with exactly that named debt and fails
on unknown classification or evidence drift.

## Capability grid

Coverage is feature- and target-specific. “Implemented” means there is a real
code path and executable test coverage; it does not mean replacement-grade
completeness.

| Surface | Implemented in v0.1.0 | Important gaps |
| --- | --- | --- |
| AArch64 | Active instruction selection, register allocation, JIT, Mach-O and ELF object emission, scalar integer/FP and selected NEON paths. | Complete ABI, aggregate, relocation authority, TLS modes, unwind/debug, atomics, SIMD, and proof coverage. |
| x86-64 | Active instruction selection, register allocation, JIT, ELF/Mach-O/COFF object emission, scalar integer/FP and selected SSE-128 paths. | Full SysV/Win64 ABI parity, aggregates, TLS, unwind/debug, atomics, AVX/vector coverage, all object relocations, and proof coverage. |
| RISC-V 64 | Experimental lowering, encoding, and ELF-oriented infrastructure. | Product-level ABI/object support, broad ISA coverage, proof emission, and parity validation. |
| trust-ir transport | Binary tMBC, text parser/printer, debug JSON, provenance and proof-sidecar footholds. | Complete semantic coverage for every type, constant, instruction, dialect, aggregate, and metadata form. |
| Optimization | O0 pipeline plus O1–O3 passes, target peepholes, vectorization work, PGO plumbing, and opt-in CEGIS experiments. | Uniform correctness/performance confidence across all higher-level passes and both primary targets. |
| Rust integration | A separate nightly `rustc_codegen_trust_cg` bridge with bounded smoke/UI coverage. | Full MIR, layout, ABI, mono-item, runtime, panic/unwind, and ecosystem coverage. It is not a rustc replacement today. |
| Proof artifacts | Per-rule reports, function-level sidecars, solver bridges, proof databases, and selected independently checked canaries. | End-to-end coverage of every transformation and emitted byte, universal independent replay, and a completed formal compiler proof. |
| Heterogeneous compute | Computation-graph analysis, dispatch planning, Metal/CoreML emission experiments, and ONNX fixture import. | A supported end-to-end launch path and product-level semantics/performance guarantees. |

The detailed stale-overclaim guards are
[`rustc-mir-coverage-inventory.md`](rustc-mir-coverage-inventory.md) and
[`trust-cg-full-replacement-ledger.md`](trust-cg-full-replacement-ledger.md).
Those inventories are deliberately conservative: support for a listed slice
must not be read as full Rust or full trust-ir replacement readiness.

## Implementation highlights

- **Typed lowering boundaries.** Separate dialect, low-level, machine, and
  target encoding layers keep validation and provenance attached to explicit
  transformations.
- **Post-lowering checks.** Register-allocation, data-flow, encoder, relocation,
  and JIT publication paths contain target-specific fail-closed validators.
- **Solver integration.** Proof obligations can be serialized to SMT-LIB and
  discharged through an external AY solver process; selected paths carry
  replayable SAT certificates.
- **CEGIS and superoptimization experiments.** Candidate rewrites are searched,
  checked for equivalence, and cached behind opt-in controls.
- **Glass-box diagnostics.** Compilation traces, structured metrics, proof
  reports, source provenance, and JIT diagnostic bundles are first-class data.

Research-track code is not automatically a supported product surface. The
capability grid and [`LIMITATIONS.md`](LIMITATIONS.md) are authoritative over
aspirational descriptions in [`VISION.md`](VISION.md).

## Similar projects

trust-cg shares ideas with several mature systems but has a different center of
gravity:

| Project | Primary focus | Relationship to trust-cg |
| --- | --- | --- |
| [LLVM](https://llvm.org/) | Production-quality, general-purpose optimizing compiler infrastructure with broad target and language support. | The main compatibility and differential-testing reference; trust-cg is far smaller and far less complete, with proof evidence as a design constraint. |
| [Cranelift](https://cranelift.dev/) | Fast, secure code generation and JIT infrastructure in Rust. | A useful Rust backend reference; trust-cg places more emphasis on proof-carrying inputs and per-transformation evidence. |
| [CompCert](https://compcert.org/) | A machine-checked optimizing C compiler, principally proved in Coq. | The standard for end-to-end compiler-correctness claims; trust-cg does not yet meet this proof bar and targets a different IR/multi-language architecture. |
| [Alive2](https://alive2.llvm.org/) | Translation validation and refinement checking for LLVM IR transformations. | A close methodological reference for solver-backed equivalence; trust-cg applies related ideas inside a native backend pipeline. |

These are reference points, not drop-in substitutes. Choose LLVM or Cranelift
for mature production code generation today; evaluate trust-cg when explicit
proof obligations, inspectable evidence, and proof-carrying IR are the subject
of the work.

## Benchmarks and SAT-Comp 2026

This repository includes a SAT-Competition 2026 No-Limits submission that uses
trust-cg to JIT a proof-carrying Boolean-constraint-propagation kernel inside
MicroSAT. It is a verification and systems experiment, not evidence that
trust-cg or the resulting solver outperforms production compilers or SAT
solvers end to end.

Build the StarExec entry point on Linux x86-64:

```bash
./starexec_build
./starexec_run_default.sh instance.cnf /tmp/trust-cg-sat/
```

Or reproduce that build in a Linux x86-64 container:

```bash
docker build --platform=linux/amd64 \
  -f docker/sat-comp-2026/Dockerfile \
  -t trust-cg-sat:sat-comp-2026 .
```

The [system description](satcomp_2026_system_description.md) states the solver
and proof boundary. The [benchmark study](benchmarks/benchmark_study.md)
contains methods, raw comparisons, checker results, limitations, and a visible
retraction of an earlier invalid end-to-end speed claim. The
[`metrics-contract.md`](metrics-contract.md) defines the evidence required for
new performance claims. This README intentionally makes no aggregate compiler
performance claim for v0.1.0.

## Roadmap

1. **Ship a reproducible 0.x source release.** Keep the public dependency graph,
   examples, license inventory, and release validation green from a fresh
   anonymous clone.
2. **Define and expand the supported envelope.** Close trust-ir semantic, ABI,
   aggregate, object, TLS, unwind, debug, SIMD, and atomic gaps with positive
   and fail-closed negative tests.
3. **Reach AArch64/x86-64 parity.** Hold both primary targets to the same
   semantic and evidence contract, allowing only documented platform ABI
   differences.
4. **Strengthen the proof chain.** Replace statistical credits with solver or
   checker-backed evidence, bind certificates to exact emitted artifacts, and
   reduce the trusted base.
5. **Stabilize integration surfaces.** Mature the CLI/file formats, the
   `rustc` bridge, diagnostics, and embedding APIs before making compatibility
   guarantees.
6. **Publish reproducible performance evidence.** Preserve inputs, revisions,
   resource envelopes, wrong/invalid counts, and checker verdicts for every
   comparison.

The 1.0 bar is a stable backend for a documented trust-ir surface on AArch64
and x86-64, with reproducible distribution, target parity, and a proof policy
whose claims survive independent checking. It is not merely a version-number
milestone.

<details>
<summary><strong>Repository layout</strong></summary>

## Repository layout

| Path | Purpose |
| --- | --- |
| `crates/trust-cg-cli` | The `trust-cg` command-line driver. |
| `crates/trust-cg-dialect`, `trust-cg-lower` | Dialect conversion, trust-ir adaptation, ABI lowering, and instruction selection. |
| `crates/trust-cg-ir` | Shared machine IR, registers, provenance, and compilation traces. |
| `crates/trust-cg-opt` | Optimization passes, rewrite infrastructure, PGO, and vectorization. |
| `crates/trust-cg-regalloc` | Liveness, register allocation, spills, coalescing, and validation. |
| `crates/trust-cg-codegen` | Target encoders, object writers, JIT, debug/unwind, and compiler orchestration. |
| `crates/trust-cg-verify` | Proof obligations, evaluators, solver bridge, certificates, proof database, and CEGIS. |
| `crates/rustc-codegen-trust-cg` | Separate nightly rustc codegen-backend bridge. |
| `crates/trust-cg-test`, `trust-cg-fuzz` | Unified validation commands and differential fuzzing. |
| `formal/lean`, `proofs` | Formal models, selected proofs, and proof fixtures. |
| `benchmarks`, `reports/perf` | Reproducible benchmark definitions and preserved results. |
| `scripts` | Test, proof, soundness, fuzz, and release-support commands. |

</details>

## Developing

Start with the narrowest test that covers a change, then broaden it:

```bash
cargo check --locked --workspace --all-targets
cargo test --locked -p trust-cg-cli
cargo test --locked -p trust-cg-codegen --test e2e_cli_tmbc
cargo test --locked -p trust-cg-verify
```

The broader local matrix is:

```bash
scripts/run_full_test_matrix.sh
```

It automatically assigns every otherwise-unlisted integration target to a
bounded shard and exits nonzero for any failed, timed-out, skipped, or
incomplete shard. Use `--report-only` only when collecting a deliberately
non-gating historical measurement.

Bug reports should include the target triple, optimization level, input format,
the smallest reproducer available, and `--trace --metrics` output. Correctness
changes should add both a positive regression and, when applicable, a
fail-closed negative test.

Contribution basics are in [`CONTRIBUTING.md`](CONTRIBUTING.md). See
[`SUPPORT.md`](SUPPORT.md) for help, [`SECURITY.md`](SECURITY.md) for private
vulnerability reports, and [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) for
community expectations. Release changes are recorded in
[`CHANGELOG.md`](CHANGELOG.md).

## License

Apache License 2.0. See [`LICENSE`](LICENSE). trust-cg was created by Andrew
Yates.

Vendored and externally fetched third-party components retain their own licenses.
Their provenance and terms are recorded in [`THIRD_PARTY.md`](THIRD_PARTY.md).
