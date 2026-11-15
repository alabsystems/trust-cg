<div align="center">
  <h1>trust-cg</h1>
  <p><strong>Lower trust-ir. Emit native code. Inspect the evidence.</strong></p>
  <p>A proof-oriented compiler backend in Rust for AArch64 and x86-64, with
  bounded RISC-V 64 AOT and WebAssembly paths.</p>
  <p>
    <a href="#quick-start">Quick start</a> ·
    <a href="#understand-and-check-the-evidence">Check the evidence</a> ·
    <a href="#use-trust-cg">Use trust-cg</a> ·
    <a href="#capability-grid">Capabilities</a> ·
    <a href="ARCHITECTURE.md">Architecture</a> ·
    <a href="LIMITATIONS.md">Limitations</a> ·
    <a href="#benchmarks-and-sat-comp-2026">Benchmarks</a> ·
    <a href="#roadmap">Roadmap</a> ·
    <a href="https://github.com/alabsystems/trust-cg/issues">Issues</a>
  </p>
</div>

## What is trust-cg?

trust-cg translates [trust-ir](https://github.com/alabsystems/trust-ir) modules
into native object code. Its pipeline includes input and translation checks,
instruction selection, optimization, register allocation, machine-code encoding, object
emission, and JIT support. Verification is part of the pipeline rather than a
separate afterthought: lowering rules carry proof obligations, evidence records
its strength, and proof-required modes reject output that cannot satisfy their
configured authority policy.

```text
  trust-ir (.tmbc; text/JSON for debugging)
                         │
                         ▼
  input admission → lower → optimize → register allocate
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
     Mach-O / ELF / COFF       in-process JIT
              │                     │
              └──────────┬──────────┘
                         ▼
       traces, proof reports, and optional sidecars
```

A separate `wasm32` lane emits `.wasm` without the native register allocator.
The CLI compiles closed modules, or relocatable objects that `wasm-ld` links;
the library also implements explicit host-island imports and
shared-memory/stack contracts.

**Current implementation:** trust-cg is a working multi-target compiler backend
with a Trust-pinned Rust codegen bridge. AArch64 and x86-64 have independent
native pipelines, optimizers, allocators, encoders, object writers and JITs.
RISC-V has a bounded integer AOT pipeline. wasm32 has a relocatable object
pipeline and a bounded Rust bridge lane. The Rust bridge lowers substantial
MIR, ABI, static-data and runtime behavior and has native LLVM differential
tests. The LLVM text importer and standalone ONNX protobuf-to-VNN importer
are separate implemented components.
See the [source audit](ARCHITECTURE.md#source-audit-and-capability-boundaries)
for the implementation and its exact boundaries.

The October 14 alignment and completeness audit
reconciles the diverged local/upstream histories and checks that snapshot against
its completion claims. The current source ledger
records 237 gaps: **42 closed, 152 partial and 43 open; 195 remain unresolved**.
The platform queue records the incremental changes.
All fourteen acceptance rows on each of Linux AArch64, Darwin
AArch64 and Linux x86-64 remain open. These are engineering and acceptance
records, not a percentage of compiler completeness. The audit distinguishes
source findings from the dated measurements below. Ledger status counts do not
certify the integrity of every historical evidence record; the queue discloses
missing historical temporary records and the scope of fresh retained checks.

The October 1 real-source audit records
Rust bridge repairs for cleanup storage, projected borrow types, loop headers
and allocator signatures. That checkpoint's complete Linux AArch64 dependency graph,
sealed candidate 21, retains 441 required refusals. CG `core` and `alloc`
artifacts are present. Its latest completed whole-std diagnostic is candidate
17: it uses 13 explicit LLVM dependencies and retains 114 refusals. Candidate
21's newer std-body replay times out and supplies no completed census. Independent
O0–O3 LLVM/CG controls pass for memory-only loops, projected scalar borrows,
nested cleanup-cell temporaries, raw-pointer loops, reference copies and normal/panic ownership
cleanup. The later memory-libcall repair passes eight independent ABI cells.
The sealed candidate26 constructed-map repair preserves 52 native heap-glue comparisons
while rejecting incoming LLVM-created maps at the exact vtable guard. The merged
candidate27 and candidate28 owning tests failed at those checkpoints because
two required `dyn_vec` cases at O2/O3 reached the then-unsupported canonical
bounds-panic route. Their source-bound failures are recorded
in the October 1 audit.
These are scoped native correctness diagnostics with frontend verification
and backend certificates disabled. A complete CG-built sysroot remains open.
Linux's separately dated bound-memory checker qualification records 72 exact
committed proof-query replays and 53 focused proof controls; the newer native
campaigns add no proof credit. Candidate28's merged memory-effect controls pass
34 selected Rust tests; exact instruction-word binding and refuted-part rejection
do not establish a new live Linux proof replay. The
reproduction workflow keeps these evidence lanes explicit.

**October 1 Linux checkpoint (source30):** source `b422f87fd`, pinned to
TrustIR `dee0ab3b`, passes all 24 focused groups and 296 executed test methods.
Its four heap-glue tests restore 52 owning/borrowed LLVM/CG comparisons;
candidate27/28's bounds-panic refusals remain historical failures. Eight fresh
memory ABI cells pass 108,480 checks and 48 layouts. Panic-hook and Linux EH
controls pass their selected scopes; foreign unwinding under `panic=abort`
still refuses on Linux. All 41 public commands exit zero with no failed Rust
assertions, including four-package Tippy. The original public aggregate remains
false: the optimizer emits 4,099 parent passes plus 34 child summaries where
the recorder expects one summary, and the Wasm fixture records missing Node
and linker skips. Wasm receives no runtime or link credit. Six ordinary Clean
ByteV1 consumer controls also pass without skips; this bounded proof-consumer
result is separate from native code and EH qualification. Scoped private Tippy
also completes, retaining 350 library warnings. See the
current-status audit
for exact scopes. This supplies no new std census, full private-suite,
CG-built std/sysroot, Darwin or complete formal qualification.

The October 4 iterator/header integration
recorded a complete original-library census with 437 refusals, a completed
std-body diagnostic with 117 refusals and 13 explicit LLVM dependencies, and
the unchanged consumer matrix at 24/40. Its selected native/unit suites pass
620 methods, including strengthened ownership expectations. An independent
LLVM callback probe found a buffer leak when an admitted by-value
Copy-element iterator payload unwound. Later upstream ownership repairs supersede
that defect record; the October 14 merge does not remeasure the old census.
Full CG-built std/sysroot and every
L01–L14/platform requirement remain open; certificates-default controls still
refuse and these native results supply no formal credit.

The later source31 checkpoint at `e85cf9b5c`, pinned to TrustIR `8cf20223`,
passes 24 selected rows and 172 Rust methods without failures or skips. It
checks the optimizer/SSA refactors, repairs prefetch startup/shutdown ordering,
and exercises exact-query memo, controlled probe and changed binary contracts.
Public format and four-package Tippy pass; private-library Tippy retains 350
warnings. These results add no source30 native-result transfer, live solver
proof or new std/sysroot census. See the
dated source31 record.

The September 29 x86-64 Linux report records zero failed O3 `core` lowering
roots across 1,285 objects. This is an object-generation result using
`no-proof-certs`; whole `std`, self-hosting, native correctness and proof
qualification remain separate requirements. See the
completion evidence and
consolidation audit.

**Qualification:** version 0.7.0 retains the 0.x research-preview release tier.
Readiness varies by target, input shape, ABI and evidence policy. Whole Rust/std
and self-hosting acceptance remain open, and supported native compilation is
broader than certified compilation. This release tier does not describe the
amount of implemented compiler functionality. The root workspace, Rust bridge
and cargo-fuzz workspace have separate builds and tests.

Verification includes structural translation validation, bounded source-bound
proofs, independently replayed AY/Clean certificates and exact artifact/cache
binding. Statistical checks remain testing evidence and never receive formal
proof credit. These mechanisms do not constitute an end-to-end proof of every
frontend, optimization and emitted binary. [LIMITATIONS.md](LIMITATIONS.md)
states the known correctness defects, input contracts and trusted boundaries;
dated test and benchmark records qualify only their named revisions and hosts.

The October 1 TrustIR v52 adoption keeps source assertion panic kinds and
failure-only operands in diagnostic execution. Native and WebAssembly routes
currently refuse source `Inst::Assert` rather than erase a Rust panic into a
machine trap; this temporarily removes earlier trap-only assertion coverage.
Internal checked guards and Assert-free native programs remain separate.
See the migration record
for the capability loss. The separate Rust MIR bridge now resolves exact
panic lang items and their actual ABI. Its ARM64/macOS diagnostic differential
executes fourteen assertion forms at O0–O3 with abort/unwind, checking payloads,
full caller locations, hooks, cleanup and catch behavior. This does not admit
general TrustIR assertions, certify EH or qualify another target; see the
native bridge record.

## Quick start

Build from source with the Trust toolchain: `rust-toolchain.toml` pins
`channel = "trust"`, and the build runs with an installed Trust package's
`targo` (its explicit `--unverified` lane makes no verification claim about the
build). Install [aterm](https://github.com/alabsystems/aterm#install) and atpkg
installs that package (Apple-silicon macOS only; no other platform has a public
Trust package or supported install path today). The runnable example also needs
a host C compiler. Maintained tests cover macOS and Linux; Linux evidence
uses private, tree-built Trust toolchains.

```bash
git clone https://github.com/alabsystems/trust-cg.git
cd trust-cg
targo --unverified build --release --locked -p trust-cg-cli --bin trust-cg
```

Compile the included text-format trust-ir module for the current host, link it
to a small C driver, and run it. It prints `42`.

```bash
HOST_TARGET="$(trustc -vV | sed -n 's/^host: //p')"

target/release/trust-cg \
  --format=text \
  --target "$HOST_TARGET" \
  -O0 -c examples/return_42.trust_ir \
  -o target/return_42.o

cc examples/return_42.c target/return_42.o -o target/return_42
target/return_42
```

`targo` builds with its own package's `trustc` whatever else is on PATH;
`scripts/trust_toolchain.py` checks that the PATH `trustc`/`targo` pair is one
branded package.

## Understand and check the evidence

“Verified” is not one binary property in trust-cg. Evidence is recorded at
different strengths, and those strengths must not be conflated:

| Lane | What it establishes | Command or entry point |
| --- | --- | --- |
| Exhaustive evaluator | Equality over the complete bounded input space used by a small-width obligation. | `targo --unverified test --locked -p trust-cg-verify` |
| Statistical evaluator | Equality on edge cases and sampled 32/64-bit inputs. Useful regression evidence, **not a proof over all inputs**. | Included in the default verifier tests. |
| Solver discharge | AY produced a proof of a supported SMT obligation, independently checked by Clean. Timeouts and `unknown` are not proofs. | `scripts/check_proof_gate.sh` |
| Certificate-required compilation | Every required report for that compilation was promoted under the configured policy; missing, unknown, timed-out, or unsupported evidence rejects publication. | `trust-cg --emit-proofs=<DIR> ...` |
| Independent replay | A separately implemented checker accepted a supported serialized artifact. Available on named paths only, not for every emitted certificate. | Vendored `drat-trim` gates, build-embedded portable canary certificates that replay without AY, and the cross-repo soundness suite. |

AY is the sole SMT solver, and exactly one AY may answer: the `ay` shipped in
the sysroot of the Trust compiler that owns the code — the compiler hosting the
process (a backend loaded into `trustc`), otherwise the compiler that built the
crate. It is admitted only when the SHA-256 of its bytes equals the digest
recorded from that toolchain's `bin/ay` when `trust-cg-verify` was built (the
recorded build banner is kept as a label). Nothing is executed to decide this,
and a script that merely prints the pinned `--version` banner is refused. A
missing, unreadable or different AY is refused with a named `TCG-AY-IDENTITY-*`
error; aterm's separately managed AY package, `PATH`, and source checkouts are
never consulted (`crates/trust-cg-verify/src/ay_identity.rs`, which also states
what remains trusted). Every AY process is started from that admitted value,
and never from the admitted path: AY re-executes itself by its own path at
startup (its kernel memory governor), so the admitted bytes are copied into a
private content-addressed file (`<user cache>/trust-cg/ay-exec/<sha256>/ay`,
directory `0700`, file `0500`, owned by the user) and AY is started from that
copy, after re-checking that neither the admitted file nor the copy changed.
`<user cache>` is an absolute `XDG_CACHE_HOME`, else an absolute `HOME`'s
`.cache`; an empty or relative `XDG_CACHE_HOME` is ignored and a relative
`HOME` names no cache (AY is then refused), so `--print-ay-identity`, each
function-verification request and the refusal note resolve the same copy
whatever the working directory (one rule for every trust-cg cache root and
the gate scripts).
Every cache directory trust-cg or one of its gate scripts creates is `0700`
whatever the umask (`scripts/private_cache.py` is the scripts' copy of the
rule), and the builds those scripts run under the cache write under umask 077
(LIMITATIONS.md names what the umask does not govern: a build's copies of
files, and default ACLs); a directory that already
exists is never changed, and if it or any other ancestor of the copy
is writable by group or others (not sticky), AY is refused with
`TCG-AY-IDENTITY-UNMATERIALIZED`, naming the directory and the remedy, and a
proof-promotion refusal that follows carries that reason.
A new copy is a new executable, and macOS holds its first start until it has
assessed the file (measured 2026-09-27: up to 32.2 s for the 158 MB toolchain
AY on a busy host, then 0.01-0.04 s for later starts). So that first start is
made as `ay --version` before any solver deadline starts, at most once per
process and only while no completed first start of that copy is recorded
beside it: a compile's warm thread makes it early for a copy it published,
and a query that needs the copy meanwhile waits for it.
Verdicts record which AY
produced them (`ay_bridge::verify_with_ay_attributed`, the strict gate report,
formal lowering certificates, codegen `Formal` evidence). In ordinary builds,
the independent Clean proof checker comes from the same toolchain: its
`bin/clean` is tried first, and aterm's managed package channel (not the `alab-*` launcher scripts) only
when that toolchain ships no capable checker. A checker must read the proofs
of the AY it is paired with: on **2026-09-27** the managed Clean build 8606
passed the control proof below but rejected the `poly_simp` bit-vector steps
of the toolchain AY (ay 0.27.0, commit 3211f7fc7, Trust 450403669e), while
that toolchain's own `clean` fully verified them. Either way, Clean must pass a
control-proof check before it is accepted as proof authority.

Inspect the installed Clean package with `aterm pkg doctor` and
`aterm pkg which clean`. Clean must include its `carcara-verify` capability.
trust-cg decides that by running its own control proof, a one-step Alethe
resolution refutation of `p` and `not p` checked with
`clean cert verify-external <certificate> --verbose`, never from a package
name or feature list. On **2026-09-18** on the maintainer's macOS arm64 host,
`aterm pkg which clean` resolved the managed Clean build **8606** (`clean 0.9.0`,
executable SHA-256 `9c594e838ff7e73815977c2d675238828f82417e77986abfe38d75b8ab060e16`).
That exact probe printed `External certificate verification: PASSED` with
`Proof status: fully verified`. The `clean` bundled in the installed Trust
package (build 9192, also `clean 0.9.0`) failed the same probe with
`carcara-verify feature required for tier 1 verification`; on such a toolchain
default discovery skips its `clean` (with a one-line notice) and uses the
managed package. The Trust toolchain sealed from 450403669e ships a `clean`
that passes the probe.
These are one host's package facts on that date, not a property of every
installation: each process re-probes its checker, a checker that fails the probe
is refused as proof authority, and a missing or incapable checker still makes the
proof gate fail. The earlier Clean build 7345 (rechecked 2026-09-09) lacked the
feature. Diagnostics identify AY separately from Clean's
proof-checking capability; reporting AY's path does not authorize a proof.
A missing or incapable checker is not evidence
that another SMT solver is needed; Z3 is not a fallback.
With a capable development checker, aterm's managed AY package (which trust-cg
no longer selects) also refused the canonical PBLENDVB obligation during its own
strict proof check; that measurement has not been repeated with the toolchain
AY. The full formal gate is not green.

For toolchain development only, `AY_SOLVER_PATH` and
`TCG_EXTERNAL_CLEAN_CHECKER` select explicit executable paths (the latter's
legacy alias is `TCG_CLEAN_CHECKER`). `AY_SOLVER_PATH` must be absolute and is
checked like the toolchain AY, so it can name another copy of the recorded AY's
exact bytes but never a different build. Invalid overrides do not silently fall
back to a different tool.

A local [overlay toolchain](scripts/assemble_trust_overlay.py) supplies an
additional checker pin. At build time, `overlay.json` must match the recorded
AY digest, commit and build number and the bytes of `bin/clean`; an invalid
manifest records no usable tool identity. An overlay build accepts only that
Clean digest, including for explicit overrides, and never falls back to a managed checker. Capability
probing and independent proof checking still apply. The manifest is unsigned,
and its Clean source commit is an assembler-provided label; it does not establish
tool correctness or turn an overlay into a published Trust pack.

Run a short solver-backed smoke check, or the full proof-database gate
(the script's default, and substantially slower):

```bash
scripts/check_proof_gate.sh --test representative_arithmetic_is_formally_verified
scripts/check_proof_gate.sh --test full_database_is_formally_verified
```

CLI certified proof output is fail-closed. For example:

```bash
target/release/trust-cg \
  --target "$HOST_TARGET" \
  -O0 -c module.tmbc \
  --emit-proofs=target/module-proofs \
  -o target/module.o
```

On a supported path this writes the available certificate records and, where
present, SMT-LIB obligations and function-level sidecars. Emitting a record does not by itself make
the result independently certified: exports are unsigned and carry a null
signature field, and relocation or opcode coverage gaps cause the command to
fail rather than silently claim a complete proof.

Library callers must distinguish report emission from certified export.
With `CompilerConfig::emit_proofs` every unverified report, sampled evidence
included, blocks promotion, as it does for the CLI. Inspect the returned
strengths and verdicts; a report records what was checked, not a proof of the
whole function.

Native certified export is currently narrow. The tested AArch64 Darwin identity
function lowers to a return and exports structural/relocation audit records;
it has no instruction-lowering SMT or per-function sidecar to export. The
general arithmetic paths still include sampled obligations; floating comparisons
and ELF calling frames also emit instructions without opcode-wide proof mappings.
Those paths reject before object publication when `--emit-proofs` is requested.
Compiling without that option does not upgrade their evidence.

Pure unconditional-jump loops have a bounded source-bound proof route. The
verifier matches the complete LIR and allocated machine control graphs, then
requires independent replay of every decoded B word's next-PC equality.
This does not cover value-carrying loops, calls or exception handling; the
Rust source/graph binder and the existing final-byte checks remain separate
parts of the trusted boundary.

Bounded Linux AArch64 affine leaves can now use independently replayed frame
and arithmetic proofs after checking their complete source and machine bodies.
Required JIT tests execute ADD/SUB and optimized doubling at O0–O3 for I32,
U32, I64 and U64, and independently compare the published bytes with the source.
The unchanged 160-case Linux matrix now also credits single MOVZ/MOVN constants
and live register copies. Copy credit requires a raw source/result theorem
replayed by AY and independent Clean, after the Rust source/frame gate.
Only copies in the return's backward slice qualify; unused register-formal
copies are removed before allocation. The
body-credit record
retains the query, export and mutation boundaries; it closes no completion row.
Their arithmetic AOT exports retain the exact operand-specific theorem and
independently replay it before publishing the object and lowering sidecars.
The required CLI matrix exports and executes all 48 type/shape/optimization
cases; same-named obligations with different operands remain distinct. Its
maintained runner is
[`scripts/check_aarch64_aot_arithmetic.py`](scripts/check_aarch64_aot_arithmetic.py),
which also audits every sidecar against its object, checks on Linux that the
`cc`-linked executable carries the certified function's words and unwind entry
at its link-time address (the runner's byte comparison, not a certificate over
the linked image), independently re-solves and checks every exported query,
and requires its three recorded corruption controls to be rejected. The [retained maintained-runner qualification](reports/perf/2026-09-20-maintained-arithmetic-aot/README.md)
passes all 48 cases and 6,912 native calls on the installed Linux compiler,
independently accepts all nine original certificates and rejects all 27
corruptions. Its exact source and tool identities are archived. The
[2026-09-23 linked-image record](reports/perf/2026-09-23-linux-linked-image-binding/README.md)
adds the linked-image step: all 48 executables are bound and all 144
linked-image negatives are refused. On Darwin the runner reports an export
refusal as a failure instead of skipping it.
See [the supported boundary](LIMITATIONS.md) for the remaining restrictions.

For several inputs, proof output is separated into `input_0/`, `input_1/`, and
so on under the requested proof directory, in input order. This keeps private
functions with the same name in different modules from overwriting each
other's sidecars. A single input retains the direct directory layout.

The broadest repository gate is [`scripts/soundness_check.sh`](scripts/soundness_check.sh).
It runs the configured trust-cg and Clean checks — the coverage inventory,
meta-theorems, mutation catalog, strict proof gate, the differential B-def
bridges, and the wasm encoding/CFG/ABI families — and records the companion
[AY](https://github.com/alabsystems/ay) revision as evidence provenance. It is
a local, cross-repository release-engineering gate and therefore requires
sibling checkouts; see [`SOUNDNESS_CHECK.md`](SOUNDNESS_CHECK.md) for its exact
trust boundary and prerequisites.
Its Cargo gates validate captured named results, rejecting ignored cases,
runtime skips, and incomplete output rather than trusting the final rollup.
Missing prerequisites or unrequested formal campaigns make the overall gate
nonzero and prevent re-pinning; complete formal execution requires
`TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` and capable managed AY/Clean tools.
The wasm encoding gate explicitly includes its exhaustive signed-i32
encoder sweep; VT-island inputs can be exported from an exact aterm commit with
the maintained provenance-recording exporter described in the soundness guide.

The Lean development under [`formal/lean`](formal/lean) proves selected
forward-simulation and encoding properties. It still contains classified proof
gaps and explicit axioms, so trust-cg does not claim a CompCert-style
end-to-end theorem for the entire compiler.

## Use trust-cg

The `trust-cg` executable accepts one or more trust-ir modules:
`trust-cg [OPTIONS] <INPUT>...`.

### Input formats

| Format | Flag | Intended use |
| --- | --- | --- |
| Binary tMBC (`.tmbc`) | Default | Canonical tool-to-tool input. |
| Human-readable trust-ir (`.trust_ir`) | `--format=text` | Debugging, review, and small examples. |
| JSON | `--format=json` | Debugging and external-tool integration. |
| Extension/magic detection | `--format=auto` | Compatibility with mixed legacy fixture trees. |

### Targets

`--target` accepts `aarch64` (the default), `x86_64` and its triples,
`riscv64`, and `wasm32-unknown-unknown` (alias `wasm32`). x86 support is
x86_64 only; 32-bit aliases and triples are rejected. The wasm32 lane runs no
optimization passes and has no WASI or emscripten imports. One input without
`-c` becomes a closed module; `-c` writes each input as a relocatable wasm
object (`<input>.o`); several inputs are compiled to objects and linked by
`wasm-ld` (`--wasm-ld`, `$WASM_LD`, or `wasm-ld` / `rust-lld` on `PATH`),
which also receives `-L`, `-l` and `-Wl`. Options the lane cannot honor are
refused by name.

```bash
# One module to an object file
trust-cg -O0 -c --target aarch64-apple-darwin input.tmbc -o input.o

# Several modules compiled, then linked by the system linker
trust-cg -O0 --target x86_64-unknown-linux-gnu app.tmbc support.tmbc -o app

# wasm32: a relocatable object, or several modules linked by wasm-ld
trust-cg --target wasm32 -c input.tmbc -o input.o
trust-cg --target wasm32 app.tmbc support.tmbc -o app.wasm

# Traces, machine-readable metrics, and the bounded UB preflight
trust-cg -O0 -c input.tmbc -o input.o --trace --metrics
trust-cg -O0 -c input.tmbc -o input.o --fsym=warn --fsym-report-json=fsym.json

# Dump a binary module to the reviewable text form
trust-cg -O0 -c input.tmbc -o input.o --emit-trust_ir=input.trust_ir

# A Linux shared object, and each object's runtime dependencies
trust-cg --target aarch64-unknown-linux-gnu -shared -soname libapp.so.1 \
  -rpath '$ORIGIN' -Wl,-z,text app.tmbc -o libapp.so --emit-runtime-deps deps.json
```

The link step runs the host `cc`. `-shared`, `-pie`/`-no-pie`, `-static`,
`-nostdlib`, `-soname`, `-rpath` (also spelled with `--`) and validated
`-Wl,<args>` groups are accepted; contradictory or target-inapplicable
combinations (for example `-static` on Darwin) and `-Wl` groups naming a
typed option are refused by name before any input is read. Linux links always
pass `-Wl,-z,noexecstack`, and a `-Wl` group requesting an executable stack is
refused. trust-cg emits no BTI landing pads or PAC instructions, so the BTI/PAC
requests `-z force-bti`, `-z pac-plt` and `-z bti-report` are refused with
`[TCG-LINK-BTI-PAC]`. A failed link keeps
the linker's own output and adds one `error[link:<kind>]` line per recognized
diagnostic (undefined or duplicate symbol, text relocation, relocation out of
range, non-PIC relocation in a shared object, missing library, local-exec TLS
in a shared object, a thread-local symbol paired with a non-thread-local one).
A `-shared` link whose AArch64 ELF input objects contain a local-exec TLS
relocation, which the `static` and `pie` relocation models emit for a
thread-local the module defines, is refused before the linker runs with
`error[link:tls-model-mismatch]` and `[TCG-LINK-TLS-MODEL]`, because GNU ld
2.42 would link it into a library that addresses the executable's TLS block;
compile such a library with `--relocation-model pic`. Its data and function
twin is refused the same way on every linker, with
`error[link:non-pic-relocation]` and `[TCG-LINK-PREEMPTIBLE-DIRECT]`: a
direct-address relocation (`ADRP`/`ADD`/`LDST` lo12 and the other
position-dependent address forms, the conditional branches `CBZ`/`CBNZ`/`B.cond`
and `TBZ`/`TBNZ`, and the local-dynamic TLS forms) against a
default-visibility symbol no input hides, which gold 2.42 (and, for the
conditional branches and local-dynamic TLS, GNU ld 2.42) would bind inside
the library where the dynamic loader binds it elsewhere; a name the linker binds inside the output (`__start_<sec>`,
`__ehdr_start`) or another input hides is exempt only while no `-Wl` option
can define, re-bind or redirect it (`--wrap` of either, `--defsym` of a
linker-defined one, a linker script option) and the image's dynamic symbol
table does not export it with default visibility. A Linux shared-object link of objects the CLI compiled `static`
or `pie` that define a default-visibility symbol is refused too, with
`error[link:non-pic-definition]` and `[TCG-LINK-PREEMPTIBLE-DEFINITION]`:
their code may have inlined or folded the uses an interposer must reach.
`--shared` without `--relocation-model` compiles AArch64 Linux modules
`pic`. On Linux a `-Wl`
group may not name a typed option in any spelling GNU ld 2.42 reads as one:
one or two dashes, any prefix of the long name (`-shar`, `--outp=<file>`),
the joined short forms `-o<file>`, `-h<name>` and `-R<dir>`, or a bare `-G`.
Other options that begin with `o` or `h` need two dashes there
(`--omagic`, `--hash-style=gnu`). Every other link with such an input writes
to a fresh staging directory next to the output. The staged image is moved
onto the output only when it is an executable (`ET_EXEC`, or `ET_DYN` marked
`DF_1_PIE`) or a relocatable object. Otherwise it is removed and refused with
the same kind. A link that exits successfully without writing the staged
image (for example `-Wl,--version`) is refused with `[TCG-LINK-NO-OUTPUT]`.
No refusal touches a file already at the output path. No forwarded value
(the output or an input path, `-L`, `-l`, the soname or a run-time search
path) may begin with `@`. The C driver, collect2 and GNU ld read such an
argument as a response file of further, unchecked link arguments, so it is
refused with `[TCG-LINK-RESPONSE-FILE]`; spell such a path `./@...`.
Positional AArch64 ELF64 relocatable inputs are scanned before the link. On
Linux every link that is not a plain `-nostdlib` executable link (every
`--shared` link, every link with the C runtime, every link with a `-l`
library or a `-Wl` group, every link with a positional input the AArch64
ELF reader cannot read, which includes every non-AArch64 link, and every
link with a positional object that embeds LLVM bitcode in a `.llvm.lto`
section) is also
staged with the linker's input trace (`-Wl,--trace,--trace`); a staged link
refuses `-o /dev/null`. When its image is not an
executable, every AArch64 ELF relocatable object the trace names is read: a
`-Wl` operand (`-Wl,le.o`), a `-l:<file>` library, a regular or thin archive
member, a file a linker script's `INPUT()` or `GROUP()` names. A local-exec
relocation in any of them refuses the image with `[TCG-LINK-TLS-MODEL]`
naming that input, and a trace that does not show what was loaded (for
example with `-Wl,--verbose`, which prints other text) is refused with
`[TCG-LINK-INPUT-TRACE]`. The trace does not name the objects LLD 22.1.6
compiles from LLVM bitcode, so the driver runs the link again with its own
`--lto-obj-path` and an empty `--thinlto-cache-dir=` after the user's
options, and reads them. It does this in three cases:
- the trace names bitcode, or an ELF relocatable object that is not AArch64
  LP64 (LLD links one only through its `.llvm.lto` bitcode);
- the `-Wl` groups turn on `--fat-lto-objects`;
- LLD's link map places input sections of a file the trace does not name,
  as when the C driver adds that option itself.

An image is refused by name (`[TCG-LINK-LTO-OBJECTS-UNREAD]`) when a check
that reads every loaded input (the local-exec check above, the GOT checks
below) needs the compiled code and the driver has not shown it read. That
happens in three cases:
- a counted input's compiled objects were not read;
- the checked link's map places more files the trace does not name than
  the driver read compiled objects;
- that map is not read while a loaded AArch64 object embeds `.llvm.lto`
  bitcode.

When its image is not shown to keep every
GOT-addressing access within its window of every place a slot can lie, the
same traced inputs are read for the aaelf64 relocations that address a GOT
slot from the place they patch (the `ADRP` page kinds, +-4 GiB; the
load-literal and `ADR` kinds such as `TLSIE_LD_GOTTPREL_PREL19` and
`TLSGD_ADR_PREL21`, +-1 MiB; `GOTPCREL32` and the PAuth forms), for the
`LDR` forms that measure a slot from the GOT base (`LD64_GOTPAGE_LO15`,
GCC's `-fpic` GOT load, which LLD 22 writes truncated, and
`LD64_GOTOFF_LO15`: 32 KiB above `_GLOBAL_OFFSET_TABLE_` or its page, which
the image's symbol table must give) and for
`STT_GNU_IFUNC` definitions, whose IPLT a linker script can hide, and one
in any of them refuses the image by name (`[TCG-LINK-GOT-PAGE-WINDOW]`,
`[TCG-LINK-GOT-PAGE-UNPROVEN]`, or `[TCG-LINK-GOT-PAGE-UNCHECKED]` for an
image that cannot be read); the C driver's own start files carry such
relocations, which is why a link with the C runtime is traced. An image
whose code and possible slots are more than 1 MiB apart therefore needs a
readable trace. An image not in page reach is also refused, whatever its
inputs, when it holds GOT-addressing code the linker wrote itself: a PLT, an
IPLT or the lazy TLS descriptor trampoline, whose `ADRP`s no input
relocation describes (a call to a PLT entry carries only
`R_AARCH64_CALL26`) and which GNU ld 2.42 does not check either; and so,
whatever its inputs, is an image whose GOT layout cannot be read, where
such code cannot be ruled out (`[TCG-LINK-GOT-PAGE-UNCHECKED]`). Every
Linux link is staged, a plain `-nostdlib` executable link too, and every
image's `.eh_frame` is decoded as an unwinder reads it: trust-cg's FDE,
personality and LSDA pointers are `R_AARCH64_PREL32` fields
(`-2^31 <= X < 2^31`), which gold 2.42 and LLD 22.1.6 write out of window
without a diagnostic, so an FDE outside executable memory, a personality or
LSDA pointer outside allocated memory or a `.eh_frame_hdr` table that
disagrees with the FDEs refuses the image (`[TCG-LINK-EH-FRAME-WINDOW]`),
as does one the check cannot complete (`[TCG-LINK-EH-FRAME-UNPROVEN]`),
including one whose link map (always the driver's own; a map a `-Wl`
group asks for is written from it) was not written or shows `.eh_frame`
input where it cannot be read whole, whatever registers it. An image the
dynamic loader cannot run is refused too: one that names a program
interpreter without a dynamic section (`[TCG-LINK-INTERP-NO-DYNAMIC]`), and
an `ET_EXEC` without an interpreter that needs shared libraries or holds
dynamic relocations, or a PIE without one whose relocations glibc's own
static-PIE start-up code does not apply (`[TCG-LINK-DYNAMIC-NO-INTERP]`); so
is the image of a `--static` link that names an interpreter or needs a
shared library (`[TCG-LINK-STATIC-DYNAMIC]`), a static executable with IFUNC
relocations that links no applier from the C driver's own `libc.a`, or
whose link can put something else in the place of glibc's start-up code (a
linker script, as an input or a `-l` library, `-z muldefs`, a `--defsym`
of one of its names; a `-Wl` piece is an option's value only as GNU ld,
gold and LLD were measured to read it, and a gold link runs once more with
`--debug=files` for the scripts it opened)
(`[TCG-LINK-IRELATIVE-UNAPPLIED]`), and a static executable whose registered
frames (`crtbeginT.o`'s) libgcc's walk does not reach in full where no
`.eh_frame_hdr` table entry does (`[TCG-LINK-EH-FRAME-UNPROVEN]`). A link
whose `-Wl` map option the driver cannot take from the linker (no usable
map path in the stage, `TMPDIR` or `/tmp`) is refused before it runs
(`[TCG-LINK-MAP-UNSTAGED]`), and so is one whose `--dependency-file` it
cannot stage beside that map (`[TCG-LINK-DEPFILE-UNSTAGED]`).
An image larger than 1 GiB (LLD writes a sparse one as long as the gap to a
section placed far from the ELF header) is read back as the ranges these
checks read, not whole; it is refused (`[TCG-LINK-IMAGE-UNCHECKED]`, naming
the cause) when those ranges come to more than 1 GiB or still grow after 64
runs of the checks.
A shared-library input applies no relocation and is
not scanned. A plain `-nostdlib` executable link is not traced, and links made outside
trust-cg, a file a linker writes at another path, and a file replaced between
the link and the read are not examined; see
[LIMITATIONS.md](LIMITATIONS.md). The CLI's `--pie`, `--no-pie`, `--static`
and `--nostdlib` links are checked by linking and running them and reading
the image kind (`ET_DYN` with `DF_1_PIE`, `ET_EXEC`, `PT_INTERP`) on the
Linux host.
`--emit-runtime-deps` (and `--metrics`) list every undefined symbol of each
object grouped by the runtime expected to provide it; the grouping is a name
table, not a check of any installed library.

Use `trust-cg --help` to see the options in the binary you built. The Rust
crates are usable in-tree, but their public APIs are not stable in the 0.x
series; the CLI and file formats are the intended evaluation surface.

`--no-parallel` makes both input-file compilation and per-module function
compilation sequential. Input reads are bounded to 512 MiB by default;
`TRUST_CG_MAX_INPUT_BYTES` can set a positive byte limit. An empty, malformed,
zero, or non-Unicode setting is rejected with a diagnostic instead of silently
falling back to the default. The bound applies to the bytes actually read,
including a file that grows after its initial size check.

The native CLI validates `TRUST_CG_MAX_PARALLELISM` as a positive integer before
reading inputs or publishing output. Invalid settings produce a diagnostic for
single-input and multi-input compilation, including `--no-parallel` runs.

Outputs must not alias inputs, profiles, or other requested outputs, including
through symbolic or hard links. On macOS and Windows, output names differing
only by case are conservatively rejected, even on case-sensitive volumes.
Combining `-c` with several inputs does not permit a shared `-o` path.
Publication across multiple output files is not an atomic transaction; an I/O
failure can leave a partial set of artifacts.

## Why trust-cg?

| Design choice | What it provides |
| --- | --- |
| Proof-aware input | trust-ir can carry the facts and provenance that justify later transformations instead of requiring the backend to rediscover all source-level intent. |
| Explicit evidence strength | Exhaustive, statistical, solver-proven, and independently replayed results remain distinguishable. |
| Fail-closed proof modes | A proof-required build can reject an unsupported opcode, relocation, or missing report before publishing an artifact. Register-allocation, data-flow, encoder, relocation, and JIT publication paths carry their own target-specific validators. |
| Solver integration | Proof obligations can be serialized to SMT-LIB and discharged through an external AY solver process; selected paths carry replayable SAT certificates. |
| Glass-box diagnostics | Typed IRs, compilation traces, structured metrics, proof reports, source provenance, and deterministic sidecars make lowering decisions auditable. |
| Differential validation | Native results are compared with independent trust-ir, clang/LLVM, and (for wasm) node execution paths on supported corpora. |
| One multi-target pipeline | AArch64 and x86-64 share validation, lowering, optimization, register allocation, and evidence infrastructure while retaining target-specific ABI and encoder checks. |

The architecture splits responsibility between producer and backend: a frontend
proves that its trust-ir represents the source program and attaches
optimization-authorizing facts; trust-cg preserves the accepted trust-ir
semantics while lowering to machine code. Important parts of that composition
are implemented, but not every pass and output format has complete proof
coverage. Missing proof metadata is therefore either a reason an optimization
does not fire or, on proof-required paths, a compilation error—it must never be
presented as stronger evidence than it is.

The bounded original-source observers also construct pending scalar-memory
relations from original Core to retained LIR, allocated AArch64 MachIR and
independently decoded final words. The writable profile reuses the existing
control/value engine with current byte memory and closed, stage-local
equations; it compares full status and every final byte and retains separate
read/write demands. `bind_scalar_memory_machine` and `bind_scalar_memory_bytes`
in `trust_cg_verify::read_only_target` return immutable unresolved inventories,
not certificates or native execution authority. The original read-only API
stays unchanged. See the connected checkpoint
for exact coverage, resource bounds and the independent-replay/caller gates.

`ScalarMemoryCompilerRelations` in `trust_cg_verify::read_only_replay` combines
every original source/LIR and actual Mach/final-word relation in one immutable
inventory. It uses the same sealed original-query discharge protocol as the
read-only inventory and x86 ABI envelope, retaining every not-run row after
the first non-Valid result. Only independently Valid replay of ALL exact parts
under one enforcing proof-promotion request can issue its conditional
certificate; that certificate grants no native or caller authority. The
all-part checkpoint
retains the mandatory original proof failures, not a verified-execution claim.

The opcode evidence inventory pins accepted/deferred classifications for
every inventoried backend. Each backend's accepted count, denominator and
exact named RED list are pinned by one test in `coverage_gate_tests`:
`aarch64_emittable_coverage_is_honest_under_strict`,
`x86_emittable_coverage_is_honest_under_strict`,
`riscv_inventory_pins_accepted_and_deferred_rows` and
`wasm_inventory_pins_accepted_and_deferred_rows`. AArch64's RED rows are all
deferred models (among them the emitted ELF TLSDESC slots and the LL/SC atomic
rows); FCMP, CSET and CSEL/CSINC/CSNEG are credited by per-instruction NZCV
producer/consumer obligations bound to the reaching flag producer, the
half-precision FCVT forms by decoded-word obligations against an independent
IEEE 754 `convertFormat` intent, and the register copies by decoded-word forms
each copy instance must bind. WebAssembly has no RED rows: `memory.copy` and
`memory.fill` are credited by the emitted guarded MemCopy/MemSet body, whose
`if (n != 0)` guard keeps a zero-byte op a no-op as trust-ir defines it; the
constant-size `memory.copy` of aggregate moves is not covered by that credit
and rests on the lane differentials; the never-selected v128 forms are
excluded, and a live-compiled corpus is scanned to show none is emitted.
`f32.const` and `f64.const` are credited by an independent decode of their raw
IEEE-754 payloads, compared bit-exactly with the constant's pattern through a
stated round-to-nearest-even narrowing for `f32`; `min`/`max`, which the
lowering emits only inside its FMin/FMax sequence, by that emitted sequence,
run under the spec semantics against the trust-ir contract with the `-0`/`+0`
tie unpinned. `clz`/`ctz`, `rotl`/`rotr`, `eqz`, `select` and `copysign` are
reconstructed from their real opcode bytes; `eqz` is credited for its
zero-test value semantics, since the lowering emits it only inside the assert,
overflow and wide-integer sequences.
The pinned ratios measure accepted obligation
coverage over emitted value/effect inventories, not compiler correctness or
formal-proof coverage. In particular, a default `Statistical(N)` Valid result is
regression evidence, not a formal proof. The inventory test passes with exactly
that named debt and fails on unknown classification or evidence drift.
The source of these ratios is
[`coverage_gate_tests.rs`](crates/trust-cg-verify/tests/coverage_gate_tests.rs);
`scripts/check_opcode_coverage_gate.sh` evaluates the inventory, and its
published-ratio regression rejects drift between these claims and the gate.

## Capability grid

Coverage is feature- and target-specific. “Implemented” means there is a real
code path and executable test coverage; it does not mean replacement-grade
completeness.

| Surface | Implemented | Important gaps |
| --- | --- | --- |
| AArch64 | Instruction selection, register allocation, JIT, Mach-O and ELF object emission (ELF `static`/`pie`/`pic` relocation models with GOT-indirect preemptible symbols and local-exec, initial-exec or TLSDESC thread-locals; explicit sections and constructor tables; ELF function sections and COMDAT groups), scalar integer/FP and selected NEON paths. | Complete ABI, aggregate, relocation authority (TLSDESC relocations are unproven), TLS modes, unwind/debug, atomics, SIMD, and proof coverage. |
| x86-64 | Instruction selection, register allocation, JIT, ELF/Mach-O/COFF object emission, scalar integer/FP and selected SSE-128 paths. | Full SysV/Win64 ABI parity, aggregates, TLS, unwind/debug, atomics, AVX/vector coverage, all object relocations, and proof coverage. |
| RISC-V 64 | Bounded integer/pointer AOT: instruction selection, allocation with spills, frames, branch relaxation, multi-function ELF and external call relocations. | At most eight GPR parameters and one result; no indirect/variadic calls, FP/vector, Switch or non-entry block parameters. Certified output and JIT are refused. |
| WebAssembly (wasm32) | Module lowering/encoding of the trust-ir value domain (narrow and 128-bit integers, floats, aggregates, enums, fat pointers, atomics, bulk memory), structured CFGs, linear memory, globals and direct/indirect calls. Closed modules, or relocatable objects linked by `wasm-ld`, from the CLI; library host-island imports with explicit shared-memory and stack contracts; the rustc bridge's wasm32 lane. Evidence: interpreter differentials over closed and linked modules, a Rust-level differential against LLVM, CFG-fuzz oracles, and bounded encoding, CFG-structural and memory/call-ABI proof families. | No general WASI/emscripten driver, bundled linker, optimizer beyond a local emission pass (O1 and above; each rewritten function is emitted only when a per-function wasm-to-wasm translation validator accepts it), exception handling, wasm64, proof certificates for emitted objects or complete semantic translation-validation verdict; the structural invariants are necessary conditions, not a proof that a module computes what its trust-ir computes. |
| trust-ir transport | Binary tMBC, text parser/printer, debug JSON, provenance and proof-sidecar footholds. | Complete semantic coverage for every type, constant, instruction, dialect, aggregate, and metadata form. |
| Optimization | O0 pipeline plus O1–O3 passes, target peepholes, vectorization work, PGO plumbing, and opt-in CEGIS superoptimization. | Uniform correctness/performance confidence across all higher-level passes and both primary targets. |
| Rust integration | A separate `rustc_codegen_trust_cg` bridge, pinned to the Trust compiler and driven in its explicit unverified frontend lane, with MIR/mono-item lowering, static/vtable data, ABI marshalling, runtime helpers and a per-shape native differential corpus checked against the LLVM backend at O0–O3, plus a `wasm32-unknown-unknown` lane executed against LLVM on a `no_std` corpus. | Full MIR, layout, ABI, mono-item, runtime, panic/unwind, and ecosystem coverage. It is not a rustc replacement today. |
| Proof artifacts | Per-rule reports, function-level sidecars, solver bridges, proof databases, and selected independently checked canaries. | End-to-end coverage of every transformation and emitted byte, universal independent replay, and a completed formal compiler proof. |
| Heterogeneous compute | Lowering compute-graph analysis and dispatch plans; Metal MSL/launch-descriptor emission; CoreML MIL construction primitives; bounded ONNX protobuf/JSON import to standalone VNN/tensor JSON. | Production CoreML graph emission refuses without an exact tensor recipe. ONNX is not a TrustIR frontend; a supported accelerator runtime and complete tensor semantics remain open. |

The detailed stale-overclaim guards are
[`rustc-mir-coverage-inventory.md`](rustc-mir-coverage-inventory.md) and
[`trust-cg-full-replacement-ledger.md`](trust-cg-full-replacement-ledger.md).
Those inventories are deliberately conservative: support for a listed slice
must not be read as full Rust or full trust-ir replacement readiness.
Research-track code is not automatically a supported product surface, and the
capability grid and [`LIMITATIONS.md`](LIMITATIONS.md) are authoritative over
aspirational descriptions in [`VISION.md`](VISION.md).

## Similar projects

trust-cg shares ideas with several mature systems but has a different center of
gravity:

| Project | Primary focus | Relationship to trust-cg |
| --- | --- | --- |
| [LLVM](https://llvm.org/) | Production general-purpose optimizing compiler infrastructure. | The main compatibility and differential-testing reference; trust-cg is far smaller and less complete, with proof evidence as a design constraint. |
| [Cranelift](https://cranelift.dev/) | Fast, secure code generation and JIT in Rust. | A useful Rust backend reference; trust-cg emphasizes proof-carrying inputs and per-transformation evidence. |
| [CompCert](https://compcert.org/) | A machine-checked optimizing C compiler, proved in Coq. | The standard for end-to-end correctness claims; trust-cg does not meet this proof bar and targets a different IR/multi-language architecture. |
| [Alive2](https://alive2.llvm.org/) | Translation validation for LLVM IR transformations. | A close methodological reference for solver-backed equivalence, applied here inside a native backend pipeline. |

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

Build the StarExec entry point on Linux x86-64, or reproduce that build in a
Linux x86-64 container:

```bash
./starexec_build
./starexec_run_default.sh instance.cnf /tmp/trust-cg-sat/

docker build --platform=linux/amd64 \
  -f docker/sat-comp-2026/Dockerfile -t trust-cg-sat:sat-comp-2026 .
```

The [system description](satcomp_2026_system_description.md) states the solver
and proof boundary. The [benchmark study](benchmarks/benchmark_study.md)
contains methods, raw comparisons, checker results, limitations, and a visible
retraction of an earlier invalid end-to-end speed claim. The
[`metrics-contract.md`](metrics-contract.md) defines the evidence required for
new performance claims. This README intentionally makes no aggregate compiler
performance claim.

The newest committed compiler-performance row is from 2026-09-29, the second on
`aarch64-apple-darwin` (Apple M4 Max), at `80b0e03aa`. As in the first
(2026-09-28), the certificates-on bridge compiles 0 of the 18 benchmark
programs, all refused with `[TCG-PROOF-465]`, so it records no runtime,
compile, size or memory ratio
([re-measure](reports/perf/2026-09-29-darwin-aarch64-remeasure/README.md),
[campaign](reports/perf/2026-09-28-darwin-aarch64-campaign/README.md)). The
newest row with such ratios is from 2026-08-30, on Linux AArch64. Every row is
scoped to its recorded revision and host, not a measurement of today's
checkout. See `ratchet/ledger.jsonl` for each row's exact measurement
identity.
Updating documentation or rendering a ledger never substitutes for rerunning
the benchmark harness.

## Roadmap

1. **Expand the supported envelope.** Close trust-ir semantic, ABI, aggregate,
   object, TLS, unwind, debug, SIMD, and atomic gaps with positive and
   fail-closed negative tests.
2. **Reach AArch64/x86-64 parity.** Hold both primary targets to the same
   semantic and evidence contract, allowing only documented ABI differences.
3. **Strengthen the proof chain.** Replace statistical credits with solver or
   checker-backed evidence, bind certificates to exact emitted artifacts, and
   reduce the trusted base.
4. **Stabilize integration surfaces.** Mature the CLI/file formats, the `rustc`
   bridge, diagnostics, and embedding APIs before promising compatibility.
5. **Publish reproducible performance evidence.** Preserve inputs, revisions,
   resource envelopes, wrong/invalid counts, and checker verdicts for every
   comparison.

The 1.0 bar is a stable backend for a documented trust-ir surface on AArch64
and x86-64, with reproducible distribution, target parity, and a proof policy
whose claims survive independent checking — not merely a version number.

<details>
<summary><strong>Repository layout</strong></summary>

| Path | Purpose |
| --- | --- |
| `crates/trust-cg-cli` | The `trust-cg` command-line driver. |
| `crates/trust-cg-dialect`, `trust-cg-lower` | Dialect conversion, trust-ir adaptation, ABI lowering, and instruction selection. |
| `crates/trust-cg-ir` | Shared machine IR, registers, provenance, and compilation traces. |
| `crates/trust-cg-process-env` | Shared process-environment access and coordinated test mutation. |
| `crates/trust-cg-opt` | Optimization passes, rewrite infrastructure, PGO, and vectorization. |
| `crates/trust-cg-regalloc` | Liveness, register allocation, spills, coalescing, and validation. |
| `crates/trust-cg-codegen` | Target encoders (AArch64, x86-64, RISC-V, wasm), object writers, JIT, debug/unwind, and compiler orchestration. |
| `crates/trust-cg-verify` | Proof obligations, evaluators, solver bridge, certificates, proof database, and CEGIS. |
| `crates/rustc-codegen-trust-cg` | Separate Trust-pinned (`channel = "trust"`) rustc codegen-backend bridge. |
| `crates/trust-cg-llvm-import`, `trust-cg-onnx-import`, `trust-cg-lift` | LLVM-IR text and ONNX importers, and binary lifting. |
| `crates/trust-cg-jit-matrix` | JIT workload builders, specialization experiments, and benchmark drivers. |
| `crates/trust-types-compat` | The local `trust-types` compatibility package. |
| `crates/trust-cg-sat-host`, `trust-cg-drat-trim` | Vendored MicroSAT bindings and the drat-trim checker. |
| `crates/trust-cg-test`, `trust-cg-fuzz` | Unified validation commands and differential fuzzing. |
| `formal/lean`, `proofs` | Formal models, selected proofs, and proof fixtures. |
| `benchmarks`, `reports/perf` | Reproducible benchmark definitions and preserved results. |
| `scripts` | Test, proof, soundness, fuzz, and release-support commands. |

</details>

## Developing

Start with the narrowest test that covers a change, then broaden it:

```bash
targo --unverified check --locked --workspace --all-targets --all-features
targo --unverified test --locked -p trust-cg-cli
targo --unverified test --locked -p trust-cg-codegen --test e2e_cli_tmbc
targo --unverified test --locked -p trust-cg-verify --features core-byte-replay
scripts/check_fmt.sh
python3 scripts/check_documentation.py --check
```

The feature flags matter: Cargo skips a target whose `required-features` are
off without failing, so plain `-p trust-cg-verify` never builds or runs the
`core_byte_store` and `core_byte_writer` targets (`core-byte-replay`).

The broader local matrix is `scripts/run_full_test_matrix.sh`. It automatically
assigns every otherwise-unlisted integration target to a bounded shard and exits
nonzero for any failed, timed-out, skipped, or incomplete shard. Use
`--report-only` only when collecting a deliberately non-gating historical
measurement. Its v2 report separates raw libtest passes from qualified passes,
captured runtime SKIPs, ignored tests, and unavailable capture; every shard's
combined log is retained. Counts are test invocations, not unique tests or
proof obligations. Do not set `RUST_TEST_NOCAPTURE`: captured `--show-output`
is required to attribute successful tests' skip diagnostics. On one host that
census is non-green by construction (Linux-only suites compile empty on macOS,
macOS-guarded suites skip on Linux). `scripts/full_test_matrix_hosts.py`
partitions the same suites into a Darwin and a Linux required set, and
`scripts/run_darwin_full_test_matrix.py` runs the Darwin set with the strict
proof gate (per-host matrix); the Linux set
is classified but not yet executed.

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
