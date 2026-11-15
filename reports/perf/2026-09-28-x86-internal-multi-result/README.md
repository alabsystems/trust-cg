> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
# 2026-09-28 — x86-64 internal multi-result convention past RAX:RDX

Upstream capability #3 of TY's
[upstream workaround inventory](https://github.com/alabsystems/ty/blob/main/reports/perf/2026-09-28-upstream-workaround-inventory/README.md):
TrustIR multi-result functions (`FuncTy.returns` is a `Vec`) were first-class
on AArch64 (X0-X7 / V0-V7) but refused on x86-64 at the third result of a
register class, so every producer with a wider internal convention was
AArch64-only here. This record is the evidence for the change on
`lane/x86-internal-multi-result`, landed on `main` at `ddc1c96f3` with the
follow-up `57b725a81` (a `ret` found anywhere in its block) at `802aee4b4`;
the design is in the commit messages and in
`X86_INTERNAL_RET_GPRS` / `X86_INTERNAL_RET_XMMS`
(`crates/trust-cg-ir/src/x86_64_regs.rs`).

**Host:** Apple M5 Max, 128 GB, macOS, shared with other sessions (load 25-40
throughout). **No x86-64 executor on this host**: Rosetta 2 is not installed
(`arch -x86_64 /bin/zsh` → "Bad CPU type"), so the in-repo native/Rosetta
link-run lane and the x86-64 JIT lane print `SKIP` here. Execution evidence
below comes from the Unicorn x86-64 emulator (QEMU TCG core, `unicorn` 2.1.4
from PyPI in a scratch virtualenv), driven by [`uc_multi_result.py`](uc_multi_result.py).
Toolchain: this repository's pinned stock Rust 1.97.1 (`rust-toolchain.toml`),
as its CLAUDE.md requires; no Trust-verified-compilation claim.

## What changed (summary)

| piece | where |
| --- | --- |
| internal file RAX,RDX,RCX,RSI,RDI,R8,R9 / XMM0-XMM7; C file its same-index prefix; R10/R11, XMM14/XMM15 excluded (post-RA scratch) | `trust-cg-ir` `x86_64_regs.rs` |
| one classifier over the internal file (System V), Windows x64 unchanged; `x86_sysv_returns_exceed_c_return_file`; `lower_return` resolves every source before its first fixed-register write and stamps the `ret` (`internal_return_regs`) | `trust-cg-lower` `x86_64_isel.rs` |
| `[TCG-X86-MULTI-RESULT]`: a signature past the C file is admitted only on a `Fast`/`Cold` edge (definition, direct call, indirect call); `C`, `Rust`, ... refused by name | `trust-cg-lower` `adapter.rs` |
| post-RA liveness reads the internal registers at the `ret`; the allocator sees an internal return's moves as explicit producers with return sinks (window must write every result register, else refused); the regalloc replay consumes those defs | `trust-cg-codegen` `x86_64/pipeline.rs` |
| TV-5 admits the internal registers as System V call results; TV-1's return-register derivation reads the shared tables; TV-5 volatile `movss`/`movsd` stores read only their scalar lane (pre-existing false positive) | `trust-cg-verify` |

## Evidence

### 1. Execution under emulation (non-TY programs)

`tests/e2e_x86_64_internal_multi_result.rs` builds, per shape, a module with a
`Fast` multi-result producer (a volatile read-modify-write keeps it out of the
inliner), a relay that calls it and returns its results (callee AND caller of
the convention), a C wrapper making two chained calls with twelve values live
across both, the same through a `Fast` `CallIndirect`, and an address export.
Shapes: 3, 5 and 7 integers (narrow carriers and `bool` included), 8 FP (both
widths), 15 mixed (both files full, interleaved) and `i128` pairs past the C
file. With `TRUST_CG_X86_MULTI_RESULT_ARTIFACTS=<dir>` the test writes the
Darwin objects and the expected bytes, computed in Rust by the test, never by
TrustCG. `uc_multi_result.py` links them with `cc -arch x86_64` (link only) and
executes the linked image under Unicorn:

```
O0: wrappers 48 exact, callees 24 exact
O1: wrappers 48 exact, callees 24 exact
O2: wrappers 48 exact, callees 24 exact
O3: wrappers 48 exact, callees 24 exact
TOTAL {'wrapper_calls': 192, 'callee_register_checks': 96, 'controls_refuted': 80}
```

192 wrapper calls (6 shapes x 4 seeds x direct/indirect x 4 levels), each two
chained multi-result calls with twelve live values and the callee's counter
side effect, byte-exact; 96 direct entries into the multi-result callee with
its result REGISTERS read in the documented order, exact. Objects:
`unicorn-artifacts.sha256` (built at `d76e8ca4c`;
rebuilt at the landed `main` `802aee4b4` every object is byte-identical and
the run is again 192 / 96 / 80),
layout: `layout.txt`, run: `unicorn-run.txt`.
Reproduce:

```sh
TRUST_CG_X86_MULTI_RESULT_ARTIFACTS=/path/art cargo test -p trust-cg-codegen \
  --test e2e_x86_64_internal_multi_result internal_multi_results_execute_exactly_at_every_level
python3 -m venv v && v/bin/pip install unicorn && v/bin/python uc_multi_result.py /path/art
```

`controls_refuted`: for every shape whose results reach RCX/RDI, the callee's
registers read in a plausible wrong order (the System V argument order) must
mismatch; every one did, so the register check discriminates placement.

**It found a real miscompile before landing** (found-before-landing.txt):
without return sinks, the allocator parked a split copy of result 6 in RAX
after RAX had received result 0 in a seven-result relay. The fix is in the
landing commit; the record reproduces the disassembly.

### 2. Byte identity of everything the backend compiled before

`examples/x86_retarget_census.rs` compiles every module of
`benchmarks/compile-corpus/modules` (1,587 TrustIR modules: 1,438
rustc-bridge codegen units of ordinary Rust programs, 109 TY, 35 fixtures, 5
ay kernels) for `x86_64-apple-darwin` and `x86_64-unknown-linux-gnu` at O0-O3
(12,696 compiles per run), retargeting `target_info`, and prints the object's
SHA-256 or the refusal's first line. Base = `ec6748a56` (this branch's base,
`origin/main`), new = this branch; same host, same flags.

| run | rows | objects byte-identical | refusals identical | changed |
| --- | ---: | ---: | ---: | ---: |
| plain (modules as collected) | 12,696 | 12,228 | 468 | **0** |
| `--externalize` (module-local functions made `External`) | 12,696 | 12,380 | 28 | 288 (all TY: capacity refusal -> object) |

`census/compare-plain.txt`,
`census/compare-externalized.txt`, the four
raw outputs gzipped under [`census/`](census/). Every object any module
compiled to before is byte-identical after (by SHA-256 and length), every
refusal keeps its text, at O0-O3 on both object formats: the 11,504 rustc
bridge compiles of ordinary Rust programs, the fixtures, the ay kernels and
TY's production modules. The only rows that change are the 288 whose base
refusal was the selector's "integer result register capacity is exhausted";
all 288 now compile. In the plain run TY's semantic images stop earlier, at
the object path's local-binding refusal, identically on both sides.

### 3. TY's semantic images reach the x86-64 backend

TY's semantic images in the corpus are its own emitted modules (collected by
`collect_ty.py` from TY replay artifacts) for 36 of the strict-exact rows.
With `--externalize`, on base every one of the 36 image modules is refused at
every level on both formats by the x86-64 selector (`unsupported x86-64 scalar
return ABI for result 2 (I64) under SystemV: integer result register capacity
is exhausted`) — the refusal TY's AArch64-only gate
(`tla-ir/src/semantic/native.rs:18-22, :947`) exists for. After: all 696
`ty-semantic` compiles (87 modules x 2 formats x 4 levels) produce objects,
and the other 584 TY rows are byte-identical. The rows: ABCorrectness,
ACP_NB_TLC, ACP_SB_TLC, AsyncTerminationDetection, AsynchInterface, Barrier,
Barriers, CatEvenBoxes, Chameneos, Channel, Consensus, DiningPhilosophers,
HourClock, HourClock2, LiveHourClock, Lock, MCConsensus, MCConsensus_2,
MCInnerFIFO, MCInternalMemory, MCLiveInternalMemory, Peterson, Prisoner,
Simple, SimpleRegular, SpanTree, SyncTerminationDetection, TCommit, TwoPhase,
VoucherLifeCycle, clean, dijkstra-mutex_LSpec-model, kvstore, nbacc_ray97,
nbacg_guer01, stages. This is compile evidence only: TY's runtime helpers
are not linked, so the images are not executed here. TY's side (a `[patch]`
build of TY against this change and its strict semantic census) is TY's
record, `reports/perf/2026-09-28-x86-internal-multi-result-ty/`.

### 4. Tests

Stock 1.97.1 debug builds on this host. "Pre-existing" means the same
tests fail identically on the base `ec6748a56` in this host's environment
(checked by running them there): every one is a proof-environment refusal —
no AY admitted by a stock-toolchain build (`[TCG-AY-IDENTITY-UNRECORDED]`),
no discovered verification authority, or x86 proof promotion refusing
statistically credited opcodes (XD-01) — in code this change does not touch.

| suite | result |
| --- | --- |
| `trust-cg-ir` lib | 534 / 534 (incl. `x86_internal_return_file_extends_the_c_file`) |
| `trust-cg-lower` lib | 1,950 / 1,950 (x86_64_isel 436: placement, extraction, emission, exhaustion, the prefix-extension property over every 0-4-component sequence of seven carriers, source-resolution ordering) |
| `trust-cg-opt` lib | 3,706 / 3,706 |
| `trust-cg-regalloc` lib | 715 / 715 |
| `trust-cg-verify` lib | 4,608 passed, 4 failed — pre-existing (AY not admitted: `gpu_blend_ay`, three wasm anti-tautology proofs) |
| `trust-cg-codegen` lib | 4,440 passed, 3 failed — pre-existing (verification authority / AArch64 proof promotion) |
| `trust-cg-codegen` integration targets named x86, multi_result, swift or must_refuse (74) | 71 pass; `e2e_x86_64_dispatcher` (2), `e2e_x86_64_module_batch_fnptr` (1), `e2e_x86_64_module_batch_globals` (1) fail — pre-existing (x86 proof promotion) |
| `e2e_x86_64_internal_multi_result` | 12 / 12 (link-run and JIT lanes SKIP here) |
| `e2e_x86_64_calling_conv` | 18 / 18 |
| `must_refuse_corpus` (codegen, cli) | 2 / 2, 1 / 1 |
| `scripts/tests/test_linux_x86_64_gate.py` | 16 / 16 (the new floor row, minimum 12) |
| backport onto TY's pin `318f896ed` | e2e 12 / 12, calling_conv 18 / 18, x86_64_isel 433 / 433, TV-5 71 / 71 |

The full battery (`battery-summary.txt`) ran on the
feature commit `5e06c59a0`; the pre-existing failures' reruns on the base are
`base-preexisting-failures.txt`. After
merging `origin/main` (trust-ir pin `c603897b` -> `bf7ee706`) the lib suites
of ir (x86_64_regs), lower, opt, verify (post_ra_dataflow, x86_source), the
codegen lib's 1,000 x86 tests, the multi-result, calling-convention, swiftcc,
indirect-call, fp-across-call, source-bound-body and must-refuse targets and
the CLI must-refuse corpus all pass (`post-merge-tests.txt`).
`scripts/check_fmt.sh` OK; `scripts/check_clippy.sh` OK on its four packages
(tippy 0.1.98); `trust-cg-opt` (outside that gate) has 175 findings on `main`,
none on a line this change wrote.

### 5. The host JIT's allocator (LinearScan), executed — addendum, 2026-09-28 evening

Everything above ran the AOT object path, which allocates with Greedy
(`X86PipelineConfig::default`). The x86-64 host JIT with
`enable_jit_fast_regalloc` (`CompilerConfig::jit_fast`, and the configuration
TY's semantic images use) allocates with LinearScan
(`X86PipelineConfig::host_jit_fast`), falling back to Greedy per function only
when LinearScan fails. The return-sink representation is strategy-independent
by construction — both strategies receive the same `reserved_regs` map from
`physical_liveness::reserve`, and the translation validator runs for both —
but until now LinearScan output of the internal convention had been executed
nowhere: the e2e test's JIT lane runs only on an x86-64 host.

Same-binary A/B at `main` `472b86e01`: a scratch, never-landed switch
([`linearscan/scratch-aot-linearscan.patch`](linearscan/scratch-aot-linearscan.patch),
`TCG_SCRATCH_X86_AOT_LINEARSCAN`) gives the AOT object pipeline the JIT's
`Full(LinearScan)` allocator. One `e2e_x86_64_internal_multi_result` test
binary (stock 1.97.1, this repository's pin), run twice:

| arm | e2e tests | objects vs the other arm | Unicorn (`uc_multi_result.py`) |
| --- | --- | --- | --- |
| switch unset (Greedy) | 12 / 12 | — ; all 26 artifacts byte-identical to `unicorn-artifacts.sha256` | 192 wrapper calls, 96 callee register reads exact; 80 controls refuted |
| switch set (LinearScan) | 12 / 12 | all 24 objects differ (expected bytes and layout identical) | 192 wrapper calls, 96 callee register reads exact; 80 controls refuted |

`linearscan/artifacts.sha256`,
`linearscan/unicorn-run.txt`. So the internal
convention executes exactly under both x86-64 allocator strategies at O0-O3
for the 3/5/7-integer, 8-FP, 15-mixed and i128 shapes, direct and indirect.
This is still emulation, still the AOT object path (with the JIT's allocator),
and still chosen inputs; the in-process x86-64 JIT itself (its raw-bytes
emission and `Internal` exact module calls) runs only on an x86-64 host.

## Where this departs from the inventory's design sketch, and why

* **Seven integer registers, not nine.** The sketch listed R10 and R11; this
  backend never allocates them because post-RA spill materialization,
  parallel-copy cycle breaking and the counter trampoline use them as scratch.
  A result parked there could be overwritten between the return moves and
  `ret`. The 3-, 5- and 9-result test plan became 3, 5 and 7 (the whole file)
  plus an 8-result refusal; FP keeps all eight argument XMMs.
* **Admission is by calling convention, not linkage.** The sketch refused an
  exported function. Linkage does not change a function's convention, AArch64
  places multi-results for any linkage, and this backend's x86-64 object path
  cannot yet reference an `Internal` function at all — an internal-only rule
  would have made the convention JIT-only. What a C caller cannot read is
  refused where it can occur: every `C`/`Rust`/other-ABI edge past the C file.
* **The register allocator needed a representation change**, not only the
  classifier: without return sinks the seven-result relay miscompiled
  (found-before-landing.txt). C-shaped returns
  keep the old representation, which is why their bytes do not move.
* **No TrustIR must-refuse row.** Multi-value return placement is the
  consumer's rule, and AArch64 accepts a C-convention multi-result, so the
  refusal is an x86-64 consumer rule; its named refusals are tested here
  (`a_foreign_convention_definition_is_refused_by_name`,
  `a_direct_call_is_decided_by_the_callee_convention`,
  `a_c_convention_indirect_call_is_refused_by_name`).

## What this does not establish

* No native x86-64 or Rosetta execution on this host, and no Linux x86-64
  run: the emulator is the only executor here. Unicorn implements the
  integer, SSE and SSE2 instructions these programs use; it is not the
  silicon.
* Execution on chosen inputs is not a proof of the convention.
* The x86-64 object path still cannot reference an `Internal` function
  (`AotDirectModuleFunctionBindingUnsupported`, a separate limitation), so an
  AOT object uses the convention only between non-internal functions; TY's
  JIT shape (`Internal` + `Fast`) is exercised here by the in-repo JIT lane on
  x86-64 hosts only, and on this host only through `--externalize`.
* Windows x64 defines no extension; it still refuses a second result.
* No TrustIR change: multi-value return placement is the consumer's rule
  (`StructPassingPolicy` docs, `SPEC_RATIFICATIONS.md`), and AArch64 places a
  C-convention multi-result in X0-X7, so "refuse a C-convention function with
  more than two results" is an x86-64 consumer rule, not a target-independent
  must-refuse row. The named refusals live in this repository's tests.
