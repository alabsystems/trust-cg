# Linux AArch64 initialized constant images

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Initialized indirect scalar constants and aggregates with pointer relocations
now lower through their exact byte images. A separate observed f32 signaling-NaN
miscompile is fixed in the direct constant-operand path. Optimized core improves
from **22 to 12 failing functions** at both O2 and O3, with no added or changed
failures. **Full Linux completion and strict compile/runtime wins over LLVM and
Clang remain open.**

## Change and boundaries

CTFE can represent an initialized `MaybeUninit<T>` as `ConstValue::Indirect`,
even when its ABI carrier is a scalar. The old path only handled wholly
uninitialized indirect scalars. The new path requires exact Rust/carrier type and
size agreement, an allocation range within bounds, and every value byte to be
initialized. Integers and valid boolean images use target-endian scalar constants.
Float and pointer images use loads from the existing allocation emitter, preserving
NaN payload bits and resolved relocations. A selected value can begin at a nonzero
allocation offset; unrelated relocations outside its bytes do not prevent a plain
integer read. An overlapping address relocation requires a pointer carrier and
one complete pointer slot. Reference carriers still refuse images without an
address relocation. TypeId markers retain their existing hash-bit interpretation.

Whole aggregate constants containing address relocations now copy bytes from the
emitted global after those relocations are resolved. Copying raw CTFE bytes would
copy relocation addends rather than pointer values. Source and destination range
arithmetic is checked, constant and destination types agree, and a selected image
cannot cut through a pointer relocation. Existing aggregate-layout admission
remains in force. Padding uses the allocation emitter's existing representation;
this change makes no new claim about the contents of uninitialized padding.

The stronger O0 fixture exposed another bug: converting a direct f32 constant
through the host f64 representation quieted its signaling NaN. Direct f32 NaN
operands now use an I32 constant and a bitcast, without a floating conversion.
Other finite and infinite direct float constants retain their existing lowering.
Partially initialized scalar images, noncanonical boolean images, and reference
images without relocations remain unsupported. The six permanent refusal probes
are valid `MaybeUninit`/union programs that LLVM accepts; they exercise those
backend boundaries without interpreting invalid bytes as Rust scalar values.

## Validation

The permanent C oracle passes **394,208 checks in 16 native executions** across
CG and LLVM, O0–O3, and abort/unwind codegen policies. It verifies signed and
unsigned 128-bit constants, booleans, characters, pointer/reference identity,
nonzero offsets, nested aggregate copies, callable relocated function pointers,
partial-union active bytes and surrounding canaries. Float cases include positive
and negative signaling NaNs, minimal and maximal signaling payloads, quiet NaNs,
negative zero, infinity, and direct f32/f64 returns. Tests inspect representations
without floating arithmetic. Six expected CG refusals produce no object and are
checked against successful LLVM compilations.

The C executables link the selected compiler's real Rust runtime through the
existing harness, with a separate SIGABRT control. The fixture does not itself
throw or catch panics, so its two codegen policies are not an unwinding proof.
Twenty broader regressions pass **19,700,308 checks**, 104 explicit abort cases
and eight existing refusals. They include the prior pointer, borrowed-storage,
scalar-cell, ownership, enum, panic, unwind, linkage and Linux relocation tests,
plus live-pointer, owning-pointer-image and TypeId controls. All-targets build,
formatting, documentation, diagnostics and diff checks pass.

Core builds at O0/O1. O2/O3 remove ten numeric-formatting refusals, including
integer formatters and decimal float-formatting routines, leaving **12 failures**.
The full CG graph attempts 19 crates: eight pass, eleven fail, with
**103 failing functions** and no compiler crashes. Isolated O0 std,
against frozen LLVM dependencies, retains the same **314 failing functions** and diagnostics. All final censuses finish
without a timeout.

Two coherent mixed graphs rebuild core with CG at O0/O1 and the other std crates
with LLVM. Actual std-dylib consumers pass **324,388 UTF-8 checks**, **224 caught
panics and 224 destructor executions**. Loader traces identify those rebuilt
libraries; exported-symbol checks trace the exercised functions to CG core
objects. Full CG-built std remains unfinished.

Strict bridge probes pass at O0/O2 for **45/34 functions**, with
**11/9 scalar obligations** and **21/20 memory refinements**, zero unmodeled shapes
and zero skipped obligations. Mandatory machine proof still refuses with
`TCG-PROOF-465`. These probes do not establish complete semantic proof for the
new constant-image paths. Development compilation disables Trust frontend
verification; concurrent build durations are not performance measurements.

## Evidence and continuation

Records retain the initial unsupported-constant probes, the observed NaN mismatch,
and the earlier standalone link failures. The third-backend qualification was
superseded when the direct NaN bug was found; its interrupted processes and
completed results are explicitly recorded. Only the fourth backend and the final
immutable test executable qualify this report. A second development build had a
source edit during its build and is not asserted as an exact-source artifact.

`build-fourth.py` and `test-build-final.py` create those frozen artifacts.
`master-final.py`, `qualify-fourth.py`, `post-graphs-fourth.py`,
`dynamic-consumers.py`, `check-dynamic-fourth.py` and `compare-fourth.py` retain
commands, result codes, diagnostics and independent comparisons. The archive
contains current and baseline source snapshots, MIR, native objects/executables,
shared libraries, loader traces and identities. All 299 current source files,
the prior 295-file snapshot, frozen 3,044 std sources, compiler and registry inputs
are rehashed. Large backend, test and library archives are identified with their
reproduction commands instead of duplicated in the archive. This is development
evidence, not the consolidated anonymous-clone acceptance report required by the
completion plan.

The remaining optimized-core failures include scalar/array transmute handling,
raw-borrow and aggregate-reference forms, enum binding and loop-state handling.
Read-only `next-pointer-image` probes reproduce the same memory-array transmute
refusal as `TypeId::as_u128` at O2. The C oracle passes 74,752 checks each for LLVM
O0/O2 and CG O0, covering observed pointer bytes, null/one-past values and canaries.
The initial C runner's macro collision is retained separately from those passing
runs. Related `next-transmute` scalar/array probes reach the declared-tuple-layout
refusal at O2, a separate boundary. No follow-up repair is included here.

Backend SHA-256:
`4721ec1117e9b0ecb9082c44511a884c6a19e9e7e94353d705d5293e9e319043`.

Native test executable SHA-256:
`0954cf6b2850a0383097f1527c549342f1bfa2416372e6d6a25d3c04886658c8`.

The evidence archive contains 27,112 files and is 306,380,694 compressed bytes.
Every member was independently rehashed against `assets.json`.
Archive SHA-256:
`e0ab2e045cda6c6239ddb77879860f87158e75155ceaf7f72f2420ac0b9cf22f`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
