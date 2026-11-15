# Linux AArch64 memory unary operations and indirect arguments — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Compiler-builtins now has eight diagnostic failing roots, down from ten. The
bridge supports complement and negation of projected integer fields stored
in aggregate memory. The regression also exposed and repaired an existing
Rust argument ABI bug for small aggregates passed indirectly by rustc.

## Changes

Field updates reuse `lower_unary_op` and `lower_memory_place_store`, retaining
both scalar arithmetic and field-memory refinement obligations. The destination
uses rustc's field offset and width. This removes libm's `i256::not` and
`u256::not` blockers, whose implementations complement two 128-bit limbs.

On Linux AArch64, `small_indirect_param_plan` consults rustc's actual `FnAbi`
for an admitted nonzero aggregate of at most 16 bytes. When rustc selects
`Indirect { on_stack: false }`, the bridge passes one pointer. The old
whole-slot carrier used the C ABI's register classification instead, treating
that pointer as the aggregate's first bytes. A separate baseline probe confirms
the wrong result without unary operations; rustc's ABI dump explicitly states
the 16-byte, 8-byte-aligned indirect argument.

The declaration, entry block, direct and function-pointer caller, and virtual
method signature use the same decision. Callers materialize a separate copy;
callees copy incoming bytes to local storage. This prevents the callee's
by-value mutations from modifying the caller's source. Size, alignment,
pointee attributes and missing metadata are checked against rustc. Larger
arguments retain the existing indirect carrier. This repair does not qualify
closure bodies with separately constructed argument lists or other targets.

## Native evidence

| Check | Result |
| --- | --- |
| Integer arithmetic and ABI matrix | O0–O3 × LLVM/CG; 144,818,176 checks |
| Checked negation, valid values | O0–O3 × LLVM/CG; 800 checks |
| Signed minimum negation, either field, every width | 80 expected SIGABRT exits |
| Isolated small indirect argument | Baseline wrong result; candidate passes 1,024 checks |
| Compiler-builtins census | 10 → 8 roots; only the two unary roots removed |
| Alloc census | Same 148 roots |
| Rebuilt core | 44 ELF64 AArch64 objects; 1,281 private hidden functions |
| LLVM and CG consumers of rebuilt core | 81,097 checks each |
| Existing linkage, conversion and wide-pair controls | 4 tests pass |
| Mandatory machine-proof control | Existing `TCG-PROOF-465` failure remains |
| All-targets compile and documentation checks | Pass |

The main matrix covers signed and unsigned complement at 8/16/32/64/128 bits,
signed wrapping negation at every width, direct scalar controls, aggregate
returns, nested padded fields, borrowed storage modified by LLVM callbacks,
and writes through references. Small aggregate arguments cross both backend
directions through direct calls, function pointers and trait methods, including
arguments after all eight integer registers are occupied. Inputs include an
exhaustive 16-bit sweep, neighbors of every 128-bit power of two and deterministic
full-width random values. The original by-value data is read again after calls
to detect accidental aliasing of caller and callee storage.

The checked matrix enables overflow checks. It tests valid values and each
signed minimum separately in both fields. A returned minimum-negation call
exits with code 77, so an ordinary return cannot satisfy the required SIGABRT.
LLVM prints its overflow panic; CG's existing abort lowering terminates without
that message. The test checks the termination behavior in both cases.

Existing controls pass 4,349,964 linkage checks, 18,349,448 integer-to-float
checks and 233,472 wide scalar-pair argument checks. These counts are separate
from the 144,820,000 new successful value checks above.

## Proof and completion boundaries

The isolated scalar probe proves `Not:I128`, `Not:U128` and `Neg:I128`, with
no skipped scalar obligations. First-field loads/stores also refine. The
second 128-bit field's memory load remains `INCONCLUSIVE` with
`incomplete self-check-rejected`; compilation fails closed. Machine-proof
admission separately rejects the complement and negation probes. The ordinary
mandatory control still reports 14 uncovered instructions across 12 opcode
kinds, first `aliased_f32_read[13]`, `AArch64::StpPreIndex`.

The eight remaining compiler-builtins roots are six AArch64 inline-assembly
functions, cbrt enum binding and a `PolymorphicIter`/`ManuallyDrop` pointee.
The census uses transitional LLVM-built core metadata. Core consumers use
LLVM-built compiler-builtins rebuilt against the new core metadata. No
complete CG-only sysroot, self-host or performance result is claimed.

## Reproduction and retained evidence

The compiler is pinned Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with
matching rustc-private inputs and LLVM SDK. The backend and test executables
are copied only after completed builds and checked by SHA256. The source
receipt extends the [previous conversion report](../2026-09-28-wide-int-float/README.md)
over base revision `e0ac540a363e36c0f28bea7a4831aca10345c313`.

The archive retains exact commands, sources, object files, native executables,
ABI dumps and raw failures. These include the first callback corruption,
the initial test's unnecessary panic-message expectation, the ABI probe's
missing library flag, and the rejected attempt to reuse compiler-builtins
metadata from the prior core. The final core consumers use freshly rebuilt
matching dependencies. No failed attempt is counted as passing evidence.

Use `records/build.py` with the recorded environment;
`records/runtime-final.py memory_unary` runs both new regressions.
`records/abi-probe.py` reproduces the baseline/current ABI comparison.
`records/refine-probe.py` records the scalar and machine-proof boundaries.
The `core-final.py`, `builtins-llvm.py` and `consumer-final.py` scripts rebuild
and exercise the core chain. Large rebuildable libraries, backend and test
executables have recorded identities rather than embedded copies.

results.json records results; assets.json
inventories evidence.tar.gz, identified by
archive.json. Every archived member is independently rehashed.
All Linux completion rows and the requested LLVM/Clang speed wins remain open.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
