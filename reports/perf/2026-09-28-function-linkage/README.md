# Linux AArch64 function linkage — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The trust-cg core library and expanded trust-cg consumer now link and execute
81,097 UTF-8 checks. The previous duplicate `str::as_bytes` definition came
from ignoring rustc's `Internal` function linkage. The LLVM consumer of the
same CG-built core also passes all 81,097 checks. These are diagnostic builds
with LLVM-built compiler-builtins; they do not qualify a complete CG sysroot.

## Change

On Linux AArch64, the bridge records rustc's function linkage and visibility
before lowering any codegen unit. Internal functions receive distinct
`__trust_cg_private.<cgu>.<item>` names with strong hidden ELF binding. This
preserves each CGU's private identity while allowing the bridge to emit a CGU
as several objects. Setting each single-function IR definition to `Internal`
would prevent its sibling objects from resolving calls. Making those copies
weak would permit the linker to conflate distinct private definitions.

The emission pass updates definitions, declarations and nested `SymbolAddr`
constants, including callback statics and vtables. Function IDs, signatures,
instructions and relocation addends retain their meaning. The reachability
graph keeps canonical rustc symbols, and now retains every planned local copy
of a reachable helper. Entry wrappers, existing stub paths, merged CGUs and
per-function fallback all use the same emission plan. Namespace collisions,
private EH personality renaming and opaque proof/contract carriers fail
closed. Linkage refusals cannot enter historical MIR skip/stub routes.

The optimized multi-CGU callback test also exposed an existing upstream-static
bug: copying an exported foreign static's initializer exposed a reference to
that crate's private function. Readers and nested static references now import
the static's canonical storage when rustc's export metadata establishes that
it is reachable. This preserves both the function pointer and the static's
address. The gate does not infer exportability from a source-level `pub` flag.

This changes function linkage on Linux AArch64 only. It does not claim target
qualification for other architectures or object formats.

## Evidence

| Check | Result |
| --- | --- |
| Structural namespace, linkage, identity and refusal tests | 8 passed |
| Independent base/left/right libraries | O0/O2, 1/8 CGUs, LLVM/CG batch/CG legacy |
| Library executions | 12 × 360,449 checks |
| Executable reachability with two copies of one helper | 3 × 8,192 checks |
| Combined new native checks | 4,349,964 |
| Reserved namespace controls | 2 LLVM accepts, 2 CG refusals |
| Ordinary Rust main smoke tests | Baseline/current × 1/8 CGUs all run successfully |
| CG core archive | 44 ELF64 little-endian AArch64 objects |
| Private core definitions | 1,281 strong hidden functions; canonical `as_bytes` absent |
| LLVM and CG consumers of CG core | 81,097 checks each |
| Compiler-builtins / alloc diagnostic census | 14 / 148 roots, identical to baseline |
| Selected native/refusal controls | 8 pass; mandatory machine-proof admission fails |

The native fixtures exercise direct calls, reified callbacks, vtables,
upstream statics, cross-crate static address equality, multi-CGU local copies,
and both batched and per-function emission. ELF inspections require generated
private definitions to be `STT_FUNC`, `STB_GLOBAL`, `STV_HIDDEN`. The tests
retain rustc's mono-item census and verify that the intended private copies
were actually collected. Batch traces also retain the single-function
fallback cases.

The mandatory proof failure remains `[TCG-PROOF-465]`: 14 uncovered
instructions across 12 opcode kinds, first `aliased_f32_read[13]`,
`AArch64::StpPreIndex`. Native diagnostic results do not waive this failure.
Selected controls include constant reachability and no-op drops, suffix
searching, wide checked returns, residual control flow, and real destructor
behavior including unwind.

## Reproduction and identities

The compiler is the pinned Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`
AArch64 Linux package, using its matching rustc-private sysroot and LLVM SDK.
The source receipt records the complete working-tree inputs above base revision
`e0ac540a363e36c0f28bea7a4831aca10345c313`. The tested backend and test binaries
are copied and hashed; builds do not select a library merely by modification
time. Exact commands, source fixtures, compiler-source extracts, ELF symbol
tables, raw failures and native outputs are retained in the evidence archive.

Use the archived `records/build.py` to build the bridge with the recorded
compiler environment. `records/runtime-qualified.py function_linkage` runs
the native and refusal fixtures; `records/model-qualified.py` runs the
structural tests. `records/core-final.py`, `records/builtins-llvm.py` and
`records/consumer-final.py` rebuild and exercise the core consumer chain.
Rebuildable libraries and large compiler/test artifacts have hash identities;
primary native fixtures, emitted objects and executables are archived.

results.json records the measured results.
assets.json inventories every archive member, and
archive.json identifies evidence.tar.gz.
All archive members are independently rehashed after writing.

No Linux closure row, sysroot/self-host status or performance claim is promoted.
Strict compile-time and execution-time wins over LLVM and Clang remain unproved.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
