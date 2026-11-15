# Linux AArch64 scalar FP assembly and compiler-builtins — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The frozen compiler-builtins diagnostic build now completes, removing its six
remaining failing roots. Fresh CG-built core and CG-built compiler-builtins
also link together: independently compiled LLVM and CG consumers each pass
81,097 UTF-8 checks. This is diagnostic compilation with mandatory machine
certificates and Trust verification disabled. Alloc, the complete sysroot,
proof, self-hosting and performance qualification remain open.

## Change

The Rust bridge recognizes one scalar `fmadd`, `fsqrt` or `frintn` instruction
on Linux AArch64. Admission requires matching f32/f64 `vreg` operands with
`s`/`d` modifiers, exactly one scalar-local output, `pure, nomem, nostack`,
one successor and no unwind. Separate output and inout forms are supported;
input order and repeated operands are preserved. Extra clobbers, opaque asm,
integer carriers, unknown instructions and multiple instructions still refuse.
The frozen libm uses **FRINTN**, whose rounding mode is fixed to nearest/even;
FRINTI is deliberately rejected.

A typed local TrustIR dialect validates the operation's width and arity.
The adapter checks operand types and the AArch64 target, and emits distinct
LIR operations so portable arithmetic folding cannot change the instruction's
NaN or rounding behavior. FMADD retains the strict fused instruction contract.
FRINTN has a new machine opcode, appended to preserve existing discriminants,
with encoder, register-allocation, scheduling, effects and inventory support.
Its four encoding pins match native GNU `as` output.

Assembly successors, inputs and the single output now participate in the
bridge's existing control-flow, liveness and loop-parameter analyses. The
wider native fixture exposed this missing SSA threading after the six small
compiler-builtins functions already compiled.

## Evidence

| Check | Result |
| --- | --- |
| Scalar FP assembly, O0–O3 × LLVM/CG | 18,874,368 hardware checks |
| Unsupported assembly | Five valid LLVM inputs rejected by CG |
| Prior backend control | Assembly fixture fails compilation |
| Frozen compiler-builtins | Six failing roots → zero; complete rlib emitted |
| Fresh core + matching CG compiler-builtins | Both libraries compile |
| LLVM/CG consumers of those two libraries | 81,097 checks each |
| Six exported compiler-builtins math functions | 2,359,296 hardware checks |
| Alloc | Same 148 failing roots |
| Existing memory and linkage controls | Three tests pass; mandatory proof control still fails |
| Focused type, target, encoder, regalloc and roster tests | Pass |
| Coverage tests | 19 initial passes; corrected ENC-5 check and aggregate ratio pass |
| All-targets, formatting and documentation checks | Pass |

The native oracle is GCC inline assembly on the host, comparing exact result
bits and FPSR flags. It exercises all four rounding modes crossed with FZ/DN
settings, signed zero, subnormals, infinities, signaling and quiet NaNs with
payloads, ties, deterministic random bits, fused cancellation, repeated
operands, distinct outputs and loops. The exported runtime-function check
links without system libm; the link map, symbol table and disassembly bind
calls to the six definitions in the CG-built archive. The host has GCC;
Clang is not installed. These counts are correctness checks, not timings.

Both compiler-builtins archives contain 11 ELF64 AArch64 relocatables.
The core archive retains 44 ELF64 AArch64 relocatables and 1,281 distinct
hidden private function definitions. This consumer fixture qualifies its
UTF-8 paths, not every core or compiler-builtins operation.

Failed intermediate builds are retained. The first native fixture needed a
wrapping loop counter to link independently of core panic helpers. The next
run exposed missing assembly successor/output SSA tracking. A differential
formatting script later dropped older test-module registrations; those were
restored from the sealed baseline, module reordering was disabled, and the
complete intended harness was rebuilt and rerun. Its partial run remains in
the archive and does not replace the final controls.

## Proof scope

The three isolated FP probes emit **zero** scalar refinement obligations;
a successful `refine` diagnostic compile provides no proof of the assembly.
Tracked `bridge-coverage-strict=1` refuses all three as unmodeled `InlineAsm`.
An earlier attempt using the retired environment variable was rejected as an
untracked control and is retained separately.

Mandatory machine certificates also refuse all three probes, each with six
uncovered instructions of six opcode kinds, starting at `StpPreIndex`.
The coverage suite initially caught an unchanged ENC-5 count pin: FRINTN adds
one more emitted opcode without a decoder. The pin and `LIMITATIONS.md` were
updated from 167/287 to 168/288, preserving the larger disclosed gap.
The new FRINTN row is explicitly deferred pending faithful decoded-word,
NaN, FPCR and FPSR obligations. The AArch64 inventory is 174 accepted of 288
emitted opcode rows, with 114 deferred rows; no proof credit was manufactured.
The existing mandatory control remains at 14 uncovered instructions/12 kinds,
first `aliased_f32_read[13] = StpPreIndex`. No Linux completion row is promoted.

## Reproduction

Compiler: frozen Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, LLVM
22.1.2, native Linux AArch64. Backend SHA-256:
`3fa9ec7f4a4a9eb1ab38ca2dd79b2e8d63f5e882e9145a4dee318b4f0aea7435`.

Final native harness SHA-256:
`f809192662b47d3530ea8f0e67aa16cdf5bf153a1874d2b38c298a1338ee33a7`.

`results.json` records the final checks and identities. The archive preserves
commands, frozen source inputs, source receipts, native objects/executables,
link maps, proof refusals and failed attempts. Large libraries, backends and
harnesses are recorded by hash. `assets.json` inventories every member;
`archive.json` records the archive identity and independent member rehash;
`inventory.json` records stored and uncompressed identities.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-28-aarch64-fp-asm
```

All fourteen Linux completion rows remain open. Strict compile-time and
executable-runtime wins over LLVM and Clang remain unproved.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
