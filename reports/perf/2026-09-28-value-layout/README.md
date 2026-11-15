# Linux AArch64 value-layout intrinsics — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Sized and bare slice/string `size_of_val` and `align_of_val` calls now lower
through the Rust bridge. The frozen alloc diagnostic build falls from 148 to
142 failing roots, with exactly six removed and no new failures. The native
LLVM/CG matrix passes 174,432 checks. This is diagnostic compilation with
machine certificates and Trust verification disabled; complete alloc/std,
proof, self-hosting and strict performance qualification remain open.

## Change

Sized queries use rustc's monomorphized layout. Bare slice size is its current
length metadata times the element stride, including padding; alignment is the
element alignment. Strings use a byte stride. Zero-sized elements return zero
without multiplying or truncating their length, including lengths above
`isize::MAX`. No data is dereferenced. Valid nonzero-stride inputs must have a
dynamic size fitting `isize`, matching the intrinsic contract.

Projected fat-pointer operands load metadata from their actual field address;
whole operands reuse the existing runtime/constant metadata handling. Return
values use the existing scalar destination and successor path. Trait objects
and struct tails retain their existing dedicated lowering. No machine opcode
or ABI guard changes.

## Evidence

| Check | Result |
| --- | --- |
| New matrix, O0–O3 × LLVM/CG | 8 executions, 174,432 checks |
| Prior backend with the same harness | Unsupported intrinsic refusal |
| Existing trait-object tail control | 272,448 checks |
| Existing slice-tail control | 915,920 checks |
| Frozen alloc census | 148 → 142 failing roots; six removed, none added |
| Frozen compiler-builtins census | Zero failures; complete rlib |
| Fresh CG core + matching CG compiler-builtins | Both compile |
| LLVM/CG consumers linking those two libraries | 81,097 UTF-8 checks each |
| All-targets, formatting and documentation checks | Pass |
| Mandatory proof control | Still refuses with TCG-PROOF-465 |

The matrix calls independent LLVM-compiled Rust drivers through Rust ABI
boundaries. It checks shared, mutable and raw pointers; packed stride 5 and
padded stride 24; u128 and alignment 64; multibyte strings; selected and
projected metadata; raw pointer construction; and loop-carried queries.
Zero-sized slices include lengths up to `usize::MAX` without allocating or
reading memory for those elements. Each execution checks 21,804 results.

The six removed alloc roots are size/alignment queries for `[u8]`, including
raw forms, and raw queries for sized `core::io::error::Custom`. Alloc still
fails at 141 functions and one static. The core archive has 44 ELF64 AArch64
objects and 1,281 hidden private function definitions. Each compiler-builtins
archive has 11 ELF64 AArch64 objects. The consumer fixture exercises its UTF-8
paths, not all library operations.

The first bridge build rejected an edition-2024 let-chain in the edition-2021
bridge; the corrected match guard built successfully. A separate attempted
opaque extern-type probe is retained: both LLVM and CG reject it at Rust type
checking (`Opaque: MetaSized` is unsatisfied). It never reaches either backend
and is not counted as a backend refusal test.

## Proof scope

Four isolated exported layout probes and their four core wrappers generate
zero scalar refinement obligations. Both ordinary refinement and tracked
`bridge-coverage-strict=1` compile, with call/return shapes labeled trusted by
the existing coverage manifest. Neither result proves the new intrinsic
lowering. Mandatory machine certificates reject all eight functions, including
missing operand-exact constant evidence and uncovered frame/call instructions.
The existing ABI proof control still refuses at 14 instructions / 12 opcode
kinds, first `aliased_f32_read[13] = StpPreIndex`. No completion row is promoted.

## Reproduction and identity

Compiler: frozen Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, LLVM 22.1.2,
native Linux AArch64. Backend SHA-256:
`87636075513edccedeee119525f75726b6893a15f73a239a0d8b412157823d5b`.
Harness SHA-256:
`f773b00b10b196f440ec78fe925366ec3ba3a74e7045cdc2158b09ec2bc46d8c`.

The final immutable backend/harness are byte-identical copies of the tested
first artifacts. The native matrix and tail controls were run against those
first paths; their identities are verified rather than rerunning unchanged
bytes. Core, builtins, alloc and proof qualification use the final paths.

Run the archived `records/build.py`, `records/runtime-final.py`, census and
consumer scripts with the recorded frozen toolchain and source. The focused
native test filter is `no_proof_value_layout_matches_llvm` in the
`aarch64_c_fnabi_aggregate_linux` integration target. The mandatory control's
nonzero exit is intentional and retained separately from native correctness.

results.json records outcomes; archive.json
and assets.json bind the self-contained
evidence archive, containing scripts, logs, source receipts,
source snapshots, frozen library inputs and native objects/executables.
Large backend, test-harness and rlib binaries are retained locally by path and
hash in the archived artifact inventory. Compiler binaries remain external,
hash-pinned prerequisites. No performance conclusion follows from these runs.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
