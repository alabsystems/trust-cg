# Linux AArch64 wide owning-pointer images — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Wide owning-pointer transport now preserves both data and length metadata
through Rust arguments, returns, callbacks, nested construction and field
storage. The native LLVM/CG matrix passes 1,505,928 checks. Alloc falls from
142 to 63 failing roots; core and matching compiler-builtins still compile and
link in independent consumers. This is diagnostic codegen, with machine
certificates and Trust verification disabled. Complete alloc/std, proof,
self-hosting and strict performance qualification remain open.

## Change

The existing transparent-wrapper classifier now also admits a Linux AArch64
struct whose concrete rustc layout has exactly one non-ZST field, at offset
zero, with the same 16-byte, 8-aligned ScalarPair image. The bounded wrapper
chain must end in a pointer with length metadata. It does not recognize
owners by name or reinterpret Rc/Arc allocation headers as slice elements.
Trait-object vtables retain their separate representation. Existing FnAbi
checks and single-scalar truncation guards remain active.

Rust pointer pairs now use two independent parameter values on Linux AArch64,
including when only x7 remains. LLVM puts the data pointer in x7 and metadata
at sp+0; declaring one two-word aggregate instead put both words on the stack
and shifted later arguments. The declaration, callee entry and direct/indirect
call builders share the same checked plan. C aggregate conventions are separate.

A checked wrapper constructor stores its unique payload's complete pair.
Field stores recover both lanes from actual storage; projected copies and
construction from a memory-backed payload give the destination a full slot.
The bare-pointer predicates for element addressing remain narrow. Other targets
retain their existing nontransparent-wrapper boundary refusals.

## Evidence

| Check | Result |
| --- | --- |
| Final native matrix, O0–O3 × LLVM/CG | 8 executions, 1,505,928 checks |
| Eleven owning-pointer identity probes | Prior backend refuses; new backend compiles |
| Existing dyn-tail, slice-tail, layout and wide argument controls | 1,596,272 checks |
| Mandatory ABI proof control | Expected TCG-PROOF-465 refusal |
| Alloc census | 142 → 63 failing roots |
| Fresh CG core + matching CG compiler-builtins | Both compile |
| LLVM/CG consumers linking both CG libraries | 81,097 UTF-8 checks each |
| All-targets, formatting and documentation checks | Pass |

The eleven owner types are Box of byte/word slices, str and CStr; Rc and Arc
of byte/word slices and str; and CString. The independent LLVM driver checks
lengths 0–257, pointer identity, contents, live values across callbacks,
reference counts, weak-reference release, loops, stack arguments and calls
in both directions. Nested user wrappers are stored inside a larger aggregate,
inspected and mutated through an LLVM callback, then projected back out.
Borrowed slices independently test the split argument convention. Each final
execution performs 188,241 checks.

Allocation, reference-count operations and final destruction in this fixture
are LLVM-compiled. The result qualifies CG's pointer-image transport and the
listed memory operations, not complete CG allocation/drop or concurrency.

The final alloc census has 62 failing functions and one static. Compared by
root identity, 84 previous failures disappear, five NonNull roots are newly
reported, and 14 remaining failures have changed diagnostics. All names and
reasons are retained. Counts alone are not completion evidence.

The first native matrix crashed because the stack callback address was shifted
by one word; GDB and LLVM/CG disassembly show the x7/stack discrepancy. After
that repair, 975,480 checks passed, then an expanded reverse-direction matrix
passed 1,233,480. The broader classifier initially caused four core constructor
failures. Pair construction fixed those; the nested-wrapper test then caught
missing slot propagation from memory-backed payloads. The final constructor,
field-copy and slot rules pass the expanded matrix and the fresh core rebuild.
Failed and superseded runs remain in the evidence archive.

## Proof scope

Isolated identity and callback probes generate zero scalar refinement
obligations. The split-argument probe discharges one scalar XOR-selection
obligation. Strict bridge coverage accepts these probes, but that arithmetic
obligation does not prove pointer transport, memory wiring or ABI placement.
Mandatory machine certificates reject all three probes. The existing ABI
control still fails at 14 instructions / 12 opcode kinds, first
`aliased_f32_read[13] = StpPreIndex`. No Linux completion row is promoted.

## Reproduction and identity

Frozen Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, LLVM 22.1.2,
native Linux AArch64. Validated backend SHA-256:
`33112eb06fecaca9db608945430ba87c14c434accbe0d5193031e64032aa6b85`.
Validated harness SHA-256:
`93e5f5fa1ad7844b3415508d74c358016c9820de2b2a9d6abcf6ca357393ac87`.

The validated immutable artifacts are byte-identical copies of the constructor
backend and carrier harness used for the final native matrix. Qualification
scripts use the validated paths. Earlier files named `final` predate the core
constructor repair and are explicitly superseded by the validated artifacts.
Run the archived `records/build.py` and `records/runtime-validated.py` with
filter `no_proof_wide_owner_matches_llvm`; library census and consumer scripts
record their complete commands and pinned dependencies.

results.json records outcomes; archive.json
and assets.json bind the self-contained
evidence archive, including scripts, logs, source snapshots,
frozen library inputs, native objects/executables and all intermediate failures.
Large backend, harness and rlib artifacts remain local, bound by hash and path.
Compiler binaries are external, hash-pinned prerequisites. These checks do not
establish a compile-time or runtime performance advantage.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
