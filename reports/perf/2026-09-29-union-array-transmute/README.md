# Linux AArch64 aggregate-union transmute storage

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Aggregate-to-aggregate transmutes now allocate byte storage for both endpoints
when one side is a supported non-scalar union on Linux AArch64. The ordinary
aggregate classifier excludes unions with overlapping fields; the storage
selection now also consults the existing checked union layout. This lets the
existing whole-slot copy lower `MaybeUninit<[T; N]>` conversions and direct
array/union transmutes. The copy still requires equal sizes and uses the weaker
of the source and destination alignments. Scalar-union ABI and proof gates are
unchanged.

Source commit: `8a9d2bd5d`. Remote x86 jump-table changes are merged at
`8bc05baca`; the combined compiler is rebuilt and separately qualified.

## Native evidence

The original stable `mem::zeroed::<[u64; 4]>()` fixture fails at O2 before the
repair and passes afterward. The expanded baseline fails at O0 for direct
array-to-union conversions and at O2 for the zeroed array. LLVM passes both.

The permanent nine-function fixture passes **589,824 checks in 16 executions**:
LLVM and CG, O0–O3, abort and unwind panic modes. It covers fixed and runtime
array indices, zeroed arrays, `MaybeUninit::assume_init`, both directions of a
custom union transmute, packed union alignment, branch-selected images, nested
arrays, thin pointers and floating-point arrays.

The new fixture and four existing regression groups together pass
**4,527,552 checks in 64 executions**, with **eight expected refusals**. The
controls cover scalar-union storage, joins, constants and aggregate-array
iteration. Invalid boolean/reference/partial union images remain refused. The
merged backend repeats the new fixture's full 589,824-check matrix.

The first exploratory expanded fixture had eight functions and passed 131,072
checks in four executions. Its O2 baseline happened to compile because the
runtime-index accesses already forced array storage. Version 2 adds the fixed
index zeroed-array counterexample. The version 1 sources are retained separately;
their recorded commands name the original paths before that addition.

## Libraries and std census

A fresh mixed library with CG-built core and alloc at O2 and LLVM-built remaining
std crates passes exact-library dynamic consumers: 21,504 network/escape-format
checks, 81,097 UTF-8/character checks with each consumer backend, and 112 caught
panic/destructor checks. Compiler invocations, sysroot hashes and loader logs
identify the executed artifacts. This is correctness qualification, not a
controlled performance comparison.

The paired complete isolated O2 std censuses report **236 and 233 failed roots** before and after this repair. There are 3 removed roots, 0 added roots and 0 changed surviving diagnostic texts. The complete root lists and comparison are retained in this report.

The census uses recorded LLVM dependencies and therefore is not a completely
CG-built std dependency graph. Full CG std, complete machine proof, self-hosting
and strict compile/runtime wins over LLVM and Clang remain unfinished.

## Proof and provenance

Strict bridge coverage passes at O0/O2: 28/14 MIR functions, 44/39 refined scalar
obligations, 25/23 memo hits, zero skips and zero unmodeled shapes. The merged
rebuild repeats those results. Memory, pointer provenance, operand wiring and
control flow remain trusted. Machine-proof-required probes still refuse with
`TCG-PROOF-465`. Native execution uses diagnostic `no-proof-certs`; the Trust
frontend is run with verification off.

Frozen backend SHA256 identities:

- Baseline: `e5cea9df8db3585ac7a5c696571bc9e7ce68391947f8afa390071daca7836b99`
- First repair: `e7c28938cf451256377e7a1b23d91be4f58ddd94222585619199345672b4a3b8`
- Merged repair: `9d81f8d89e51c32e7e2b58a5d93553c5ed9180cc5f8411f8850340c5b31b7cbd`

The first repair is built from `7e1cfe798` plus the recorded production patch;
the merged backend is built from `8bc05baca`. Trust frontend:
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`; TrustIR:
`824174a164de10dba2053e387dfc4b1140960885`. Source snapshots, exact patches,
harness input hashes, receipts, commands, compressed logs and evidence hashes
accompany this report. Frozen binaries and full ELF inventories remain local in
`target/array-union-transmute-investigation/`; independent binary publication
remains open.
