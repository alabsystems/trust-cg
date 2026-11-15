# Slice-tail structs and expanded iterator exits on Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Rust bridge preserves both words of a pointer to a struct whose unsized
last field is a slice or string. The data address names the whole struct; the
metadata counts tail elements. Layout comes from the concrete rustc type and
field offsets, including nested headers, padding and alignment. Unsizing an
array-tailed struct keeps its address and records the array length. Prefix
loads/stores, field borrows, tail reborrows and dynamic size/alignment preserve
that distinction. Trait-object tails and unsupported projections still fail
closed.

The regression also exposed two independent iterator problems. A function item
passed to `fold` now resolves to its concrete function without a closure
environment, and borrowing a function item uses its allocated zero-sized
place address. When a MIR block expands into an iterator loop, outgoing join
and loop-header arguments are attached to the actual exit edges owned by that
MIR block. Arguments are never copied onto another predecessor's edges. Existing
loop mutation and semantic proof checks remain enabled.

The maintained corpus has 14 operations over nested 64-bit slice tails, plus
four byte/32-bit/zero-sized/string tail layouts. It exercises lengths zero
through four, shared/mutable/raw pointers, nested unsizes, prefix and tail
mutation, field reborrows, metadata, dynamic layout and intact surrounding
storage. Noncommutative function-item folds, a loop-carried fold result and a
capturing closure check expanded exit-edge argument order. An independent C
model checks every result and the affected memory, including inactive elements,
padding and sentinels. Each LLVM/CG O0–O3 execution performs 114,490 checks.

The final genuine Trust/Targo private all-targets check, exact seven-test
inventory, backend build and maintained native test pass: 915,920 checks.
The unchanged thin-pointer, scalar-union, trait-pointer and trait-upcast
regressions pass another 3,557,920 checks, for 4,473,840 final native checks.
Every corpus links the actual Rust runtime and checks its SIGABRT panic control.
Qualification base: `614a42ceecd36d708844d1687400675374585de7`, with all six
changed source/test files hashed in `dst-tail-repair-third/results.json`.
Backend SHA256: `95c03e532952e4d5978b2ecb56c3d0a253496ab65fbe75707ec3e14de36ccdd5`.
Root formatting passes. Private formatting has no new differences: deleting
obsolete diagnostic text removes two of the 61 preexisting edits, leaving 59.
The final checks cover the new module and maintained fixtures in full.

Normal fetch, pull, push and actual remote checks aligned all three mains.
Incoming Trust commit `3b30328c071b86da31191bc9e8d7e953a759fa26` was reviewed
and fast-forwarded separately. Its unsigned Clean-call type checking does not
change this compiler pack, fixture repair or pinned dependencies; source-bound
older compiler tests do not qualify that new main.

The complete original core diagnostic drops from 46 failed roots to 31,
removing all 15 `PolymorphicIter<[MaybeUninit<char>]>`/array iterator failures
with no new failing roots. Full core compilation still fails. The unchanged
mandatory proof-required C FnABI test was actually rerun and still rejects
`aliased_f32_read` with TCG-PROOF-465: 14 uncovered instructions across 12
AArch64 opcode kinds. That test's proof policy was unchanged.

The original published backend refuses 15 corpus roots. The first development
repair clears the struct-pointer failures, exposing function-item fold/borrow
refusals; the second exposes the missing synthesized exit-edge arguments.
The original 11-mode native probe then passes 715,000 checks and its expanded
14-mode version passes 910,000. Final integration attempts preserve an actual
duplicate-module build failure and a harness output-label mismatch; both were
repaired without removing tests or changing expected computed values.

All native comparisons explicitly disable frontend verification and codegen
certificates. They provide runtime regression evidence, not proof authority,
self-hosting or whole-system acceptance. No installed toolchain was promoted.
All G1–G8 and L01–L14 remain open. The compressed evidence retains exact source,
commands, complete logs, object files, executables and hashes; large rebuildable
backend/runtime archives are listed separately with exact digests.
