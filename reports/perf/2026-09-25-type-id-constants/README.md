# TypeId runtime constants on Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now distinguishes rustc's compile-time TypeId markers from actual
address relocations. The pinned compiler represents a TypeId with two pointer
words; the first carries type provenance for constant evaluation. At runtime
both words contain the type hash. Its LLVM backend explicitly discards that
marker and uses the stored offset bits (`scalar_to_backend_with_pac`).

Whole aggregate constants now accept allocations whose only provenance consists
of those markers. Static and promoted-constant emission leave those hash words
as bytes while preserving every ordinary pointer relocation. A standalone
marker scalar becomes an integer-to-pointer cast of its exact bits, without
inventing an allocation address. Real relocations retain the original admission
rules; this does not permit arbitrary pointer images to be flattened to bytes.

The maintained native test covers eight types: `u8`, `u64`, `i64`, `[u8; 3]`,
`()`, `str`, `&str` and `Option<u64>`. It checks all 64 equality combinations,
returns both hash words to C and requires every LLVM/CG O0–O3 run to match the
actual LLVM O0 bytes. C also reads exported static and promoted mixed globals,
checking hash words, real pointer identity and dereferenced values directly.
Standalone low/high pointer-word constants exercise scalar materialization.
The runtime and its SIGABRT panic control are real linked Rust artifacts.

The genuine Trust/Targo private all-targets check, exact eight-test inventory,
backend build and maintained runtime test pass. The new test performs 164
checks per execution, 1,312 across eight executions. Five unchanged native
regressions (slice tails, thin pointers, scalar unions, trait-pointer values
and upcasts) pass another 4,473,840 checks. The final total is 4,475,152 checks.
Qualification base: `56b557ea41d45f5b0ee267ad9b1a05a3849019fb`, with all five
changed files hashed in `type-id-repair-second/results.json`.
Backend SHA256: `ee414584beab8bd74fa93c59b2de8445cf9e1915f78c572e61acac1988fd3e74`.
Root formatting passes. Private formatting retains the same 59 preexisting
edits with zero new differences; the changed test and fixture files pass in full.
Normal fetch/pull/push and actual remote checks align local/remote main in
trust-cg, Trust and trust-ir before this publication.

The named `MIXED` and `PROMOTED_REF` ELF objects each retain exactly one
`R_AARCH64_ABS64` relocation to `VALUE + 0` at byte 16 at all four optimization
levels. An initial check incorrectly expected two relocations across *all*
objects; O0 also contains a valid private promoted allocation in the function
object. That failed assertion is retained. The corrected check identifies each
named static object, and C independently verifies the resolved values.

The original complete core diagnostic drops from 31 failed roots to 30,
removing `TypeId::of::<PanicInfo::payload::NoPayload>` with no new failures and
no changed error messages for the remaining functions. Full core still fails.
The unchanged proof-required C FnABI test was rerun and still fails
TCG-PROOF-465 at `aliased_f32_read`: 14 uncovered instructions across 12
AArch64 opcode kinds. No proof policy or expected failure was changed.

The original published backend rejects all eight TypeId constructors in the
compile probe; its LLVM control compiles. The first development native run
matches all eight LLVM/CG executions, including mixed globals. The final
maintained test adds direct scalar-word constants and records the exact source
and backend used. No test denominator or resource limit was weakened.

Native comparisons explicitly disable frontend verification and codegen
certificates. These are runtime regression results, not proof authority or
self-hosting. No installed compiler was promoted. All G1–G8 and L01–L14 remain
open. Archived records retain commands, complete logs, source snapshots,
objects, native executables and exact digests; large rebuildable backend/runtime
archives are inventoried separately.
