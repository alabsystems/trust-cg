# Scalar closure wrappers on Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A scalar-sized struct can contain a closure whose MIR representation is still
an aggregate. The bridge now reads that closure's single captured scalar from
its real slot when constructing the wrapper. It requires exactly one leaf at
byte zero, the expected scalar type, the entire layout size, and rustc's Scalar
representation. Pointer captures remain pointer-typed values.

Borrowing a closure through scalar wrappers now gives the wrapper a stable
scalar cell. A shared or mutable closure environment points into that cell.
The same layout witness governs allocation and borrowing: direct field chains,
one zero-offset field per level, exact size and alignment against the actual
allocation, matching leaf type, and no drop-bearing or intercepted collection
representation. Non-scalar wrappers use their existing memory layout. When MIR
inlining replaces the closure borrow with a direct captured-scalar write, that
projection also requires the cell. Primitive cell access admits a closure
container only under its existing full-allocation size/alignment checks.

The maintained test has six functions: shared and mutable reference captures,
owned integer captures including repeated mutation, and nested wrappers of
shared and mutable captures. Seven edge values and 256 deterministic random
values exercise return values, caller-memory updates and adjacent sentinels
against independent C expectations. LLVM and CG pass at O0–O3. Two additional
O0 executables combine LLVM callers with CG wrapper constructors and CG callers
with LLVM constructors. Both original objects must contain real CALL26
relocations to all eight wrapper monomorphizations. Symbol binding selects the
implementations; their compiled bodies and environments remain intact. All ten
executions pass 3,682 checks each, 36,820 in total. The genuine linked Rust
runtime also passes its SIGABRT panic control.

Genuine Trust/Targo all-targets, the exact ten-test inventory, fresh backend
build and maintained native test pass. Seven unchanged native regressions pass
another 4,491,984 checks, for 4,528,804 total. Qualification base:
`62360f69f0befb5c5124a6cb88f00e470c2ff242`, with all five changed files hashed
in `closure-wrapper-repair-first/results.json`. Backend SHA256:
`db6ab387f617b96c5a568cc7cb5dcb6703b03d3864979978d0da344cc0293f46`.
Root formatting passes; private formatting retains 59 preexisting edits and
adds none. Changed tests and fixtures pass formatting in full.

The complete original core diagnostic falls from 27 failed roots to 24,
removing three `fmt::builders::from_fn` monomorphizations. There are no new roots
or changed error messages among the remaining failures. Full core still fails.
The unchanged proof-required C FnABI test still fails TCG-PROOF-465 at
`aliased_f32_read`, with 14 uncovered instructions across 12 opcode kinds.

The first probe reproduces four failures on the immutable earlier ControlFlow
development backend. The first wrapper prototype removes the constructor
failures but still rejects the callers' closure borrows. The second passes the
basic eight-run native corpus; the extended corpus then exposes the inlined
owned-mutation refusal at O2. Those failures are retained, followed by the final
maintained qualification covering every original and extended case. Three
complete-core runs retain the same original source/compiler denominator.

Normal fetch/pull/push checks align local and actual remote main in trust-cg,
Trust and trust-ir. These native lanes explicitly disable frontend verification
and codegen certificates; they confer no proof authority. No installed compiler
is promoted. All G1–G8 and L01–L14 remain open. Archives retain exact commands,
logs, source, objects, executables and digests; rebuildable backend/runtime
archives are separately inventoried.
