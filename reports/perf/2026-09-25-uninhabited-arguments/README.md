# Uninhabited arguments and live zero-sized values

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now normalizes a function body to Unreachable when rustc reports
that a concrete, monomorphized argument layout is uninhabited. The signature
is retained and the body still passes through ordinary MIR lowering, ABI,
structural validation and proof checks. A failed layout query does not admit
this normalization. Zero size is never evidence that an argument is invalid.

Inhabited neighboring types exposed additional lowering gaps. Zero-sized
arrays and unions now map to Unit using rustc's complete layout. A validated
zero-byte union construction writes nothing and leaves an enclosing projected
aggregate's bindings intact. Static enum discriminants now use the actual
projected enum type and rustc's Single variant index before attempting a tag
load. Multi-variant enums retain their existing tag/niche handling.

The maintained regression compiles five exported functions with impossible
arguments, including a fully uninhabited ControlFlow residual, a direct empty
enum, a tuple with a nonzero-sized field, and a nonempty array of an empty enum.
It never fabricates or calls an invalid argument. Four live C entries exercise
ordinary question-mark control flow, Option<Never>, MaybeUninit<Never>,
[Never; 0], a custom zero-sized union, [(); 3], and a tagged Option<u64>.
Seven edge values and 256 deterministic random values are checked against
independent C expectations. LLVM and CG pass 1,052 checks each at O0–O3:
8,416 total. The real linked Rust runtime passes the SIGABRT panic control.

Genuine Trust/Targo all-targets, the exact eleven-test inventory, a fresh
backend and the maintained native regression pass. Eight unchanged native
regressions pass 4,528,804 more checks, for 4,537,220 total. Qualification base:
`f9d9fd6047d5a4e2198a728948172c941683feab`. All five changed source files are
hashed in the qualification receipt. Backend SHA256: `90cb7bdb597e062ea09f0ca7286d0e269f6b26dcea42961e889019dbf0b41ce1`.
Root formatting passes. Private formatting retains 59 preexisting changes and
introduces none; changed tests and fixtures pass their complete format check.

The original complete-core diagnostic falls from 24 failed roots to 23,
removing the fully uninhabited ControlFlow residual-conversion body. There are
no new roots or changed remaining diagnostics. Full-core compilation still
fails. The unchanged proof-required C FnABI test still fails TCG-PROOF-465 at
aliased_f32_read, with 14 uncovered instructions across 12 opcode kinds.

The archives retain both original reproducers, development builds and their
failures. The first body repair removes the residual failure while exposing
zero-sized union mapping. The next expanded native probe records three
additional refusals before the final repair. The original iterator reproducer
is rerun unchanged against the final backend and still rejects its untagged
try_fold result; that separate interceptor gap remains open.

Normal fetch, pull and push align local and actual remote main in Trust,
trust-ir and trust-cg. These native lanes explicitly disable frontend
verification and codegen certificates; they provide no proof authority.
No installed compiler is promoted. All G1–G8 and L01–L14 remain open.
Archives retain exact commands, source, logs, objects, executables and hashes;
rebuildable backend/runtime archives are separately inventoried.
