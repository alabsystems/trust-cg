# ControlFlow residual calls on Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`ControlFlow::from_residual` now uses its ordinary Rust body when the callee has
no hidden caller-location parameter. The bridge previously intercepted every
`FromResidual` implementation with a helper that only models Result and Option.
The new path identifies core's actual ControlFlow diagnostic item and retains
the ordinary ABI, MIR, structural and proof checks. It does not synthesize enum
layouts or payload conversions. Result/Option and other residual types retain
their existing admission rules.

The maintained native regression exercises eight modes: integer, all three
Ordering values, unit, shared-reference, mutable-reference and nested-enum
payloads, plus question-mark Break and Continue behavior. Seven edge values and
256 deterministic random values drive independent C expectations. All eight
LLVM/CG executions at O0–O3 pass 2,104 checks each, 16,832 in total. Each run
links the genuine Rust runtime; its separate panic control terminates by SIGABRT.

The genuine Trust/Targo private all-targets check, exact nine-test inventory,
fresh backend build and maintained regression pass. Six unchanged native suites
(TypeId, slice tails, thin pointers, scalar unions, trait-pointer values and
upcasts) pass another 4,475,152 checks. The total is 4,491,984 checks.
Qualification base: `821a232886a7420c8c85d873d716068bc06dea98`, with all five
changed files hashed in `control-flow-repair-first/results.json`.
Backend SHA256: `bb3d56535f84221860627d0cb8baeb0116bf4698ca648a7eb7147e5192e5553f`.
Root formatting passes; private formatting retains 59 preexisting edits and
introduces zero new differences. Changed test and fixture files pass in full.

The original complete core diagnostic falls from 30 failed roots to 27. The
three targeted residual-call failures disappear, with no new roots or changes
to the other failure messages. Full core still fails, including a separate
fully uninhabited ControlFlow body. The unchanged proof-required C FnABI test
still fails TCG-PROOF-465 at `aliased_f32_read`: 14 uncovered instructions across
12 AArch64 opcode kinds. Neither result is recorded as a complete compiler or
proof pass.

The published baseline rejects five residual-call roots in the focused probe;
its LLVM control compiles. The first development native probe passes, followed
by an expanded probe with nested enums, every Ordering value and mutable
references. Both precede the final maintained qualification and are retained
with their exact inputs. The two full-core runs use the complete original
source denominator and unchanged compiler/LLVM control.

Normal fetch/pull/push checks align actual local and remote main in trust-cg,
Trust and trust-ir. Native comparisons explicitly disable frontend verification
and codegen certificates. No installed compiler is promoted, and all G1–G8 and
L01–L14 remain open. The archives retain commands, logs, source snapshots,
objects, native executables and digests; rebuildable large backend/runtime
archives are separately inventoried.
