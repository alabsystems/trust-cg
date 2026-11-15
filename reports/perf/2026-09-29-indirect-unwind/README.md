# Linux AArch64 indirect unwind continuations

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Function-pointer calls and dynamic vtable drops can now retain their MIR cleanup
and termination edges on Linux AArch64. Trust IR's `Invoke` names a direct
callee, so the bridge gives each admitted indirect signature a private typed
forwarding function and invokes that boundary. The forwarding function preserves
the original argument and result signature; its ordinary unwind frame leads back
to the caller's landing pad. Result stores and mutable-argument reloads execute
only on the normal continuation. Plain calls without a live cleanup/termination
edge keep their existing lowering.

Source commit: `8df247a87`. Remote main's AArch64 LICM/BCE and proof-tool custody
changes were merged at `4ceee840e`. Subsequent toolchain-policy and x86-only
merges are `31e43efc7` and `a4330ece6`; they preserve the AArch64 lowering. Existing indirect hidden-return-buffer,
virtual-call, and boxed-dyn-Fn admission boundaries were not relaxed.

## Regression evidence

The scalar callback reproducer was refused at O0/O2 before the change; its LLVM
controls pass. The first forwarding implementation passes that callback and
allows optimized `alloc` to compile, but the broader fixture finds an unstored
`MaybeUninit<u64>` return. The indirect scalar path bound the carrier only as SSA
while the address-taken union was read from its slot. The final implementation
stores that scalar carrier in the slot on the normal edge, matching direct-call
handling. Retained before/after binary IR shows the missing and restored store;
the text renderings are diagnostic and identify themselves as lossy.

The permanent tests cover scalar, Rust pair, C pair, u128, HFA, and scalar-union
returns, plus enough integer/floating arguments to cross register and stack
boundaries. Callbacks mutate aliased storage and optionally panic. The driver
checks values, cleanup order, and absence of normal-path actions after a panic.
Dynamic-drop tests pass an LLVM-constructed `Box<dyn Any>` into compiled code,
check null/non-null vtable drop slots, and verify exactly one deallocation after
the destructor and before caller cleanup. An exploratory test constructing the
box inside trust-cg still reaches an existing fat-pointer-field refusal at O2;
this report does not claim that constructor shape is supported.

The final pre-merge backend and rebuilt merged backend each pass **4,765,696
checks in 88 fixture executions**, including existing direct aggregate, associated
destructor, scalar-union, and closure-storage controls. The termination fixture
also observes **112 expected SIGABRT outcomes**, including indirect calls at C
boundaries and double panics. Seven named refusals remain across the groups
(hidden indirect result buffers, disabled EH, unsupported collection/drop and
union shapes), with LLVM controls where applicable. Native execution is diagnostic
codegen, not proof promotion.

## Real libraries and remaining work

Optimized `alloc`, against the recorded LLVM dependency set, goes from two
refused roots to a successful build. It succeeds with both the first forwarding
prototype and the rebuilt merged backend. Fresh mixed-library builds also
succeed with **both core and alloc compiled by trust-cg at O2**, and the rest of
std built by LLVM. The mixed builds take 407.98 and 407.43 seconds; these are observed
build durations, not a performance comparison.

These mixed builds use the completed pre-merge and first merged backends.
Both mixed libraries pass dynamic consumers that load the exact produced libstd:
21,504 network/escape-formatting checks, two sets of 81,097 UTF-8/character-count
checks, and 112 caught panics with payload/destructor checks. Compiler invocation
records identify the selected backends and optimization levels; loader logs and
library hashes identify the executed library.

The isolated full-std O2 probe hits its 600-second deadline after emitting
SSA/IR diagnostics, before producing a complete failed-root inventory. Its
`failed_roots: []` field therefore means **incomplete**, not success. The probe
uses recorded LLVM dependencies and is separate from the successful mixed builds.
Full trust-cg std, complete machine proof, and compile/runtime wins over LLVM and
Clang remain unfinished.

## Proof boundaries and provenance

Strict scalar bridge probes pass at O0/O2 before and after the merge: 11/9 MIR
functions, 11/10 refined obligations, 6/6 memo hits, zero skips, and zero unmodeled
shapes. These are scalar operation-selection checks. Memory, operand wiring,
control flow, and exception tables remain trusted. Machine-proof-required runs
refuse with `TCG-PROOF-465`, including the explicit `TCG-EH-UNPROVED`/TB-12 gate.
The forwarding helpers do not acquire MIR proof coverage merely by being emitted.

Frozen backend SHA256 identities:

- Initial forwarding prototype: `bc25ce54dc8a1b5acbfb6c979580c2700d16f57fe3f3aa42a7c463eae4fd7a70`
- Completed pre-merge fix: `bd1090c134010efe74fc33924ddef5e5d2ae28522adbc8e41b679effc3012bb2`
- First rebuilt merge: `1badb2d848d1664a9a579563a0d02eb2ae5be462b083f1e744f5aaaf9a75d32e`

The final checkpoint also rebuilds successfully after the x86/toolchain merges.
Its focused indirect-return and dynamic-drop tests pass 36,864 checks in 16
fixture executions, with two hidden-result-buffer refusals and two LLVM controls;
its strict/machine probes retain the same pass/refusal boundaries. Final backend:
`d52d2a626e6b5f60eaa4c6bf1b813a014776cb53c8c6a44db186d6ff8b5dd682`.
The intermediate rebuild `97923b69454fc5f0f9ea5250806f26b561b2c17d724c3544f1821519b037f92d`
is a build checkpoint, not a separately qualified native result.

The identical frozen native harness is used for both qualification runs:
`020186b86a842483370c62c38ab8fba833a33afc858da090f45b5339b725af62`.
The final focused run rebuilds the harness to include the updated Trust-only
compiler-selection helper; its separate receipt records that identity.
Production source manifests, patches, harness input hashes, build receipts,
commands, compressed logs, and evidence hashes accompany this report. Patch and
environment snapshots retain their exact bytes in gzip files. Native and
strict tests use the private AY cache; library probes preserve their recorded
baseline diagnostic cache policy. Full binaries, sysroots, and ELF inventories
remain local under `target/indirect-unwind-investigation/`; independent artifact
publication remains open.
