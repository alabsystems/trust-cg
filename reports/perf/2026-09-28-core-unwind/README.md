# Linux AArch64 core with unwinding

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The frozen full-feature core source now compiles with unwinding at O0 and O1.
Two narrow bridge repairs remove the four previous O0 failures without
weakening SSA validation. Building core does not yet qualify its panic runtime.
**Core panic execution, optimized unwind core, full std, shared-library
linkage, mandatory machine proof, self-hosting, and strict compile/runtime wins
over LLVM and Clang remain open.**

## Repairs and tests

The loop source-consensus and symbolic walkers now accept modeled calls with
`UnwindAction::Continue`. An unwind leaves the function, so only the normal
return can reach its loop latch. Existing call identity, integer semantics,
aliasing, and result-use restrictions remain active. Cleanup and terminate
edges are still outside these call models. This handles the u64/u128 overflowing
power loops and maximal-suffix search that previously failed validation.

The remaining O0 failure was an unused forward-join parameter on an unwinder-only
landing-pad head in `try_from_fn_erased`. The new cleanup pass removes a block's
entire parameter list only when every parameter is unused, the block begins with
a landing pad, it is not the function entry, and no normal edge targets it. It
uses the verifier's operand and edge enumerators, preserves all instructions,
and declines to change functions containing instruction proof metadata. Live
cleanup values still fail the unchanged argument-arity check.

Five pure-IR tests cover dead parameters, live instruction and edge operands,
normal incoming edges, and the function entry signature. The expanded permanent
overflow-loop matrix passes **393,216 native checks in 16 executions**: LLVM/CG,
O0–O3, and abort/unwind. It adds full-width u128 powers with an independent
division-based overflow oracle. O0 traces require a successful back-edge proof
for all six kernels in each panic mode. Four negative controls still refuse
unmodeled calls or disabled diamond modeling; LLVM accepts all four.

The old backend fails the expanded unwind fixture at O0/O1 and passes at O2/O3;
LLVM passes at every level. Five existing regression tests pass **178,272
checks**, including unwind calls, terminate pads, aggregate returns, associated
drop, and try-fold. The terminate-pad regression additionally verifies 80
SIGABRT subprocesses and four refusals; the unwind-call regression retains its
two cleanup refusals. The all-target check, formatting, documentation inventory,
and diagnostic inventory pass.

## Build coverage and limits

The fresh CG dependency graph attempts 19 target crates: **8 pass and 11 fail**.
Its failing roots decrease **108 → 103**, with no added roots, changed retained
diagnostics, or compiler crashes. Core removes four roots and alloc's
`str::to_lowercase` removes one. Cargo still cannot reach std through the failed
dependencies.

Isolated std O0 completes with **330 failing roots, down from 348**, using the
same LLVM-built dependencies. Eighteen old failures disappear and no new root
symbols appear. Eight retained roots report a different first SSA arity failure;
the full before/after diagnostics are archived. Live cleanup transport remains
unsupported in those cases. This isolated probe does not qualify a CG std.

Isolated core builds emit rlibs and metadata at O0/O1. At each of O2 and O3,
both the baseline and repaired backend reject the same **24 roots with identical
diagnostics**. Remaining categories include constant aggregate images,
discriminants, borrowed aggregate shapes, raw-pointer reborrows, and one
loop-carried update. The separate earlier panic-abort core/alloc campaign is
not evidence that this unwind configuration works at these levels.

A library integration probe rebuilds core with CG and its dependent libraries
with LLVM. The default std build reaches the shared-library link and fails on
`R_AARCH64_ADR_PREL_PG_HI21` relocations against externally binding core symbols.
An explicit static-only std replay succeeds. Two static consumers, compiled by
LLVM and CG at O0, then pass **162,194 checks** for UTF-8 validation and character
counting against an independent C oracle. Object/symbol checks confirm the
actual CG core implementations are defined in both executables. This is a
mixed-toolchain integration probe, not a CG-built std or a dylib qualification.

A further panic/catch/drop probe exposes a runtime blocker: the CG core's
`core::panicking::panic` calls itself until stack overflow (SIGABRT). The
archived disassembly contains the self-call and the debugger backtrace shows
repeated panic frames. The panic-block rewrite assumes the panic entry comes
from a precompiled core; that assumption is invalid while building core itself.
The same source passes with the coherent LLVM core and dependencies, including
16 caught panics and 16 destructor executions. The successful normal-path CG
consumer checks do not qualify panic propagation.
An earlier direct swap of isolated CG core into old LLVM dependencies was
rejected with E0460 metadata mismatch; all successful static consumers instead
use the rebuilt coherent dependency graph.

Strict bridge probes pass at O0/O2: **12/6 functions**, **34/22 pushed refinement
obligations**, zero unmodeled shapes and zero skipped obligations. Mandatory
machine proof still refuses uncovered emitted instructions with
`TCG-PROOF-465`. Compiler runs disable Trust frontend verification. Development
timings collected during concurrent work are diagnostic measurements, not
performance comparisons.

## Reproduction and identities

Final production evidence uses `build-second.log` and `second-backend.so`.
Native fixtures and regression controls use `test-build-first.log` and
`first.test`. The cleanup unit tests were rebuilt and rerun after formatting;
their final executable is `cleanup_params-second.test` from
`test-build-second.log`. Production sources match the second backend's frozen
source copies. An initial backend launch failed before execution because its
copied build script was not ready; the terminal retry is retained separately.

The archive includes exact commands, complete diagnostic and failure logs,
source snapshots, patches, native objects and executables, and artifact hashes.
It retains the same 3,044 frozen std/registry source inputs and fingerprints of
the compiler and LLVM dependency artifacts. Large backend/test/library binaries
are identified by hash and can be rebuilt from the recorded sources and commands.

Backend SHA-256:
`fdfad748760cb050fc22b8fb34c4334a1c77ebf8354101e52e975dc45572f106`.

Native test executable SHA-256:
`14cf25bd58c738aa841a42eff033c160e4167d311e5b67269db393fb4a4585c5`.

The archive contains 20,698 independently rehashed files, including
283 current backend/test source and documentation files and 3,044 frozen
std/registry inputs. Archive SHA-256:
`942dceeb3a0fe066e2a94de1f3275d933b35ddb73cf5a0a4acaa8c7822fcfd67`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
