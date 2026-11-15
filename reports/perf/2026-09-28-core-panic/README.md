# Linux AArch64 core panic runtime

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

CG-built core now raises and propagates the tested panics at O0 and O1 with the
original payloads, caller locations, and destructor execution. The previous
runtime recursively called its own panic entry until stack overflow. The
repairs preserve real panic calls while compiling standard-library code.
**Full std, optimized unwind core, shared-library linkage, mandatory machine
proof, self-hosting, and strict compile/runtime wins over LLVM and Clang remain
open.**

## Cause and repair

Two legacy shortcuts assumed a precompiled panic runtime. One replaced a whole
diverging panic block; another replaced a diverging tracked call. Compiling
core's `panic` with either shortcut could turn its call to `panic_fmt` back into
`panic`, causing recursion. Merely preserving the first block was insufficient:
the tracked-call shortcut still discarded the real message.

The bridge now excludes panic runtime definitions from both shortcuts and uses
the existing `std_def_is_interceptable` boundary for panic interception. Sysroot
builds retain their own and upstream real calls, including helpers outside the
panic module. The same predicate controls formatting-liveness analysis, so the
real payload construction is preserved with the call. Ordinary direct-call
lowering supplies the hidden caller-location argument and the original unwind
or terminate edge. No SSA or machine-proof check is bypassed.

The second candidate fixed the runtime entry but still synthesized the payload
for core's string bounds helper. A caught payload is program-visible: changing
its type or contents is not merely a printing difference. The final candidate
preserves that helper's calls too, and the original bounds/catch/drop reproducer
passes with the expected messages. Application-build panic interception remains
outside this repair; this report does not claim complete panic-message fidelity
for every application shape.

## Permanent tests and library execution

The new permanent matrix compiles core/alloc/std crate-name fixtures with LLVM
and CG at O0–O3 in both panic modes. It passes **18,432 caught-panic checks in
24 executions**, checking exact literal, formatted, and forwarded payloads,
caller locations, cleanup effects, and helpers outside the panic module.
It also passes **96 SIGABRT subprocess checks** for abort builds and non-unwinding
entries, including the actual panic text and the nounwind termination message.
These crate-name fixtures test the interception boundary; the separate builds
below exercise the actual core library.

Seven existing regression tests pass **3,383,456 checks**: sysroot iterator
layouts, caller locations, unwind calls, terminate pads, aggregate returns,
associated drop, and try-fold. They also retain 80 SIGABRT checks and six
refusal controls. The all-target check, formatting, documentation inventory,
and diagnostic inventory pass.

The baseline backend compiles the permanent fixture but fails its native
payload checks at every optimization level. LLVM passes at every level. An
initial task-local fixture omitted an unstable feature gate and was rejected
by both compilers before code generation; corrected sources and all intermediate
failures are retained.

Two coherent static library graphs build actual core with CG at O0 and O1,
and the dependent libraries with LLVM. Four LLVM/CG consumers pass **324,388
checks** against an independent C oracle for UTF-8 validation and character
counting. At each core optimization level, the original string-bounds test
passes 16 catches/drops, and direct literal, dynamic, and formatted panic-entry
tests pass another 96 catches/drops: **224 caught panics and 224 destructor
executions** across the two core builds.

Six additional subprocesses call the actual core's nounwind, cleanup-panic,
and C-boundary panic entries at O0/O1. All terminate with SIGABRT, the correct
message, and the runtime's non-unwinding termination diagnostic. The private
lang-item probes use symbol names checked against the compiled library and
their no-argument ABI in the frozen source; the initial direct Rust calls were
rejected by privacy checking and are retained as harness failures.

ELF and archive checks identify the CG core implementations in the consumer
executables. Disassembly verifies that core's panic entry calls `panic_fmt`
and does not call itself. These are mixed CG-core/LLVM-dependency static builds.
The std dylib relocation failure discovered in the preceding report remains
open; static-only builds here explicitly request an rlib and do not qualify
shared-library linking.

## Remaining compilation and proof work

The full CG dependency graph remains at **19 attempted crates, 8 passes, 11
failures, and 103 failing roots**, with identical root diagnostics and no
compiler crashes. Core succeeds in that graph. Isolated O1 core also succeeds.
At O2 and O3, failing roots decrease **24 → 23** each: `panic_nounwind_fmt` now
lowers. No added roots or changed retained diagnostics appear in either
optimized-core comparison. Other sysroot compilation gaps remain open.

Isolated std O0 completes with **330 failing roots**, the same total as before.
`std::panicking::resume_unwind` now lowers. Preserving real assertion payloads
also exposes one new refusal: `assert_failed::<[u8; 4], &[u8]>` cannot yet
materialize a data pointer for a trait-object unsizing conversion. Six existing
btree failures retain the same pointer-cast error with shifted value IDs.
These exact diagnostic changes are archived. The isolated std probe still uses
LLVM-built dependencies and does not qualify a CG std library.
The small `assert-slice.rs` reproducer also captures the new trait-object
refusal independently of the full std build.

Strict bridge probes pass at O0/O2: **13/9 functions**, **2/4 pushed refinement
obligations**, zero unmodeled shapes and no skipped obligations. Mandatory
machine proof still refuses uncovered emitted instructions. All diagnostic
compiler runs disable Trust frontend verification. Timings taken during
concurrent development are not performance comparisons.

## Reproduction and identities

Final production evidence uses `build-third.log`, `third-backend.so`, and its
frozen `third-lib.rs`. The permanent matrix and regression controls use
`test-build-first.log` and immutable `first.test`. Earlier candidate builds,
fixture failures, and the baseline panic-recursion evidence are retained.

The evidence includes exact commands, complete logs, source snapshots, patches,
native objects and executables, artifact identities, and the same 3,044 frozen
std/registry source inputs. Large backend/test/library binaries are identified
by hash and can be rebuilt from the recorded sources and commands.

Backend SHA-256:
`a9f1196d188e4fb3ddc13ffbf2888d279c00463e2977fc7c288c1e6b07d82803`.

Native test executable SHA-256:
`c24bbf8c487cfca02f6f9e57692982630399a3127d963b9a2ee0b6b333652ac6`.

The archive contains 21,440 independently rehashed files, including
286 current backend/test source and documentation files and 3,044 frozen
std/registry inputs. Archive SHA-256:
`b95c8d5cab9bbb728982b6f01bdd2f8cb21cefa8e100efcc3e2bc6d14a8e3ac5`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
