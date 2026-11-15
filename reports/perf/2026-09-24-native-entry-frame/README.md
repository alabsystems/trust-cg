# Native AArch64 entry-frame regression — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**PASS on `56d8751961a711a31a6456f2b2091a98f3ce1c8f`: all three live-frame
integration tests and the focused frame unit test.** The integration target has
zero failed, ignored or filtered tests. The unit command selects one test and
discloses 4,209 filtered tests; it is not a full codegen unit-suite result.

The new regression executes entry-block backedges with an ordinary frame and a
1 MiB probed stack slot, for 0, 1, 2, 7, 31 and 4,096 backedges at each of
O0–O3. An external assembly/C observer checks the caller's stack pointer before
its own prologue, stack alignment, stable slot identity, exact call counts
and return values; it writes both endpoints of the stack slot. All 48 native calls and 33,144 stack
observations pass. Four separately injected assembly loops repeat frame
allocation deliberately; every one exits with exactly `ENTRY_STACK_CHANGED`
and status 83. Independent C reference implementations also pass the observer.
The existing masked-bounds regression adds 4,100 native calls.

The pre-fix `c29c68640` compiler, with the exact final test source overlaid,
**refuses the valid entry loop** with `[TCG-A64-SPILL-SLOT]`: the repeated
prologue reads a call-clobbered return address and cannot restore the entry
frame state. It does not emit a wrong native executable in this run. The repair
retains that verifier and passes it before native execution. Baseline and
candidate used separate source-bound Cargo caches and distinct test executable
hashes. The frame unit covers both small and probed frame layout.

## Preserved attempts

The first qualification never started a compiler: its preceding scheduler
failed while inspecting a process that exited. The second reached an invalid
new fixture, which lacked required TargetInfo for its external declarations.
The diagnostic records identify that missing metadata. The fixture was corrected
to specify Linux AAPCS64; validation was retained. The third then reached the
real pre-fix spill-slot refusal. Its orchestrator had incorrectly expected a
native failure, so that attempt is retained as failed. The fourth uses the
hash-bound targeted refusal as baseline evidence and requires the repaired
candidate to execute. No verifier, native assertion or floor requirement was
relaxed. The first independent C control extraction also failed because its
harness regex crossed Rust raw-string boundaries; the corrected extraction and
both results are retained.

## Reproduction and scope

The inventory binds compressed and uncompressed raw records,
source, runner scripts, observer controls, emitted objects and native executables.
Stock Rust 1.97.1, offline locked dependencies, one Cargo job and one test thread
were used under an enforced 8 GiB process-group limit with zero grace. Resource
admission used live available memory and the existing exclusive harness lease;
other worktrees did not need to stop compiling. This is correctness regression
evidence, not a controlled performance comparison.

The test is required by the maintained Linux floor, whose live-frame minimum is
now three passing tests. The separate complete 167-target run is not included in
this focused result. These finite checks do not establish a universal frame,
external-call memory, unwind or whole-compiler correctness proof.
