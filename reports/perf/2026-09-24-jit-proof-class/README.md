# Source-attributed JIT arithmetic regression — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Both JIT arithmetic tests pass at `744303be4ddcc6d8872412047665bb71a3b839d2`:
160 proof-required compilations, 23,040 native calls, 84 emitted-ADD byte
mutations, and 84 explicit-LSL byte mutations. No tests are ignored or filtered.
The request/cache controls retain changed-input, stale-stamp and missing-authority
refusals. The compiler and proof grades are unchanged by this test repair.

The previous full Linux floor at `56d8751961a711a31a6456f2b2091a98f3ce1c8f`
completed all 167 targets: 166 passed, and this two-test target failed because
both tests expected doubling to be rewritten to a shift. The source-proof-class
guard intentionally keeps attributed ADD instructions until a checked class
rebind exists. The test now checks the emitted ADD and mutates its register,
shift, width and opcode bits. Independently assembled LSL encodings preserve
the byte checker's shift coverage without fabricating a machine proof stamp.

The inventory retains every log from the completed failing
167-target run, the passing focused run, exact source and runner, independent
assembler control, and compressed/uncompressed hashes. Native execution used
stock Rust 1.97.1, locked offline dependencies, the pinned AY/Clean tools, one
Cargo job and one test thread, and an 8 GiB process-group limit with zero grace.
The original source path retains exclusive ownership of its Cargo target cache.

A full 167-target rerun at the repaired revision is still in progress when this
focused report is recorded. This report does not claim it passed. Finite native
and mutation tests do not establish whole-compiler correctness or completion.
