# Scalar callback source binding and stack-pointer type repair

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge emitted an invalid typed `Copy` from an `Alloca` result: canonical
TrustIR gives `Alloca` the opaque `Ptr` result, but the copy claimed `*mut f32`
or `*mut f64`. The existing reinterpretation pass did not index `Alloca` result
types. It now records that result as `Ptr` and emits an explicit `PtrToPtr`
cast with the actual source type. The canonical validator remains unchanged.

The independent `check_aarch64_scalar_cell_source` API now binds the original
C caller and bodyless external C declaration to retained LIR. It interprets
one initialized scalar cell, typed address transport, floating bit constants,
ordered opaque calls, and the returned bytes without invoking the adapter.
It retains immutable references to both original and lowered endpoints. It
rejects incorrect pointer-copy types, calling conventions, pointer mutability
or extent, signatures, symbol identity, call arguments, volatile operations,
uninitialized cells, malformed control flow, and mismatched observations.
Finite literal values must be exactly representable at their declared width;
parameter and opaque-call result bytes remain unconstrained.

## Executed evidence

- Six real Rust callers at O0–O3 were captured before and after the producer
  repair: `aliased_f32_read`, `aliased_f32_write`, `aliased_f64_read`,
  `aliased_f64_write`, `local_cell_read_f32`, and `local_cell_read` (f64).
  These are 48 actual compilations, with original TrustIR, retained LIR,
  allocated machine debug records, source files, logs and tool identities.
- All 24 original inputs have the specific canonical pointer-copy type error.
  All 24 freshly recompiled repaired inputs pass canonical validation and
  independent source/LIR binding. The integration regression also applies the
  exact product normalizer to the old captures, checking the single changed
  instruction and normalization idempotence.
- The selected frame/source unit suite passes 60 tests, including existing
  instruction-credit refusal controls and seven source-binding tests with
  positive and mutation matrices. This is a selected suite, not all verifier
  unit tests; 3,990 unrelated unit tests were filtered out.
- The unchanged bridge pointer/signature targets plus the new regression pass
  13 tests: eight `bridge_copy_types`, five `bridge_signature_layouts`.
- The Linux gate harness passes 31 tests with its existing non-Linux-only test
  skipped. The required inventory now includes `bridge_copy_types`, raising
  the floor from 125 to 126 families. The previously archived 125-family run
  applies to its own source; this increment does not claim a new full floor.
- The maintained root formatting check passes. The first discovery run
  (56 passed, three failed) and initial inventory-list test failure remain
  archived alongside the corrected runs.

## Source and execution boundary

Both isolated capture builds start at
`1e585e20fe4b43685891d4242013b84f4c1a5208`. The second adds the five-line
`Alloca` type-index repair. The instrumented builds additionally log original
TrustIR and verifier inputs; their exact diagnostic patches and before/after
hashes are retained. Both checkouts were restored and verified clean after
capture. These diagnostic backends were never activated on the machine.
The Trust frontend lane explicitly uses `-Ztrust-verify=off`; backend checks
remain enabled. Fresh production admission was not claimed.

The repaired diagnostic release backend was built with the genuine pinned
Trust compiler. Compilation/testing ran serially under the anchored process
supervisor with a 16 GiB process-group RSS ceiling, zero grace, Cargo jobs two
and one Rust test thread. Complete command, resource, source and dependency
records are retained. Backend binary identities are retained in the records;
the large diagnostic shared libraries are omitted from this archive.

## Remaining obligation

All 48 native compilation attempts remain refused with `TCG-PROOF-465`, and
none emitted an object. The first maintained C-ABI bridge failure therefore
remains open. Source binding is a necessary prerequisite, not instruction
proof credit or native execution. A typed mutable pointer does not assert that
an opaque callback can write only that object: it may also change public
memory. Production calling-frame admission still needs a bound whole-call
memory/ABI composition, private-save separation, independent replay, and
matching emitted bytes and relocations. No L01–L14 closure is claimed.

`inventory.json` records exact and, where compressed, decoded byte lengths
and SHA-256 hashes. The source fixture generator verifies that committed
fixtures are byte-for-byte projections of the retained captures.
