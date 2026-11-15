# Trait-object aggregate leaves from memory — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A closure-returned trait object can live in a memory slot. Storing that value
inside another aggregate previously looked only for projected SSA bindings,
refusing `core::fmt::Formatter::wrap_buf` with “Place projection field 0 before
aggregate binding.” The bridge now recovers both the data pointer and vtable
from the source's actual representation and stores both at rustc-derived offsets.

This native lowering repair is qualified on
`19846b93751a43d43a808e6e8855436b953bb008`, with seven exact source hashes in
the maintained qualification receipt. Genuine Trust `ae9c2c1da` builds and tests
the backend using TrustIR `794227ad`. Backend SHA-256:
`67250f2db346457636b6a6ab138a5b27e4d5fcb489171797122c3e11b2156ade`. These diagnostic lanes explicitly disable frontend
verification and codegen proof certificates; no installed toolchain is promoted.

## Behavior and admission

The source must remain an unprojected local with a trait-object pointer type.
Existing complete projected pairs still work; memory-backed sources load both
halves through the established fat-pointer helper. The vtable's destination
offset comes from `fat_ptr_metadata_offset` and checked offset addition.
Non-place operands, projected sources and incomplete pairs remain refused.

The tests exercise a captured mutable closure returning `&mut dyn Sink`, followed
by aggregate construction and virtual dispatch through the stored field. They
also cover shared and raw trait-object fields, two different implementations
with distinct vtables, mutations to caller-owned storage and neighboring guards.

## Validation

- Genuine Targo all-targets check and backend build pass. The maintained ABI
  target lists exactly 17 tests; both new tests execute and pass.
- LLVM and CG O0–O3 pass 5,568 native checks in eight executions. The original
  captured mutable case contributes 4,608; shared/raw fields and distinct
  vtables contribute another 960. Buffer and aggregate guards are checked.
- The original cleanup case runs on LLVM at all four optimization levels:
  48 checks cover normal return, caught panic payload, callback count,
  destructor count, unchanged storage and guards. CG specifically refuses
  all four with `TCG-EH-CALL-EDGE` for the unsupported aggregate-return cleanup
  edge. A timeout or unrelated failure cannot satisfy this negative control.
- Thirteen unchanged maintained regressions pass, including 4,919,412 native
  checks and the four zero-sized over-alignment refusals. Total native checks
  including this repair and the LLVM cleanup control: 4,925,028. This count
  includes the 48 LLVM-only cleanup checks; CG does not execute that case.
- Root formatting passes. Private formatting introduces no new differences
  beyond the 59 pre-existing library blocks; all changed fixtures pass in full.
- Full original core diagnostic: 22 failed roots, actual
  exit 1. Exactly the Formatter
  wrapper failure disappears from the prior 23-root census. No new roots or
  changed remaining failure messages occur. Both prototype and maintained
  measurements are retained; neither is a clean core/self-host build.
- Unchanged proof-required C ABI test: actual exit
  101, passed=false,
  TCG-PROOF-465=true. Runtime success does not
  satisfy this proof gate.
- A separate rerun with a fresh mode0700 XDG cache removes the AY identity
  materialization error. It still exits101 with TCG-PROOF-465: 14 uncovered
  emitted instructions across 12 distinct AArch64 opcodes, starting with
  StpPreIndex. Both original-cache and private-cache results are retained.

## Retained failures and limits

The initial baseline also attempted real pretty-debug formatting and a mutable
trait coercion of a scalarized local, exposing separate borrowed-aggregate,
raw-dereference and mutable-copy restrictions. Those failures are retained.
The second baseline isolates the original wrapper with caller-owned storage:
LLVM passes, CG refuses the wrapper at O0 and O3. The same wrapper passes after
the repair. The expanded corpus then checks the shared/raw cases at O0–O3.

Aggregate-return cleanup remains unsupported as the explicit negative control
shows. The implementation does not change EH lowering or loosen that refusal.
All product completion gates, the remaining core roots and missing opcode
proofs remain open.

## Reproduction and records

The maintained tests are `trait_leaf_memory::` in
`aarch64_c_fnabi_aggregate_linux`, backed by
`crates/rustc-codegen-trust-cg/tests/support/trait_leaf_memory.rs` and four
fixture files. The archived qualification scripts bind compiler, private
sysroot, source, backend and test-binary identities and enforce the exact test
inventory and execution markers. `manifest.json`, `assets.json`, `excluded.json`
and `inventory.json` bind all records. Rebuildable backend/runtime archives
are excluded with hashes; sources, logs, objects and executables are retained.
