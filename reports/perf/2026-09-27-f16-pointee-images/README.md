# Half-precision pointee images — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Pointers and references to `f16`, arrays of `f16`, and the native four/eight-lane
NEON types now have size/alignment-correct pointee images. The bridge validates
rustc's layout, array length, vector lane count and native vector alignment,
then uses the existing integer-lane image type to describe the storage behind
the pointer. This representation is consulted only by pointer/reference typing.
It supplies no f16 value type, arithmetic implementation or SIMD value ABI.

This permits stdarch's `as_array` pointer casts and reborrows while preserving
the address and element stride. The memory access paths continue to use the
actual Rust element layout. Scalar f16 addition and load-return roots retain
their specific value-type refusals.

Qualification uses base `874c4b3ef89b26f7fe9a7adc5771bf65db7fdde7`, genuine Trust `ae9c2c1da`, TrustIR
`dcc5b9a3ce02827dca6c3b0ae556d09ca338fdad`, and six maintained source hashes.
Backend SHA-256: `f196c78a6df92efbae8e263378e5b2ab4517abf481b7f5e3678330adf4247ae3`. Native diagnostics disable frontend
verification and codegen proof certificates. The original required proof test
is measured separately; no installed compiler is promoted.

## Validation

- Genuine Targo all-targets check and backend build pass. The ABI test target
  lists exactly 23 tests; both new tests execute and pass.
- Original const pointer casts pass 34,816 checks across LLVM/CG O0–O3. Expanded
  const/mutable casts, element offsets, exact stored bits and caller-owned buffer
  guards pass 94,208 checks. The expanded total includes the original cases.
- Original unsupported f16 scalar addition and load-return controls compile
  with LLVM and are specifically refused by CG at all four optimization levels.
  Each refusal identifies both original roots and `Ty::Float(f16)`.
- Nineteen unchanged regressions pass 5,015,436 native checks. This includes
  272 LLVM-only whole-wide-newtype store checks and 48 LLVM-only aggregate cleanup
  checks whose corresponding CG cases remain refused. The existing over-aligned
  zero-sized Drop refusal controls also pass. New and unchanged suites total
  5,109,644 native checks.
- Root formatting passes. Private formatting has zero new differences beyond
  59 existing library blocks, and all changed
  test and fixture files pass in full.
- Full core has 15 failed roots, actual exit
  1. The maintained build
  has identical backend bytes to the prototype; a checked identity receipt
  reuses that actual core run, without claiming a second compilation. It also
  checks the compiler and entire original source denominator. The published
  17-root census falls by 2, with no new roots or
  changed remaining failure messages.
- The unchanged proof-required ABI test exits 101,
  passed=false, TCG-PROOF-465=true.
  It uses the existing mode0700 private cache. Missing instruction proofs remain
  separate from these native checks.

## Scope and reproduction

The LLVM baselines pass the same caller-owned-memory checks while CG refuses the
pointee type. The reproducer copies the actual stdarch macro's crate-private
`as_array` body and expands it with mutable and offset cases. It performs no
half-precision arithmetic and passes no f16 or SIMD value by value across an ABI.
The negative value tests retain the missing capability explicitly.

The maintained `f16_pointee_images::` tests in `aarch64_c_fnabi_aggregate_linux`
use a support module and three fixtures. Exact test inventory, native markers,
compiler/backend/source identities and original refusal roots are checked by
the archived scripts. Manifests retain baseline and candidate sources, actual
commands and exits, logs, objects and executables. Rebuildable backend/runtime
archives are excluded with hashes. Full core, instruction proof coverage and
all product completion gates remain open.
