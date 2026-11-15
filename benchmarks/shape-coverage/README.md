# Shape-coverage differential gate (rustc bridge)

One program per *shape*, compared against trustc's LLVM backend at O0–O3, with
every binary run twice so an out-of-bounds read shows up as run-to-run
variation.

This exists because the differential fuzz campaign drives the trust_ir and
LLVM-import frontends, while the **rustc bridge** — the primary user-facing
frontend — had no differential net beyond the 18-program `beat-llvm` corpus.
An audit on 2026-08-18 found seven wrong-code bugs reachable from ordinary
Rust; the corpus contained none of the shapes that triggered them.

Each program's name records the shape and, where applicable, the pass whose
recognizer/emitter disagreement it pins. The table below records the founding
`s01`-`s24` corpus; the later `s25`-`s72` sources carry a one-line shape and
regression description beside the executable fixture, and the salvage ledger
records their provenance:

| program | shape | pass it guards |
| --- | --- | --- |
| `s01_fill_f32` / `s02_fill_f64` | FP-valued fill loop | `neon_fill` (element width from register class; `DUP` fed an FP register into a GPR field) |
| `s03_fill_u16` | narrow integer fill | `neon_fill` |
| `s04_matmul_i32` / `s05_matmul_i64` | register-blocked matmul | `mac_reg_block` (64-bit lanes hardcoded; scale-4 read two packed i32s and over-read the array) |
| `s06_seeded_reduction` / `s07_…_i64` | reduction with a NON-ZERO initial accumulator | `neon_reduce` (drain overwrote the accumulator instead of folding) |
| `s08_cond_store` | store under an internal condition | `strided_store_unroll`, `mac_row_unroll` (store not proven to execute on every path) |
| `s09_bitrev_carried` | `reverse_bits` plus a second loop-carried value | `neon_bitrev` |
| `s10_mixed_types` | mixed element widths in one loop | `vectorize` (element-type homogeneity) |
| `s11_slice_sum_u64` | bounds-checked `Vec` slice sum, seeded | `neon_array` chain lane |
| `s12_fp_reduction` | FP reduction (non-associative — must NOT reassociate) | vectorizers generally |
| `s13_zero_trip` | zero- and tiny-trip counts around vectorizable loops | all vector lanes (drain/tail correctness) |
| `s14_i8_i16_reduce` | narrow element widths through a reduction | widening lanes |
| `s15_fill_merge_value` | fill value selected by a multi-predecessor merge | `neon_fill` (single reaching-definition discipline) |
| `s16_reassigned_bound` | loop bound reassigned in the body | `strided_store_unroll` (single reaching-definition discipline) |
| `s17_mac_offset_index` / `s18_strided_offset_index` | address formed from an offset or incremented induction value | MAC and strided-store lanes (exact induction identity) |
| `s19_iota_merge_addend` / `s20_iota_merge_bound` | affine addend or bound selected by a merge | `neon_iota_fill` (single reaching-definition discipline) |
| `s21_bytesum_ptr_offset` / `s22_bytesum_merge_bound` | offset induction value or merged bound in a byte sum | `neon_bytesum` (exact induction and bound identity) |
| `s23_abi_stack_arg_return_clobber` | dead stack-argument load beside an ABI return-register write | scheduler fixed-PReg/VReg anti-dependencies |
| `s24_sret_nested_indirect_return` | large aggregate return around a nested indirect return | preserve the incoming AArch64 X8 sret pointer across calls |

Adding a shape is the point: when a pass is fixed for a shape the corpus
lacked, put that shape here so it stays fixed.

## Usage

    ./run.sh [path/to/librustc_codegen_trust_cg.so]

Exits non-zero if any shape disagrees with the LLVM oracle, if the LLVM oracle
cannot compile a corpus source, or if the backend's exact decline set changes.
The ratcheted final-s72 decline set is ten rows: `s13` at O2/O3 and every level
of `s27` and `s31`. A new decline loses executable differential coverage; a
newly supported row makes its old allowance stale. Both require a conscious
runner update. `./run.sh --selftest` checks the exact decline allowlist.

## The declines: 11 -> 2 (2026-08-25)

The diagnostic read `Ty::[T; N]`, which sounds like "arrays are unsupported"
and was never what was wrong. Bare arrays were always fine — `[i8; 64]`,
`[i32; 576]`, by value through `black_box`, summed with `.iter().map().sum()`,
all compiled and matched at every opt level. Three separate defects wore that
same message, plus one unrelated encoding bug:

1. **A for-loop over a CONST-FOLDED range.** At -O1 rustc const-propagates
   `for i in 0..64`, so `into_iter` receives `Operand::Constant` and there is no
   source place to copy the iterator state from. Four programs, -O1 only. The
   place path is a memcpy between identical layouts, so writing the constant's
   own byte image is the same store. `RangeInclusive` had the identical gap.

2. **A struct/array field offset past 4095.** `select_struct_gep` emitted a bare
   `AddRI`; AArch64 `ADD (immediate)` is 12 bits with an optional `LSL #12`, and
   the overflow surfaced only in the ENCODER. `[i64; 576]` reaches it — element
   512 sits at byte 4096. `emit_pointer_add_const` is now total over every
   offset.

3. **An array as a FIELD of an aggregate, and the transmute producing one.**
   The shape rustc emits once `<[T; N] as IntoIterator>::into_iter` inlines. The
   scalarized representation binds leaves as individual SSA values and has no
   spelling for an array field. Fixed with `lower_aggregate_transmute_slot_copy`
   plus rules 0e/0f in `compute_memory_backed_locals`.

**A note on (3), because the intermediate results were misleading.** Rules 0e
and 0f are BOTH required and NEITHER is sufficient. Memory-backing the affected
locals alone leaves the compile declining on the transmute; handling the
transmute alone leaves it declining on the wrapper construction. Each attempt
looks like it achieved nothing — the error message simply moves — and an
earlier version of this file recorded "memory-backing is NOT sufficient" as a
dead end on exactly that evidence. It was necessary but not sufficient. When a
fail-closed diagnostic moves to a different type after a change, that is
progress, not a null result.

## Expected fail-closed declines (10 rows, 3 shapes)

`s13_zero_trip` at -O2/-O3. They are blocked one layer deeper than the above:
`array::IntoIter::unsize_mut` coerces
`&mut PolymorphicIter<[MaybeUninit<T>; N]>` to
`&mut PolymorphicIter<[MaybeUninit<T>]>` — a fat pointer to an UNSIZED struct
with a trailing slice. Supporting that means representing unsized-struct
references, a much larger feature than anything above and unrelated to arrays
as such. The same program compiles and matches at -O0/-O1.

`s27_dyn_box_drop` at -O0 through -O3. The drop-in-place vtable entry reaches a
projected aggregate field before the aggregate has a lowering binding. The
backend deliberately rejects that ordering instead of inventing a value for
the projection.

`s31_vec_sort_dedup` at -O0 through -O3. The inlined sort comparator reaches a
`PartialOrd::lt` function-definition carrier that the bridge does not yet
lower. It likewise remains fail-closed at every optimization level.

These are coverage gaps, not passes. `run.sh` requires exactly these ten rows:
if another row declines, or one of these rows starts compiling without its
allowance being removed, the gate fails.
