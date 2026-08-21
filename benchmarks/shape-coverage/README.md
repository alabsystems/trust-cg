# Shape-coverage differential gate (rustc bridge)

One program per *shape*, compared against rustc's LLVM backend at O0–O3, with
every binary run twice so an out-of-bounds read shows up as run-to-run
variation.

This exists because the differential fuzz campaign drives the trust_ir and
LLVM-import frontends, while the **rustc bridge** — the primary user-facing
frontend — had no differential net beyond the 18-program `beat-llvm` corpus.
An audit on 2026-08-18 found seven wrong-code bugs reachable from ordinary
Rust; the corpus contained none of the shapes that triggered them.

Each program's name records the shape and, where applicable, the pass whose
recognizer/emitter disagreement it pins:

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

Exits non-zero if any shape disagrees with the LLVM oracle.
