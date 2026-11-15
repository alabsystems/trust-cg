// (b) The ZST-reference placeholder is one entry-block `Alloca` per borrowed
// zero-sized PLACE (so `ptr::eq(&f, &f)` is true and `ptr::eq(&f, &g)` false —
// `fix_b_zst_ref_identity.rs`). trust-cg's frame layout honours a slot's `align`
// only up to the target stack alignment (16 bytes), so an OVER-ALIGNED referent
// got an address its own type says is invalid: measured 2026-09-10,
// `#[repr(align(64))] struct Z64;` printed `&z as usize % 64 == 48` where rustc
// prints `0` (review probe `adv_zst1_align.rs`). The bridge already refused an
// over-aligned NON-zero-sized local; this arm was quietly exempt. Now REFUSED
// by name at every opt level — expected: REFUSED, never a running binary.
#[repr(align(64))] struct Z64;
#[repr(align(32))] struct Z32;
#[inline(never)] fn al<T>(r: &T) -> usize { (r as *const T as usize) % std::mem::align_of::<T>() }
fn main() { let a = Z64; let b = Z32; println!("z64={} z32={}", al(&a), al(&b)); }
