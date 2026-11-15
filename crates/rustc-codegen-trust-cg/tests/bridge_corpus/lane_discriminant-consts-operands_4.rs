// CORPUS FIXTURE — lane discriminant-consts-operands: the previously refused
// intrinsics that core reaches — `exact_div` (`<[T]>::as_chunks_unchecked`),
// `arith_offset` (`<*const T>::wrapping_offset`, negative and positive counts,
// multi-byte elements), `select_unpredictable` (`hint::select_unpredictable`,
// lowered through the intrinsic's own fallback MIR body), and `abort_immediate` (behind a
// runtime-false guard so the program still runs — only its lowering is tested).
#![feature(core_intrinsics, slice_as_chunks)]
#![allow(internal_features)]
#[inline(never)]
fn chunk_fold(s: &[u32]) -> u64 {
    let chunks: &[[u32; 4]] = unsafe { s.as_chunks_unchecked::<4>() };
    let mut acc = 0u64;
    let mut i = 0;
    while i < chunks.len() {
        let c = &chunks[i];
        acc = acc * 100 + (c[0] + c[1] + c[2] + c[3]) as u64;
        i += 1;
    }
    acc
}
#[inline(never)]
fn walk(base: *const u64, steps: &[isize]) -> u64 {
    let mut acc = 0u64;
    let mut i = 0;
    while i < steps.len() {
        let p = base.wrapping_offset(steps[i]);
        acc = acc.wrapping_mul(31).wrapping_add(unsafe { *p });
        i += 1;
    }
    acc
}
#[inline(never)]
fn pick(c: bool, a: u64, b: u64) -> u64 { core::hint::select_unpredictable(c, a, b) }
#[inline(never)]
fn guarded(v: u32) -> u32 {
    if v == 0xdead_beef { core::intrinsics::abort_immediate(); }
    v + 1
}
fn main() {
    let data = [1u32, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    println!("chunks {}", chunk_fold(&data));
    let arr: [u64; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
    let steps: [isize; 6] = [1, -3, 2, 3, -1, -4];
    println!("walk {}", walk(arr.as_ptr().wrapping_add(4), &steps));
    println!("pick {} {}", pick(true, 111, 222), pick(false, 111, 222));
    println!("guarded {}", guarded(41));
}
