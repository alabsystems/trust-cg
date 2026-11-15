// CORPUS FIXTURE (companion of `stale_celled_entry_arg.rs`: the shapes that
// failed closed before the fix, kept apart so a refusal cannot mask a wrong
// value there) — a local or ENTRY ARGUMENT whose address escapes (`&mut p` through a
// returned alias) and is written through it (`*identity(&mut p) = q`) before a
// later read of `p` / `(*p).f`. The argument is CELLED; its live value is only in
// the cell. Before: every deref-base read took the INCOMING parameter
// (`value_for_scalar_binding`'s entry-arg fallback), so `p.b` read s1.b instead of
// s2.b — a SILENT wrong value at O0 (11 / 13 instead of 21 / 23). Each statement
// now loads the celled locals it reads from their cells (`preload_celled_reads`).
// Correct exit = LLVM oracle (32 at O0/O2/O3).
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
pub struct S { a: u64, b: u64 }
#[inline(never)]
fn local_copy<'a>(p0: &'a S, q: &'a S) -> u64 {
    let mut p = p0;
    let pp: &mut &'a S = core::convert::identity(&mut p);
    *pp = q;
    p.a + p.b
}
#[inline(never)]
fn scalar_arg(mut x: u64, y: u64) -> u64 {
    *core::convert::identity(&mut x) = y;
    x * 2
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let s1 = black_box(S { a: 1, b: 10 });
    let s2 = black_box(S { a: 2, b: 20 });
    let acc = local_copy(&s1, &s2) + scalar_arg(black_box(3), black_box(5));
    (acc % 251) as i32
}
