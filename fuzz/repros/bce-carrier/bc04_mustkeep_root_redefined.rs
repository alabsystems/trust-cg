// BC04 MUST-KEEP: the IV is redefined (i += step) BETWEEN the guard and the
// access, so the guard's bound is stale at the access. The region
// no-redefinition scan must decline. i jumps by an opaque step, so i can pass
// the guard at 23 then access a[23+? ] — with step folded the access uses the
// UPDATED i. Both arms identical exit (trap or clean, but identical).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = [9u64; 24];
    let mut s: u64 = 0;
    let mut i = 0usize;
    let step = core::hint::black_box(3usize);
    while i < 24 {
        i += step;              // root redefined BEFORE the access
        if i >= 24 { break; }
        s = s.wrapping_add(a[i]);
    }
    ((s ^ 0x77) & 0xff) as i32
}
