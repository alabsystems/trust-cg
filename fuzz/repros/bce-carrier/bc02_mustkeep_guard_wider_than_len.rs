// BC02 MUST-KEEP: the loop guard bound (32) is WIDER than the array length
// (24), so the bounds check is NOT redundant — it must fire at i==24. The
// implication check (K'=32 <= K=24 is FALSE) must decline; if the arm wrongly
// eliminates, the program silently reads OOB instead of trapping and the exit
// code changes. Both arms must produce the IDENTICAL (trapping) exit.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = [7u64; 24];
    let mut s: u64 = 0;
    let mut i = 0usize;
    // volatile-ish opaque bound so the compiler can't fold the trap statically
    let bound = core::hint::black_box(32usize);
    while i < bound {
        s = s.wrapping_add(a[i]); // traps at i==24
        i += 1;
    }
    ((s ^ 0x55) & 0xff) as i32
}
