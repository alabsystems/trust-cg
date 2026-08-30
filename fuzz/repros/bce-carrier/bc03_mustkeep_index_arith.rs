// BC03 MUST-KEEP: the accessed index is i*2 (an ImulRRI/shift def, NOT a plain
// copy of the guarded IV), so the canon chain rule must decline; the check must
// stay and fire when i*2 >= 24 (at i==12). Identical trapping exit both arms.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = [3u64; 24];
    let mut s: u64 = 0;
    let mut i = 0usize;
    let bound = core::hint::black_box(24usize);
    while i < bound {
        s = s.wrapping_add(a[i * 2]); // traps at i==12
        i += 1;
    }
    ((s ^ 0x66) & 0xff) as i32
}
