// SD04 MUST-NOT-PROMOTE (or must preserve exact behavior): uninitialized-read
// SHAPE via MaybeUninit partial init. Lane 1 is stored and read only under an
// OPAQUE runtime condition (the compiler cannot prove the store dominates the
// read), and lanes 2..4 are NEVER stored at all. A promoter that fabricates a
// defined register value for a lane with no dominating store — or that
// reorders the conditional store/read — changes behavior. Actual execution
// never reads uninitialized memory (the condition is always true at runtime),
// so the program itself is UB-free and deterministic.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

use core::mem::MaybeUninit;

#[inline(never)]
fn opaque_true(x: u32) -> bool {
    // Always true at runtime, but behind an #[inline(never)] boundary.
    x.wrapping_mul(2) % 2 == 0
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u32 = 0;
    let mut rep: u32 = 0;
    while rep < 4_000 {
        let mut a: [MaybeUninit<u32>; 4] = [MaybeUninit::uninit(); 4];
        let cond = opaque_true(rep);
        // Unconditional constant-index init of lane 0 only.
        a[0] = MaybeUninit::new(rep.wrapping_mul(7).wrapping_add(3));
        // Conditional constant-index init of lane 1 (read is guarded by the
        // SAME condition below). Lanes 2 and 3 are never stored.
        if cond {
            a[1] = MaybeUninit::new(rep ^ 0x99);
        }
        let mut v = unsafe { a[0].assume_init() };
        if cond {
            v = v.wrapping_add(unsafe { a[1].assume_init() });
        }
        acc = acc.wrapping_add(v);
        rep += 1;
    }
    (acc & 0x7f) as i32
}
