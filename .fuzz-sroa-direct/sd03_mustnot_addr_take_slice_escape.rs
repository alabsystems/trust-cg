// SD03 MUST-NOT-PROMOTE: address-take mix. The SAME array is (a) accessed with
// constant indices — the promotable-looking shape — AND (b) passed by &slice
// (fat pointer) to an #[inline(never)] function, so its address genuinely
// escapes. If the pass promotes the constant-index lanes to registers, the
// callee reads a stale/garbage slot and the post-call constant-index write is
// lost to any later address-based reader. The escape must disqualify the slot.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[inline(never)]
fn sum_slice(s: &[u32]) -> u32 {
    let mut t: u32 = 0;
    let mut i = 0;
    while i < s.len() {
        t = t.wrapping_add(s[i]);
        i += 1;
    }
    t
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u32 = 0;
    let mut rep: u32 = 0;
    while rep < 5_000 {
        let mut a: [u32; 4] = [0; 4];
        // Constant-index writes (the bait).
        a[0] = rep;
        a[1] = rep ^ 0xa5;
        a[2] = a[0].wrapping_add(a[1]);
        a[3] = a[2].wrapping_mul(3);
        // Address escapes as a fat-pointer slice into an opaque callee: the
        // callee MUST observe the four stores above through memory.
        let s = sum_slice(&a);
        // Constant-index write AFTER the escape, then another escape: the
        // second call MUST observe this store too.
        a[2] = s.wrapping_add(a[3]);
        let s2 = sum_slice(&a[1..4]);
        acc = acc.wrapping_add(s).wrapping_add(s2).wrapping_add(a[2]);
        rep += 1;
    }
    (acc & 0xff) as i32
}
