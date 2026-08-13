// SD06 MUST-NOT-PROMOTE: raw-pointer ALIASED write. The array has
// constant-index reads/writes (the promotable-looking shape), but a raw
// pointer obtained via as_mut_ptr() plus RUNTIME pointer arithmetic
// (p.add(pick(rep))) stores into an unpredictable lane each iteration. A
// promoter that keeps lanes in registers misses the aliased store (the u32
// written through p lands in a dead stack slot / is lost), corrupting the sum.
// pick() is always in 0..4 so every access is in-bounds and defined.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// Satisfies the _rust_eh_personality reference a libcore CGU's eh_frame keeps
// at -Copt-level=0 under plain rustc; never called (panic=abort).
#[no_mangle]
extern "C" fn rust_eh_personality() {}

#[inline(never)]
fn pick(i: u32) -> usize {
    (i as usize) & 3
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u32 = 0;
    let mut rep: u32 = 0;
    while rep < 5_000 {
        let mut a: [u32; 4] = [1, 2, 3, 4];
        // Constant-index writes (the bait)...
        a[0] = rep;
        a[3] = rep ^ 0x77;
        // ...then a raw-pointer-arithmetic store into a runtime lane that
        // aliases the constant-index lanes.
        let p = a.as_mut_ptr();
        unsafe {
            *p.add(pick(rep)) = rep.wrapping_mul(13).wrapping_add(1);
        }
        // Constant-index reads MUST observe the aliased store.
        acc = acc
            .wrapping_add(a[0])
            .wrapping_add(a[1])
            .wrapping_add(a[2])
            .wrapping_add(a[3]);
        rep += 1;
    }
    (acc & 0xff) as i32
}
