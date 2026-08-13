// SD02 MUST-NOT-PROMOTE: overlapping MIXED-WIDTH access to the same bytes of a
// stack array. A u64 lane is stored whole, then its low/high u32 halves are
// read through a raw-pointer cast; a u32 is stored into the LOW HALF of another
// u64 lane which is then read whole. Lane-granular scalarization that models
// the slot as independent u64 registers would lose the sub-word overlap
// (partial-write merge + half reads), so the pass must refuse this slot.
// All accesses are in-bounds and alignment-safe (u64 lane align 8 >= u32's 4);
// x86_64 little-endian makes the halves deterministic.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u64 = 0;
    while rep < 4_000 {
        let mut a: [u64; 2] = [0; 2];
        // Whole-lane u64 store...
        a[0] = rep.wrapping_mul(0x0123_4567_89ab_cdef);
        // ...then u32 reads of its two halves via raw ptr (same bytes, narrower).
        let lo = unsafe { (&a[0] as *const u64 as *const u32).read() } as u64;
        let hi = unsafe { (&a[0] as *const u64 as *const u32).add(1).read() } as u64;
        // u32 store into the LOW HALF of a[1] (partial-lane write)...
        unsafe { (&mut a[1] as *mut u64 as *mut u32).write(0xdead_beef ^ (rep as u32)) };
        // ...then read the whole u64 lane back (high half must still be 0).
        acc = acc.wrapping_add(lo ^ hi).wrapping_add(a[1]);
        rep += 1;
    }
    ((acc ^ (acc >> 8) ^ (acc >> 32)) & 0xff) as i32
}
