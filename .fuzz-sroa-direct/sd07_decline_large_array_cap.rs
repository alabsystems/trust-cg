// SD07 DECLINE-FOR-SANITY (MUST-NOT-PROMOTE in practice): a 4KB stack array
// ([u32; 1024]) that is otherwise a legal-looking candidate (no address
// escape, includes constant-index accesses). Promoting 1024 lanes to virtual
// registers would explode regalloc/compile time, so any sane scalarization cap
// must DECLINE this slot; the program must still compile and produce the same
// checksum either way (and compile in bounded time).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u32 = 0;
    let mut rep: u32 = 0;
    while rep < 50 {
        let mut a = [0u32; 1024]; // 4KB — beyond any sane per-slot scalar cap
        let mut i = 0;
        while i < 1024 {
            a[i] = (i as u32).wrapping_mul(2654435761).wrapping_add(rep);
            i += 1;
        }
        // Constant-index accesses so the slot LOOKS like a candidate.
        a[0] = a[0].wrapping_add(a[1023]);
        a[512] = a[0] ^ a[256];
        let mut s: u32 = 0;
        let mut j = 0;
        while j < 1024 {
            s = s.wrapping_add(a[j]);
            j += 1;
        }
        acc = acc.wrapping_add(s).wrapping_add(a[512]);
        rep += 1;
    }
    (acc & 0xff) as i32
}
