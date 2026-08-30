// SD01 POSITIVE: small stack array ([u32; 4]) with ONLY constant-index reads
// and writes, every lane stored before it is read, address never taken, inside
// a hot repeat loop. This is the exact shape the x86_sroa direct-[StackSlot+disp]
// promotion extension SHOULD promote to registers; the checksum must be
// identical with the pass ON vs OFF.
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
    while rep < 10_000 {
        let mut a: [u32; 4] = [0; 4];
        // Constant displacements only: [slot+0], [slot+4], [slot+8], [slot+12].
        a[0] = rep.wrapping_mul(3).wrapping_add(1);
        a[1] = a[0].wrapping_add(7);
        a[2] = a[1] ^ 0x55;
        a[3] = a[2].wrapping_mul(5);
        a[1] = a[3].wrapping_sub(a[0]); // re-store a lane after reading it
        acc = acc
            .wrapping_add(a[0])
            .wrapping_add(a[1])
            .wrapping_add(a[2])
            .wrapping_add(a[3]);
        rep += 1;
    }
    (acc & 0xff) as i32
}
