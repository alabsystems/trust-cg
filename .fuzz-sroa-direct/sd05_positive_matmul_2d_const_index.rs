// SD05 POSITIVE: mini 2D-array matmul (2x2, u32) with FULLY CONSTANT indices —
// three small [[u32; 2]; 2] locals whose every access is [StackSlot + const
// disp], no address taken, every lane stored before read. This is the b05_matmul
// shape in miniature; the direct-[StackSlot+disp] promotion SHOULD promote all
// three arrays to registers. Checksum must be identical ON vs OFF.
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
    while rep < 8_000 {
        let mut a = [[0u32; 2]; 2];
        let mut b = [[0u32; 2]; 2];
        let mut c = [[0u32; 2]; 2];
        a[0][0] = rep;
        a[0][1] = rep ^ 3;
        a[1][0] = rep.wrapping_mul(5);
        a[1][1] = rep.wrapping_add(9);
        b[0][0] = rep ^ 7;
        b[0][1] = rep.wrapping_mul(3);
        b[1][0] = rep.wrapping_add(11);
        b[1][1] = rep ^ 13;
        // c = a * b, hand-unrolled: constant displacements only.
        c[0][0] = a[0][0].wrapping_mul(b[0][0]).wrapping_add(a[0][1].wrapping_mul(b[1][0]));
        c[0][1] = a[0][0].wrapping_mul(b[0][1]).wrapping_add(a[0][1].wrapping_mul(b[1][1]));
        c[1][0] = a[1][0].wrapping_mul(b[0][0]).wrapping_add(a[1][1].wrapping_mul(b[1][0]));
        c[1][1] = a[1][0].wrapping_mul(b[0][1]).wrapping_add(a[1][1].wrapping_mul(b[1][1]));
        acc = acc
            .wrapping_add(c[0][0])
            .wrapping_add(c[0][1] ^ c[1][0])
            .wrapping_add(c[1][1]);
        rep += 1;
    }
    (acc & 0xff) as i32
}
