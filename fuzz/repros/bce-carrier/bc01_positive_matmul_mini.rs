// BC01 POSITIVE: mini-matmul with constant-bound loops — every bounds check is
// dominated by its loop guard (i<6, j<6, k<6 over [[i64;6];6]). The carrier arm
// SHOULD eliminate all checks; exit code must be identical arm-on vs arm-off.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
const N: usize = 6;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 2000 {
        let mut a = [[0i64; N]; N];
        let mut i = 0;
        while i < N {
            let mut j = 0;
            while j < N { a[i][j] = (i * 3 + j + rep as usize) as i64 % 11; j += 1; }
            i += 1;
        }
        let mut s: i64 = 0;
        let mut r = 0;
        while r < N {
            let mut k = 0;
            while k < N { s = s.wrapping_add(a[r][k].wrapping_mul(a[k][r])); k += 1; }
            r += 1;
        }
        acc = acc.wrapping_add(s as u64);
        rep += 1;
    }
    ((acc ^ 0x3c) & 0xff) as i32
}
