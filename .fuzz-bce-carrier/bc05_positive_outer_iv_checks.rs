// BC05 POSITIVE (the outer-IV shape the diamond arm can never reach): nested
// loops where the INNER body accesses a[r][k] — r's check is proven by the
// OUTER loop guard several CFG levels up. The idom walk must climb past the
// inner header to find r's guard. Exit identical both arms.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
const N: usize = 8;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 3000 {
        let mut a = [[0i64; N]; N];
        let mut i = 0;
        while i < N { let mut j = 0; while j < N { a[i][j] = (i + j + rep as usize) as i64; j += 1; } i += 1; }
        let mut s: i64 = 0;
        let mut r = 0;
        while r < N {
            let mut k = 0;
            while k < N {
                s = s.wrapping_add(a[r][k]); // r proven by the OUTER guard
                k += 1;
            }
            r += 1;
        }
        acc = acc.wrapping_add(s as u64);
        rep += 1;
    }
    ((acc ^ 0x1b) & 0xff) as i32
}
