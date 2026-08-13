// CORPUS FIXTURE — bug #71: loop-carried scalarized aggregate field.
// `q.a += 1` inside a loop. The bridge scalarizes the struct into per-field SSA
// values; the bug dropped the header phi for a PROJECTED field (q.a), so q.a/q.b
// stayed at their entry value while plain scalars z1/z2 updated correctly.
// Correct exit: (10 + 20 + 10 + 20) & 0xff = 60.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
struct Q { a: i64, b: i64 }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut q = Q { a: black_box(0), b: black_box(0) };
    let mut z1: i64 = black_box(0);
    let mut z2: i64 = black_box(0);
    let mut i: i64 = 0;
    while i < black_box(10) {
        q.a += 1;
        q.b += 2;
        z1 += 1;
        z2 += 2;
        i += 1;
    }
    ((q.a + q.b + z1 + z2) & 0xff) as i32
}
