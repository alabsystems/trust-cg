// float->narrow-int `as` MUST saturate to the narrow range (regression for the
// P0 fixed in f243d837: fcvtzs/fcvtzu was 64-bit-saturating then truncating).
// Every value below is OUT of the narrow range (or NaN) so the saturating
// clamp is exercised; the accumulator folds the full results so any wrong
// clamp changes the exit code.
use std::hint::black_box as bb;
fn main() {
    let f64s: [f64; 8] = [bb(1e300), bb(-1e300), bb(f64::NAN), bb(f64::INFINITY),
                          bb(f64::NEG_INFINITY), bb(300.0), bb(5e9), bb(-5.0)];
    let f32s: [f32; 5] = [bb(1e30), bb(-1e30), bb(70000.0), bb(40000.0), bb(-1.0)];
    let mut acc: u64 = 0;
    for &f in f64s.iter() {
        acc = acc.wrapping_add(f as i8 as u8 as u64);
        acc = acc.wrapping_add(f as i16 as u16 as u64).wrapping_mul(3);
        acc = acc.wrapping_add(f as i32 as u32 as u64).wrapping_add(7);
        acc = acc.wrapping_add(f as u8 as u64);
        acc = acc.wrapping_add(f as u16 as u64).wrapping_mul(5);
        acc = acc.wrapping_add(f as u32 as u64);
    }
    for &f in f32s.iter() {
        acc = acc.wrapping_add(f as i32 as u32 as u64).wrapping_add(f as u32 as u64);
        acc = acc.wrapping_add(f as i16 as u16 as u64).wrapping_add(f as u8 as u64);
    }
    std::process::exit((acc % 251) as i32);
}
