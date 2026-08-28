// narrow signed div/rem OVERFLOW: iN::MIN / -1 wraps to iN::MIN (rem 0) for
// i8/i16/i32 — the LLVM-UB case Rust guards; must match the wrapping result.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    // i8
    let a8: [i8; 4] = [bb(i8::MIN), bb(-1), bb(i8::MAX), bb(-50)];
    let b8: [i8; 3] = [bb(-1), bb(3), bb(-7)];
    for &x in a8.iter() { for &y in b8.iter() {
        acc = acc.wrapping_add(x.wrapping_div(y) as u8 as u64).wrapping_add(x.wrapping_rem(y) as u8 as u64);
    }}
    // i16
    let a16: [i16; 4] = [bb(i16::MIN), bb(-1), bb(i16::MAX), bb(-1000)];
    let b16: [i16; 3] = [bb(-1), bb(100), bb(-13)];
    for &x in a16.iter() { for &y in b16.iter() {
        acc = acc.wrapping_add(x.wrapping_div(y) as u16 as u64).wrapping_add(x.wrapping_rem(y) as u16 as u64);
    }}
    // i32
    let a32: [i32; 4] = [bb(i32::MIN), bb(-1), bb(i32::MAX), bb(-1000000)];
    let b32: [i32; 3] = [bb(-1), bb(7919), bb(-104729)];
    for &x in a32.iter() { for &y in b32.iter() {
        acc = acc.wrapping_add(x.wrapping_div(y) as u32 as u64).wrapping_add(x.wrapping_rem(y) as u32 as u64);
    }}
    std::process::exit((acc % 251) as i32);
}
