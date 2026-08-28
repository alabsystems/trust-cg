// Result method chains: unwrap_or/map_or/ok/unwrap_or_else/is_ok over div-by-zero.
use std::hint::black_box as bb;
fn div(a: i64, b: i64) -> Result<i64, u32> { if b == 0 { Err(1) } else { Ok(a / b) } }
fn f() -> u64 {
    let mut acc = 0u64;
    for &(a, b) in [(bb(10i64), bb(2i64)), (bb(7), bb(0)), (bb(-9), bb(3))].iter() {
        let r = div(a, b);
        acc = acc.wrapping_add(r.unwrap_or(0) as u64);
        acc = acc.wrapping_add(r.map_or(5, |v| v as u64 & 0xff));
        acc = acc.wrapping_add(r.ok().unwrap_or(0) as u64);
        acc = acc.wrapping_add(r.unwrap_or_else(|e| e as i64) as u64);
        acc = acc.wrapping_add(r.is_ok() as u64 * 13);
    }
    acc
}
fn main() { std::process::exit((f() % 241) as i32); }
