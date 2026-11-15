use std::hint::black_box;
fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }
fn main() { let n = black_box(30u32); let v = if n % 2 == 0 { Some(n as u8) } else { None };
 exit(calleearg::apply_once(v, |o, k| match o { Some(x) => x as u64 * 5 + k as u64, None => 800 + k as u64 }, black_box(2))) }
