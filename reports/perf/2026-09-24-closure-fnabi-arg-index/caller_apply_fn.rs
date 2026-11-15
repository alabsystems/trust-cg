use std::hint::black_box;
fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }
fn main() { let n = black_box(30u32); let m = black_box(4u64); let v = if n % 2 == 0 { Some(n as u8) } else { None };
 let g = |o: Option<u8>, k: u32| match o { Some(x) => x as u64 * m + k as u64, None => 700 + k as u64 + m };
 exit(calleearg::apply_fn(v, &g, black_box(2))) }
