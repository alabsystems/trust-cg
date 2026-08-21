// strided_store_unroll / mac_row_unroll: store NOT on every path.
use std::hint::black_box as bb;
fn main() { let n = bb(64usize); let mut buf = vec![0u64; 512]; let f = bb(true);
    let mut i = 0usize;
    while i < n { if f && (i % 3 != 0) { buf[i*4] = (i as u64).wrapping_mul(7); } i += 1; }
    let s: u64 = buf.iter().fold(0u64,|a,&b| a.wrapping_add(b));
    std::process::exit((s % 126) as i32); }
