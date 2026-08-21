use std::hint::black_box as bb;
fn main() { let n = bb(64usize); let mut b = vec![0u16; 128]; let v = bb(1234u16);
    let mut i = 0usize; while i < n { b[i] = v; i += 1; }
    let s: u64 = b.iter().map(|&x| x as u64).sum();
    std::process::exit((s % 126) as i32); }
