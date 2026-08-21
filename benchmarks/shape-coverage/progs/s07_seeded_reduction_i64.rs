use std::hint::black_box as bb;
fn main() { let n = bb(200u64); let seed = bb(999_777u64);
    let mut acc: u64 = seed; let mut i = 0u64;
    while i < n { acc = acc.wrapping_add(i.wrapping_mul(11)); i += 1; }
    std::process::exit((acc % 126) as i32); }
