// neon_bitrev: a SECOND loop-carried value beside the induction variable.
use std::hint::black_box as bb;
fn main() { let n = bb(64usize); let mut a=[0u8;64];
    for i in 0..64 { a[i]=(i as u8).wrapping_mul(37).wrapping_add(11); }
    let a = bb(a); let mut out=[0u8;64]; let mut acc: u32 = 0; let mut i=0usize;
    while i < n { out[i]=a[i].reverse_bits(); acc=acc.wrapping_add(out[i] as u32); i+=1; }
    let s: u32 = out.iter().map(|&x| x as u32).sum::<u32>().wrapping_add(acc);
    std::process::exit((s % 126) as i32); }
