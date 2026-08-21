use std::hint::black_box as bb;
#[inline(never)] fn f(p0:u64,n:u64)->u64{ let mut s=0u64; let mut i=0u64;
  while i<n { s=s.wrapping_add(i^p0); if s>1000 { break; } i+=1; } s }
fn main(){ std::process::exit((f(bb(3),bb(5))%251) as i32); }
