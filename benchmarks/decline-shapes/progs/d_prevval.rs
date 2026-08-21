use std::hint::black_box as bb;
#[inline(never)] fn f(p0:u64,n:u64)->u64{ let mut a=0u64; let mut prev=0u64; let mut i=0u64;
  while i<n { let t=i.wrapping_mul(p0); a=a.wrapping_add(prev); prev=t; i+=1; } a }
fn main(){ std::process::exit((f(bb(3),bb(5))%251) as i32); }
