use std::hint::black_box as bb;
#[inline(never)] fn f(p0:u64,n:u64)->u64{ let mut x=1u64; let mut y=2u64; let mut i=0u64;
  while i<n { let t=x.wrapping_add(y^p0); x=y; y=t; i+=1; } y }
fn main(){ std::process::exit((f(bb(3),bb(5))%251) as i32); }
