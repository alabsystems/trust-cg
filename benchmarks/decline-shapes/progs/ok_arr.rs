use std::hint::black_box as bb;
#[inline(never)] fn f(p0:u64,n:u64)->u64{ let a=[1u64,2,3,4]; let mut s=0u64; let mut i=0usize;
  while i<n as usize { s=s.wrapping_add(a[i%4]^p0); i+=1; } s }
fn main(){ std::process::exit((f(bb(3),bb(5))%251) as i32); }
