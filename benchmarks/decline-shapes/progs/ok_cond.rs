use std::hint::black_box as bb;
#[inline(never)] fn f(p0:u64,n:u64)->u64{ let mut a=0u64; let mut i=0u64;
  while i<n { if i&1==0 { a = i.wrapping_add(p0); } i+=1; } a }
fn main(){ std::process::exit((f(bb(3),bb(5))%251) as i32); }
