#![no_std]
#[repr(C)] pub struct Hfa {pub x:f64,pub y:f64}
#[repr(C)] pub struct Pair {pub x:u64,pub y:u64}
#[unsafe(no_mangle)] pub unsafe extern "C" fn mixed_return(f:unsafe extern "C" fn(Hfa)->Pair,a:Hfa,out:*mut u64){let p=unsafe{f(a)};unsafe{*out=p.x;*out.add(1)=p.y;}}
