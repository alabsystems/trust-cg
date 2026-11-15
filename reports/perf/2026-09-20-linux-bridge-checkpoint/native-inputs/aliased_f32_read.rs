#![no_std]
#[repr(C)] pub struct Inner{pub value:f32}
#[repr(C)] pub struct Outer{pub inner:Inner}
unsafe extern "C"{fn c_change(p:*mut Outer,value:f32);fn c_record(p:*mut Outer,tag:u32);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn aliased_f32_read(mut a:Outer,value:f32)->f32{unsafe{c_change(&raw mut a,value);}a.inner.value}
