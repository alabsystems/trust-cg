#![no_std]
#[repr(C)] pub struct Inner {pub value:f64}
#[repr(C)] pub struct Outer {pub inner:Inner}
unsafe extern "C" {fn c_change(p:*mut Outer,value:f64);fn c_change_leaf(p:*mut f64,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn projected_borrow(mut a:Outer,value:f64)->f64{unsafe{c_change(&raw mut a,value);c_change_leaf(&mut a.inner.value,value);}a.inner.value}
