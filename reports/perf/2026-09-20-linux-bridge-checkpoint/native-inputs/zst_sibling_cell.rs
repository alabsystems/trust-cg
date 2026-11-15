#![no_std]
#[repr(C)] pub struct WithZst {pub value:f64,pub z:()}
unsafe extern "C" {fn c_change(p:*mut WithZst,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn zst_sibling_cell(value:f64)->f64{let mut b=WithZst{value:-21.5,z:()};unsafe{c_change(&raw mut b,value);}b.value}
