#![no_std]
#[repr(C,align(16))] pub struct Bad {pub value:f64}
unsafe extern "C" {fn c_change(p:*mut Bad,value:f64);}
#[unsafe(no_mangle)] pub unsafe extern "C" fn overaligned_cell(value:f64)->f64{let mut b=Bad{value:-21.5};unsafe{c_change(&raw mut b,value);}b.value}
