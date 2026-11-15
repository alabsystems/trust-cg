#![no_std]
use core::ffi::CStr;
unsafe extern "C" { fn fat_event(value: u64); }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { unsafe { fat_event(1) } } }
#[repr(C)]
pub struct Header { pub head: u64, pub tail: [u8] }
#[unsafe(no_mangle)]
pub fn virtual_str(op: &dyn Fn(&str, u64, bool) -> u64, text: &str, seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(text, seed, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_slice(op: &mut dyn FnMut(&mut [u64], u64, bool) -> u64, data: &mut [u64], seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(data, seed, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_const(op: &dyn Fn(&str, u64, bool) -> u64, seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op("hello", seed, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_cstr(op: &dyn Fn(&CStr, u64, bool) -> u64, text: &CStr, seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(text, seed, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_raw(op: &dyn Fn(*const [u16], u64, bool) -> u64, data: *const [u16], seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(data, seed, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_split(op: &dyn Fn(u64,u64,u64,u64,u64,u64,&[u64],u64,bool)->u64, data: &[u64], seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(seed, seed+1, seed+2, seed+3, seed+4, seed+5, data, seed+6, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_zst(op: &dyn Fn(u64,(),&str,bool)->u64, text: &str, seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(seed, (), text, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_mixed(op: &dyn Fn(f64,u8,&str,&[u16],bool)->u64, text: &str, data: &[u16], seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(seed as f64 + 0.25, seed as u8, text, data, fail)
}
#[unsafe(no_mangle)]
pub fn virtual_dst(op: &dyn Fn(&Header,u64,bool)->u64, data: &Header, seed: u64, fail: bool) -> u64 {
    let _guard = Guard;
    op(data, seed, fail)
}
