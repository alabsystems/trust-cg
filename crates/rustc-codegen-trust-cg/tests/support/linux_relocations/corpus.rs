#![no_std]
#![feature(thread_local)]
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn exported_function(x: u64) -> u64 {
    x.wrapping_mul(19).wrapping_add(7)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn function_address() -> extern "C" fn(u64) -> u64 {
    exported_function
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn direct_call(x: u64) -> u64 {
    exported_function(x)
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn own_address() -> usize {
    own_address as *const () as usize
}
#[repr(C)]
pub struct Triple {
    pub address: usize,
    pub a: u64,
    pub b: u64,
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn own_triple(x: u64) -> Triple {
    Triple {
        address: own_triple as *const () as usize,
        a: x,
        b: x ^ 0xabcdef0123456789,
    }
}
#[unsafe(no_mangle)]
pub static EXPORTED_DATA: u64 = 0x123456789abcdef;
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn data_address() -> *const u64 {
    &EXPORTED_DATA
}
#[thread_local]
static mut THREAD_VALUE: u64 = 0x987654321;
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn tls_replace(x: u64) -> u64 {
    unsafe {
        let old = THREAD_VALUE;
        THREAD_VALUE = x;
        old
    }
}
#[inline(never)]
extern "C" fn hidden_callback(x: u64) -> u64 {
    x.rotate_left(13) ^ 0xaabbccdd
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn hidden_address() -> extern "C" fn(u64) -> u64 {
    hidden_callback
}
