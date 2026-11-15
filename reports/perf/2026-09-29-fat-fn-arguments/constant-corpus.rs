#![no_std]
unsafe extern "C" { fn fat_event(value:u64); }
struct Guard;
impl Drop for Guard { fn drop(&mut self) { unsafe {fat_event(1);} } }
#[unsafe(no_mangle)]
pub fn virtual_all_const(op:&dyn Fn(&str,u64,bool)->u64)->u64 {
 let _g=Guard;
 op("literal",91,false)
}
#[unsafe(no_mangle)]
pub fn virtual_all_cstr(op:&dyn Fn(&core::ffi::CStr,u64,bool)->u64)->u64 {
 let _g=Guard;
 op(c"abc",71,false)
}
