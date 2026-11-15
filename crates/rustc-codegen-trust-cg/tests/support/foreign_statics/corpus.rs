#![no_std]
#![feature(linkage)]

unsafe extern "C" {
    static foreign_value: u64;
    static mut foreign_mutable: u64;
    #[linkage = "extern_weak"]
    static optional_function: Option<unsafe extern "C" fn(u64) -> u64>;
    #[linkage = "extern_weak"]
    static optional_data: *const u64;
    #[linkage = "extern_weak"]
    static optional_mutable: *mut u64;
}
static SAVED_FOREIGN: &u64 = unsafe { &foreign_value };
static SAVED_WEAK: &Option<unsafe extern "C" fn(u64) -> u64> = unsafe { &optional_function };

#[unsafe(no_mangle)]
pub extern "C" fn strong_read() -> u64 {
    unsafe { foreign_value.wrapping_mul(37) ^ *SAVED_FOREIGN }
}
#[unsafe(no_mangle)]
pub extern "C" fn strong_write(value: u64) -> u64 {
    unsafe {
        foreign_mutable = value;
        foreign_mutable
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn weak_read(value: u64) -> u64 {
    let f = unsafe { optional_function };
    let result = match f {
        Some(f) => unsafe { f(value) },
        None => value.wrapping_add(17),
    };
    let ptr = unsafe { optional_data };
    result
        ^ if ptr.is_null() {
            0x88776655
        } else {
            unsafe { *ptr }
        }
}
#[unsafe(no_mangle)]
pub extern "C" fn weak_address_direct() -> usize {
    core::ptr::addr_of!(optional_function) as usize
}
#[unsafe(no_mangle)]
pub extern "C" fn weak_address_saved() -> usize {
    SAVED_WEAK as *const _ as usize
}
#[unsafe(no_mangle)]
pub extern "C" fn weak_mutable_set(value: u64) {
    let ptr = unsafe { optional_mutable };
    if !ptr.is_null() {
        unsafe {
            *ptr = value;
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn weak_mutable_get() -> u64 {
    let ptr = unsafe { optional_mutable };
    if ptr.is_null() {
        0x13579bdf
    } else {
        unsafe { *ptr }
    }
}
