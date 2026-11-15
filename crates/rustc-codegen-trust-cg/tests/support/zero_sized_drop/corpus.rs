#![no_std]
unsafe extern "C-unwind" {
    fn maybe_panic(item: u64, enabled: u64);
}
unsafe extern "C" {
    fn note_address(kind: u64, address: usize);
}
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe {
            note_address(2, self as *mut Self as usize);
        }
    }
}
#[repr(align(8))]
struct Aligned;
impl Drop for Aligned {
    fn drop(&mut self) {
        unsafe {
            note_address(4, self as *mut Self as usize);
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn zst_scope(enabled: u64) -> u64 {
    let guard = Guard;
    unsafe {
        note_address(1, &guard as *const Guard as usize);
    }
    {
        let aligned = Aligned;
        unsafe {
            note_address(3, &aligned as *const Aligned as usize);
            maybe_panic(2, enabled);
        }
    }
    77
}
#[inline(never)]
fn take(_guard: Guard) {}
#[unsafe(no_mangle)]
pub extern "C" fn zst_by_value() {
    take(Guard);
    core::mem::drop(Guard);
    take(Guard);
}
#[unsafe(no_mangle)]
pub extern "C" fn zst_loop(count: u32) -> u64 {
    let mut i = 0;
    while i < count {
        let guard = Guard;
        unsafe {
            note_address(1, &guard as *const Guard as usize);
        }
        i += 1;
    }
    u64::from(i)
}

#[repr(align(16))]
struct Bare;
#[unsafe(no_mangle)]
pub extern "C" fn zst_raw_local() -> u64 {
    let mut value = Bare;
    let first = &raw const value as usize;
    let second = &raw mut value as usize;
    unsafe {
        note_address(5, first);
        note_address(6, second);
    }
    core::mem::align_of::<Bare>() as u64
}
