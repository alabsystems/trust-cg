unsafe extern "C-unwind" {
    fn variadic_callback(callback: unsafe extern "C-unwind" fn(u64) -> u64, tag: u32, ...) -> u64;
}
struct Guard(*mut u64);
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { *self.0 += 1 };
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn invoke_variadic(
    callback: unsafe extern "C-unwind" fn(u64) -> u64,
    value: u64,
    drops: *mut u64,
) -> u64 {
    let _guard = Guard(drops);
    unsafe { variadic_callback(callback, 23, value) }
}
