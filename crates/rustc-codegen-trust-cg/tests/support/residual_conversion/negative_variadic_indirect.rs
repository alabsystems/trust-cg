#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_pointer(
    f: unsafe extern "C" fn(u32, ...) -> u64,
    a: u64,
    b: u64,
) -> u64 {
    unsafe { f(2, a, b) }
}
