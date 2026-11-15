unsafe extern "C" {
    fn variadic_words(count: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_constant_empty() -> u64 {
    let f: unsafe extern "C" fn(u32, ...) -> u64 = variadic_words;
    unsafe { f(0) }
}
