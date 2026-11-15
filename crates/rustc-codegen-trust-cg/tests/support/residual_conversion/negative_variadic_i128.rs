unsafe extern "C" {
    fn variadic_sink(tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rejected(a: i128) -> u64 {
    unsafe { variadic_sink(1, a) }
}
