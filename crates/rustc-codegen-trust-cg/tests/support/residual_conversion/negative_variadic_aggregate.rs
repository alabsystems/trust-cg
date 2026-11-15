#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
unsafe extern "C" {
    fn variadic_sink(tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rejected(a: u64, b: u64) -> u64 {
    unsafe { variadic_sink(1, Pair { a, b }) }
}
