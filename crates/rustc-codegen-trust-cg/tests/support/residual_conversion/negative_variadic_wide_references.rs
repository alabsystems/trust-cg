unsafe extern "C" {
    fn ref_sink(tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe fn rejected_slice(x: &[u8]) -> u64 {
    unsafe { ref_sink(0, x) }
}
#[unsafe(no_mangle)]
pub unsafe fn rejected_str(x: &str) -> u64 {
    unsafe { ref_sink(0, x) }
}
#[unsafe(no_mangle)]
pub unsafe fn rejected_dyn(x: &dyn core::fmt::Debug) -> u64 {
    unsafe { ref_sink(0, x) }
}
#[unsafe(no_mangle)]
pub unsafe fn rejected_raw_slice(x: *const [u8]) -> u64 {
    unsafe { ref_sink(0, x) }
}
