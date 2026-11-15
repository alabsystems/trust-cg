unsafe extern "C" {
    fn variadic_write(tag: u32, ...) -> u64;
    fn variadic_ref(p: &mut u64, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_write(x: u64) -> u64 {
    let mut value = x;
    let r = unsafe { variadic_write(11, &raw mut value, x.rotate_left(17)) };
    value ^ r
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn call_ref(p: &mut u64, x: u64) -> u64 {
    let r = unsafe { variadic_ref(p, x) };
    *p ^ r
}
