#[repr(C)]
struct Record {
    a: u64,
    b: u64,
    out: *mut u64,
}
impl Drop for Record {
    fn drop(&mut self) {
        unsafe {
            *self.out = (self.a ^ self.b).rotate_left(9);
            *self.out.add(1) += 1;
        }
    }
}
unsafe extern "C-unwind" {
    fn reference_callback(cb: unsafe extern "C-unwind" fn(u64) -> u64, tag: u32, ...) -> u64;
}
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn write_then_unwind(
    cb: unsafe extern "C-unwind" fn(u64) -> u64,
    a: u64,
    b: u64,
    x: u64,
    out: *mut u64,
) -> u64 {
    let mut value = Record { a, b, out };
    let result = unsafe { reference_callback(cb, 41, &mut value, x) };
    value.a ^ value.b ^ result
}
