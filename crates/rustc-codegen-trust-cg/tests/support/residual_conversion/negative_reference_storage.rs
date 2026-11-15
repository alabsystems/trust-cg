#[repr(transparent)]
pub struct DropValue(u64);
impl Drop for DropValue {
    fn drop(&mut self) {}
}
unsafe extern "C" {
    fn identity(a: &DropValue, b: &DropValue) -> bool;
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn unsupported_drop_referent(x: u64) -> bool {
    let x = DropValue(x);
    let r = &x;
    unsafe { identity(r, r) }
}
