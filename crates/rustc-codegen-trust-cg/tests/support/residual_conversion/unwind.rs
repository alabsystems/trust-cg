#![no_std]
unsafe extern "C" {
    fn residual_event(kind: u64, value: u64);
}
unsafe extern "C-unwind" {
    fn residual_may_panic(value: u64);
}
struct Input(u64);
impl Drop for Input {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { residual_event(3, self.0) }
    }
}
struct Guard(u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { residual_event(self.0, 0) }
    }
}
struct Final(u64);
impl From<Input> for Final {
    #[inline(never)]
    fn from(value: Input) -> Self {
        let _guard = Guard(4);
        unsafe {
            residual_event(1, value.0);
            residual_may_panic(value.0);
            residual_event(2, value.0);
        }
        Final(value.0 ^ 0x4321)
    }
}
#[inline(never)]
fn inner(v: u64, fail: bool) -> Result<u64, Input> {
    if fail { Err(Input(v)) } else { Ok(v) }
}
#[inline(never)]
fn outer(v: u64, fail: bool) -> Result<u64, Final> {
    let _guard = Guard(9);
    let v = inner(v, fail)?;
    Ok(v ^ 123)
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn residual_unwind(v: u64, fail: bool) -> u64 {
    match outer(v, fail) {
        Ok(n) => n,
        Err(Final(e)) => e,
    }
}
