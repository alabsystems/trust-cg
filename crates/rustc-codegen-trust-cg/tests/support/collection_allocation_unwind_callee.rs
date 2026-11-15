unsafe extern "C" {
    fn mark_drop();
    fn record_buffer(pointer: usize);
}
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { mark_drop() }
    }
}
#[inline(never)]
pub fn f(method: u8, n: usize) -> Vec<u64> {
    let _guard = Guard;
    if method == 0 {
        let v = Vec::with_capacity(n);
        unsafe { record_buffer(v.as_ptr() as usize) };
        v
    } else {
        let mut v = Vec::with_capacity(4);
        v.push(7);
        unsafe { record_buffer(v.as_ptr() as usize) };
        if method == 1 {
            v.reserve(n);
        } else {
            v.reserve_exact(n);
        }
        v
    }
}
