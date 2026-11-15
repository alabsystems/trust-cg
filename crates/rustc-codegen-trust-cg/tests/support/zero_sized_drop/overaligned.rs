#![no_std]
unsafe extern "C" {
    fn note_address(kind: u64, address: usize);
}
#[repr(align(64))]
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe {
            note_address(1, self as *mut Self as usize);
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn zst_overaligned() {
    let _guard = Guard;
}

#[unsafe(no_mangle)]
pub extern "C" fn zst_tuple_overaligned() {
    let tuple = (Guard, ());
    unsafe {
        note_address(2, &tuple as *const (Guard, ()) as usize);
    }
}
