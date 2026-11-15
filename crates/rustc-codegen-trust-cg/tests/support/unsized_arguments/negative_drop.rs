#![no_std]
#![feature(unsized_fn_params)]
pub struct Item(pub u64);
unsafe extern "C" {
    fn observed(v: u64);
}
impl Drop for Item {
    fn drop(&mut self) {
        unsafe {
            observed(self.0);
        }
    }
}
#[unsafe(no_mangle)]
pub fn owned_drop(s: [Item]) -> usize {
    s.len()
}
