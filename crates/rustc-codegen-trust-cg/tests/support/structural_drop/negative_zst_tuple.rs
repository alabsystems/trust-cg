#![no_std]
struct Leaf(u64);
unsafe extern "C" {
    fn record(value: u64);
}
impl Drop for Leaf {
    fn drop(&mut self) {
        unsafe {
            record(self.0);
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn rejected(seed: u64) {
    let _tuple = ((), Leaf(seed), 7_u8, (Leaf(seed ^ 123), ()));
}
