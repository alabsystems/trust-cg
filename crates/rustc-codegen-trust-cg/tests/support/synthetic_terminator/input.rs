// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![no_std]
pub struct Tracked(pub usize);
impl Drop for Tracked {
    fn drop(&mut self) {
        self.0 = self.0.wrapping_add(1);
    }
}
pub fn case_simple() -> usize {
    17
}
pub fn case_drop(value: Tracked) -> usize {
    value.0
}
pub fn case_conditional(value: Tracked, choose: bool) -> usize {
    if choose { value.0 } else { 0 }
}
pub fn case_borrowed(_: &mut Tracked) {}
pub fn case_bounds(values: &[u8], index: usize) -> u8 {
    values[index]
}
pub fn case_overflow(a: u8, b: u8) -> u8 {
    a + b
}
pub fn case_divide(a: u64, b: u64) -> u64 {
    a / b
}
pub fn case_loop(limit: usize) -> usize {
    let mut value = 0;
    while value < limit {
        value += 1;
    }
    value
}
