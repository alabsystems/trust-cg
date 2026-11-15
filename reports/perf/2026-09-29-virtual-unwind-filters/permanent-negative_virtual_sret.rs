#![no_std]
#[repr(C)]
pub struct Large {
    pub words: [u64; 4],
}
pub trait Operation {
    fn run(&self, value: u64) -> Large;
}
unsafe extern "C" {
    fn virtual_event(value: u64);
}
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe {
            virtual_event(1);
        }
    }
}
#[unsafe(no_mangle)]
pub fn virtual_sret(op: &dyn Operation, value: u64) -> u64 {
    let _guard = Guard;
    op.run(value).words[0]
}
