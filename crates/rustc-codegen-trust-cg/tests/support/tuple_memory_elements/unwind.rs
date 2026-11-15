#![no_std]
unsafe extern "C" {
    fn record_drop(tag: u64);
}
unsafe extern "C-unwind" {
    fn cleanup_callback(value: u64) -> u64;
}
#[repr(C)]
struct Guard {
    tag: u64,
    a: u64,
    b: u64,
}
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe {
            record_drop(self.tag ^ self.a ^ self.b);
        }
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn conditional_drop(value: u64) -> u64 {
    let guard = Guard {
        tag: value,
        a: 0x1234,
        b: 0xabcd,
    };
    if value & 1 == 0 {
        drop(guard);
    }
    unsafe { cleanup_callback(value) }
}
