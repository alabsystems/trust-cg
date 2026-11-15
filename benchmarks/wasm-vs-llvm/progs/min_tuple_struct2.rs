#![no_std]
#![allow(dead_code)]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}
struct Re(u32, u32);
impl Re {
    #[inline(never)]
    fn area(&self) -> u32 {
        self.0.wrapping_mul(self.1)
    }
}
#[no_mangle]
pub extern "C" fn f(a: u32) -> u32 {
    let r = Re(a, 9);
    r.area()
}
