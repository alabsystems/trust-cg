#![no_std]
#![no_main]
extern crate linkage_base as base;

mod first {
    #[inline(never)]
    pub fn call(x: u64) -> u64 {
        super::base::repeated(x)
    }
}
mod second {
    #[inline(never)]
    pub fn call(x: u64) -> u64 {
        super::base::repeated(x ^ 0x12345678)
    }
}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    let mut i = 0u64;
    while i < 4096 {
        let x = i.wrapping_mul(0x35417757abce91);
        let y = x ^ 0x12345678;
        if first::call(x) != x.wrapping_mul(5).wrapping_add(7) {
            return 1;
        }
        if second::call(x) != y.wrapping_mul(5).wrapping_add(7) {
            return 2;
        }
        i += 1;
    }
    0
}
