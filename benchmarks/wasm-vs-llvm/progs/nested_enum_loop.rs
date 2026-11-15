#![no_std]
#![allow(dead_code)]

use core::cmp::Ordering;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Light {
    Red,
    Green,
    Yellow,
}

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
enum Mode {
    Idle = 10,
    Run = 20,
    Halt = 250,
}

struct Machine {
    state: Light,
    ticks: u32,
}

impl Machine {
    #[inline(never)]
    fn tick(&mut self, go: bool) {
        self.state = match (self.state, go) {
            (Light::Red, true) => Light::Green,
            (Light::Green, _) => Light::Yellow,
            (Light::Yellow, _) => Light::Red,
            (s, false) => s,
        };
        self.ticks += 1;
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Tok {
    None,
    Word,
    Space,
    Punct,
}

#[no_mangle]
pub extern "C" fn nested_enum_loop(a: u32) -> u32 {
    let mut outer = Light::Red;
    let mut total = 0u32;
    for i in 0..4 {
        let mut inner = outer;
        for j in 0..3 {
            if (a >> (i * 3 + j)) & 1 == 1 {
                inner = match inner {
                    Light::Red => Light::Yellow,
                    Light::Yellow => Light::Green,
                    Light::Green => Light::Red,
                };
            }
            total = total * 3 + inner as u32;
        }
        outer = inner;
    }
    total ^ (outer as u32) << 30
}
