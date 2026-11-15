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
pub extern "C" fn inline_machine(a: u32) -> u32 {
    let mut m = Machine {
        state: Light::Red,
        ticks: 0,
    };
    let mut h = 0u32;
    for i in 0..12 {
        let go = (a >> i) & 1 == 1;
        m.state = match (m.state, go) {
            (Light::Red, true) => Light::Green,
            (Light::Green, _) => Light::Yellow,
            (Light::Yellow, _) => Light::Red,
            (s, false) => s,
        };
        m.ticks += 1;
        h = h * 3 + m.state as u32;
    }
    h ^ m.ticks << 28
}
