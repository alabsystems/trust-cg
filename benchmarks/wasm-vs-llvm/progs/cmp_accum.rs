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
pub extern "C" fn cmp_accum(a: u32, b: u32) -> i32 {
    let mut ord = Ordering::Equal;
    let mut k = 0;
    while k < 6 {
        let x = a.rotate_left(k * 5) & 0xf;
        let y = b.rotate_left(k * 3) & 0xf;
        ord = ord.then(x.cmp(&y));
        k += 1;
    }
    ord as i32
}
