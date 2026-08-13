// GOAL-3 perf baseline benchmark.
// Match-heavy state machine driven by a deterministic input stream.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut state: u32 = 0;
    let mut x: u64 = 0x243f6a8885a308d3;
    let mut i: u64 = 0;
    while i < 6000000 {
        x = x.wrapping_mul(2862933555777941757).wrapping_add(3037000493);
        let sym = (x >> 60) as u32 & 0x7;
        state = match state {
            0 => match sym {
                0 | 1 => 1,
                2 => 2,
                3 | 4 => 3,
                _ => 0,
            },
            1 => match sym {
                0 => 0,
                5 | 6 => 4,
                _ => 1,
            },
            2 => match sym {
                7 => 5,
                1 | 2 => 2,
                _ => 0,
            },
            3 => match sym {
                3 => 3,
                _ => 1,
            },
            4 => match sym {
                0 | 1 | 2 => 2,
                _ => 4,
            },
            _ => match sym {
                4 | 5 => 0,
                _ => 5,
            },
        };
        acc = acc.wrapping_add(state as u64).wrapping_add(sym as u64 * 3);
        i += 1;
    }
    (acc & 0xff) as i32
}
