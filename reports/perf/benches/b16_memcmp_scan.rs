// GOAL-3 perf baseline benchmark.
// Naive substring search (byte scan / memcmp-like) over a fixed buffer.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 2048;
const M: usize = 7;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut buf = [0u8; N];
    let mut i = 0;
    while i < N {
        buf[i] = (((i * 3 + 1) % 5) as u8) + b'a';
        i += 1;
    }
    let pat = [b'a', b'b', b'a', b'a', b'b', b'a', b'c'];
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 28000 {
        // mutate one byte deterministically per rep to defeat hoisting
        let idx = (rep as usize) % N;
        let saved = buf[idx];
        buf[idx] = pat[(rep as usize) % M];
        let mut matches: u64 = 0;
        let mut s = 0;
        while s + M <= N {
            let mut k = 0;
            let mut ok = true;
            while k < M {
                if buf[s + k] != pat[k] {
                    ok = false;
                    break;
                }
                k += 1;
            }
            if ok {
                matches += 1;
            }
            s += 1;
        }
        buf[idx] = saved;
        acc = acc.wrapping_add(matches).wrapping_add(rep as u64);
        rep += 1;
    }
    (acc & 0xff) as i32
}
