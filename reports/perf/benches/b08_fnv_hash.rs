// GOAL-3 perf baseline benchmark.
// FNV-1a byte hashing over a fixed byte buffer, repeated.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 1024;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // build a deterministic byte buffer once
    let mut buf = [0u8; N];
    let mut i = 0;
    while i < N {
        buf[i] = ((i.wrapping_mul(31).wrapping_add(7)) & 0xff) as u8;
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 28000 {
        let mut hash: u64 = 0xcbf29ce484222325;
        let mut k = 0;
        while k < N {
            hash ^= (buf[k] ^ (rep as u8)) as u64;
            hash = hash.wrapping_mul(0x100000001b3);
            k += 1;
        }
        // non-cancelling fold (mix in a rep-dependent multiplier so XOR can't
        // accidentally cancel to zero across reps)
        acc = acc.wrapping_add(hash.wrapping_mul(rep as u64 | 1));
        rep += 1;
    }
    ((acc ^ (acc >> 32)) & 0xff) as i32
}
