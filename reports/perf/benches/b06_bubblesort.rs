// GOAL-3 perf baseline benchmark.
// Bubble sort of a fixed array (worst-case-ish reverse-ish data), repeated.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 256;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 1400 {
        let mut arr = [0u32; N];
        let mut i = 0;
        while i < N {
            // pseudo-random-ish fill, deterministic per rep
            arr[i] = ((i as u32).wrapping_mul(2654435761).wrapping_add(rep)) ^ 0x5bd1e995;
            i += 1;
        }
        let mut n = N;
        while n > 1 {
            let mut j = 1;
            while j < n {
                if arr[j - 1] > arr[j] {
                    let tmp = arr[j - 1];
                    arr[j - 1] = arr[j];
                    arr[j] = tmp;
                }
                j += 1;
            }
            n -= 1;
        }
        // checksum: xor of sorted, weighted by index
        let mut cs: u64 = 0;
        let mut k = 0;
        while k < N {
            cs = cs.wrapping_add((arr[k] as u64).wrapping_mul(k as u64 + 1));
            k += 1;
        }
        acc = acc.wrapping_add(cs);
        rep += 1;
    }
    (acc & 0xff) as i32
}
