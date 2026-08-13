// GOAL-3 perf baseline benchmark.
// Sieve of Eratosthenes over a fixed array, repeated; checksum = prime count.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 4096;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 4200 {
        let mut sieve = [1u8; N];
        sieve[0] = 0;
        sieve[1] = 0;
        let mut p: usize = 2;
        while p * p < N {
            if sieve[p] == 1 {
                let mut m = p * p;
                while m < N {
                    sieve[m] = 0;
                    m += p;
                }
            }
            p += 1;
        }
        let mut count: u64 = 0;
        let mut k: usize = 0;
        while k < N {
            count += sieve[k] as u64;
            k += 1;
        }
        acc = acc.wrapping_add(count);
        rep += 1;
    }
    (acc & 0xff) as i32
}
