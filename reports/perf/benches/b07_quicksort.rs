// GOAL-3 perf baseline benchmark.
// Iterative quicksort (explicit stack) of a fixed array, repeated.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 512;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 1800 {
        let mut arr = [0u32; N];
        let mut i = 0;
        while i < N {
            arr[i] = ((i as u32).wrapping_mul(40503).wrapping_add(rep.wrapping_mul(7))) % 100003;
            i += 1;
        }
        // explicit-stack quicksort
        let mut stack = [0usize; 64];
        let mut sp = 0;
        stack[sp] = 0;
        sp += 1;
        stack[sp] = N - 1;
        sp += 1;
        while sp > 0 {
            sp -= 1;
            let hi = stack[sp];
            sp -= 1;
            let lo = stack[sp];
            if lo >= hi {
                continue;
            }
            let pivot = arr[(lo + hi) / 2];
            let mut a = lo;
            let mut b = hi;
            loop {
                while arr[a] < pivot {
                    a += 1;
                }
                while arr[b] > pivot {
                    if b == 0 {
                        break;
                    }
                    b -= 1;
                }
                if a >= b {
                    break;
                }
                let t = arr[a];
                arr[a] = arr[b];
                arr[b] = t;
                a += 1;
                if b == 0 {
                    break;
                }
                b -= 1;
            }
            if sp + 4 <= 64 {
                stack[sp] = lo;
                sp += 1;
                stack[sp] = b;
                sp += 1;
                stack[sp] = b + 1;
                sp += 1;
                stack[sp] = hi;
                sp += 1;
            }
        }
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
