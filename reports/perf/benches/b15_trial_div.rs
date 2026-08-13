// GOAL-3 perf baseline benchmark.
// Prime counting by trial division over a range, repeated. div/mod heavy.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    if n % 2 == 0 {
        return n == 2;
    }
    let mut d: u64 = 3;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 2;
    }
    true
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 50 {
        let mut count: u64 = 0;
        let mut n: u64 = 2 + (rep as u64 & 1);
        while n < 30000 {
            if is_prime(n) {
                count += 1;
            }
            n += 1;
        }
        acc = acc.wrapping_add(count);
        rep += 1;
    }
    (acc & 0xff) as i32
}
