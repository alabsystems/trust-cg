// GOAL-3 perf baseline benchmark.
// Integer loop: running sum/product/mod accumulation.
// no_std + no_main + extern "C" fn main so it compiles through both LLVM and
// the trust-cg bridge (the bridge fails closed on std::rt::lang_start). The
// exit code (checksum & 0xff) is the correctness oracle; it is identical under
// LLVM and the bridge when codegen is correct.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u64 = 0;
    while rep < 11000 {
        let mut sum: u64 = 0;
        let mut prod: u64 = 1;
        let mut i: u64 = 1;
        while i <= 2000 {
            sum = sum.wrapping_add(i);
            prod = prod.wrapping_mul(i | 1);
            sum = sum.wrapping_add(prod % 1009);
            i += 1;
        }
        acc = acc.wrapping_add(sum);
        rep += 1;
    }
    (acc & 0xff) as i32
}
