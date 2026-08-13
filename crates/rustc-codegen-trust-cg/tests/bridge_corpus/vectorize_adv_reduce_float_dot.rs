// OPT-12-REDUCE adversarial: a FLOAT dot-product d += a[i]*b[i] over [f32;N].
// Float add is non-associative, so the reduction MUST stay scalar (float loads
// are MOVSS not MOVRM32; the accumulator is Fpr128 not Gpr32; the combine is
// ADDSS not ADDRR). Rust emits no fast-math, so LLVM keeps an ordered scalar
// dot -> the bridge (scalar) equals LLVM bit-for-bit (or fails closed = safe).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 100;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut a = [0f32; N];
    let mut b = [0f32; N];
    let mut i = 0usize;
    while i < N { a[i] = bb((i as f32) * 0.25 + 1.0); i += 1; }
    let mut i = 0usize;
    while i < N { b[i] = bb((i as f32) * 0.5 - 3.0); i += 1; }
    let mut d: f32 = bb(0.0);
    let mut i = 0usize;
    while i < N { d += a[i] * b[i]; i += 1; }
    ((d.to_bits() as u64) % 126) as i32
}
