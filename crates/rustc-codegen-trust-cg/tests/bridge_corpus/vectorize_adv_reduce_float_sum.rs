// OPT-12-REDUCE adversarial (THE CRITICAL ONE): a FLOAT sum s += f[i]. Float add
// is NOT associative (each add rounds), so summing four interleaved lanes then
// combining does NOT equal the sequential sum in general. The recognizer MUST
// reject this and keep it scalar: a float load is MOVSS (not MOVRM32), a float
// accumulator is Fpr128 (not Gpr32), and the add is ADDSS (not ADDRR) — a triple
// fail-safe. Rust emits no fast-math, so LLVM ALSO keeps an ordered (scalar)
// float sum -> the bridge (scalar) equals LLVM bit-for-bit. If instead the
// bridge fails closed on any float op, that is safe (a note, not a miscompile).
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box as bb;
const N: usize = 100;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut f = [0f32; N];
    let mut i = 0usize;
    while i < N { f[i] = bb((i as f32) * 0.5 + 1.0); i += 1; }
    let mut s: f32 = bb(0.0);
    let mut i = 0usize;
    while i < N { s += f[i]; i += 1; }
    ((s.to_bits() as u64) % 126) as i32
}
