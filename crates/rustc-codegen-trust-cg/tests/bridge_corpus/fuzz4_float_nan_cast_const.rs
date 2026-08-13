// CORPUS FIXTURE — FUZZ-4 float / NaN / saturating-cast / const-eval sweep.
//
// A single deterministic no_std program that a WRONG float-comparison-parity
// lowering, a WRONG saturating float->int clamp, or a mis-evaluated const array
// would each diverge on (distinct exit code), tying FUZZ-4's clean-surface
// evidence (0 wrong-value miscompiles across ~60 programs) to an executable
// oracle. Every sub-result folds into the low byte of a running checksum.
//
// Covers:
//   * All 6 float comparison predicates with NaN in BOTH operand positions
//     (the x86 ucomisd parity edge: ordered `==`/`<`/`<=` must AND-NOT-parity,
//     unordered `!=` must OR-parity — a wrong SETcc mask flips a NaN result).
//   * Saturating float->int `as` casts (Rust semantics): +inf/huge -> MAX,
//     -inf/huge-neg -> MIN(signed)/0(unsigned), NaN -> 0, in-range -> trunc,
//     at i8/u8/i32/u32 widths (the CVTTSD2SI + threshold-CMOV clamp paths).
//   * A `const fn`-built array indexed at a runtime (black_box) index.
//   * -0.0 sign propagation through +/*.
//
// Agree O0/O2/O3 -> 178.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

const fn squares() -> [i32; 8] {
    let mut a = [0i32; 8];
    let mut i = 0;
    while i < 8 {
        a[i] = (i as i32) * (i as i32);
        i += 1;
    }
    a
}
const SQ: [i32; 8] = squares(); // [0,1,4,9,16,25,36,49]

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut r: u32 = 0;

    // --- NaN comparison parity, both operand positions ---
    let n = black_box(f64::NAN);
    let x = black_box(2.0f64);
    // ordered predicates: every one is FALSE when a NaN is involved
    if n < x { r |= 1 << 0; }
    if x < n { r |= 1 << 0; }
    if n <= x { r |= 1 << 0; }
    if x <= n { r |= 1 << 0; }
    if n > x { r |= 1 << 0; }
    if x > n { r |= 1 << 0; }
    if n >= x { r |= 1 << 0; }
    if x >= n { r |= 1 << 0; }
    if n == x { r |= 1 << 0; }
    if x == n { r |= 1 << 0; }
    // `!=` is unordered-true: both directions must be TRUE
    if n != x { r += 7; }
    if x != n { r += 7; }
    // a real ordered compare still works
    if x < black_box(3.0f64) { r += 3; }
    // running: r = 0 (no ordered NaN bit) + 7 + 7 + 3 = 17

    // --- saturating float->int casts ---
    let huge = black_box(1e18f64);
    let neg = black_box(-1e18f64);
    let nan = black_box(f64::NAN);
    let ok = black_box(-1.5f64);
    r = r.wrapping_add((huge as i32) as u32);   // i32::MAX = 2147483647
    r = r.wrapping_add((neg as i32) as u32);     // i32::MIN = -2147483648
    // 2147483647 + (-2147483648) = -1 -> 0xFFFFFFFF; + prior 17 = 16
    r = r.wrapping_add((nan as i32) as u32);     // 0
    r = r.wrapping_add((huge as u32));           // u32::MAX = 4294967295 -> wraps
    // 16 + 4294967295 = 15 (mod 2^32)
    r = r.wrapping_add((neg as u32));            // 0 (neg saturates to 0)
    r = r.wrapping_add((huge as u8) as u32);     // 255
    r = r.wrapping_add((neg as i8) as i32 as u32); // -128 -> 0xFFFFFF80
    r = r.wrapping_add((ok as i8) as i32 as u32);  // -1  -> 0xFFFFFFFF
    // 15 + 255 + (-128) + (-1) = 141

    // --- const array indexed at runtime ---
    let i = black_box(6usize);
    r = r.wrapping_add(SQ[i] as u32);            // 36 -> 177

    // --- -0.0 sign propagation ---
    let nz = black_box(-0.0f64);
    if (nz + 0.0).is_sign_positive() { r += 1; } // -0.0 + 0.0 = +0.0 -> 178
    if (nz * 1.0).is_sign_positive() { r += 100; } // -0.0 * 1.0 = -0.0 -> NOT added

    (r & 0xff) as i32
}
