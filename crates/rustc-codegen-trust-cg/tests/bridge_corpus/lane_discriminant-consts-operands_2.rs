// CORPUS FIXTURE — lane discriminant-consts-operands: `Operand::RuntimeChecks`
// (Trust's MIR spells `intrinsics::ub_checks()` / `overflow_checks()` as a
// session-determined operand; `<[T]>::split_at_unchecked` and `<*const T>::add`
// guard their precondition checks on it), `StatementKind::ConstEvalCounter`
// (the CTFE step counter rustc leaves in a `const fn`'s runtime MIR at every
// loop back-edge — a no-op at run time), and `Rvalue::Repeat` whose count is a
// CONST GENERIC `N` that must be monomorphized before it is target-usize
// evaluable (`escape::hex_escape::<N>`'s `[AsciiChar::Null; N]`).
// The `RuntimeChecks` values are printed: both compilers see the same session,
// so the folded constant must agree with LLVM at every opt level.
#![feature(core_intrinsics)]
#![allow(internal_features)]
#[derive(Clone, Copy)]
enum Digit { Zero, One, Two, Three }

#[inline(never)]
fn split_fold(s: &[u32], mid: usize) -> u64 {
    let (a, b) = unsafe { s.split_at_unchecked(mid) };
    (a.len() as u64) * 1000 + (b.len() as u64) * 100 + (a[a.len() - 1] as u64) * 10 + b[0] as u64
}
#[inline(never)]
fn ub() -> bool { core::intrinsics::ub_checks() }
#[inline(never)]
fn ovf() -> bool { core::intrinsics::overflow_checks() }
#[inline(never)]
const fn tri(n: u64) -> u64 {
    let mut i = 0;
    let mut s = 0;
    while i < n { s += i; i += 1; }
    s
}
#[inline(never)]
fn filled<const N: usize>(v: u8) -> [u8; N] { [v; N] }
#[inline(never)]
fn digits<const N: usize>(hi: Digit) -> [Digit; N] {
    let mut out = [Digit::Zero; N];
    out[0] = hi;
    out[N - 1] = Digit::Three;
    out
}
#[inline(never)]
fn digit_code<const N: usize>(d: [Digit; N]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < N { acc = acc * 4 + d[i] as u32; i += 1; }
    acc
}
fn main() {
    let data = [1u32, 2, 3, 4, 5, 6, 7];
    println!("split {}", split_fold(&data, 3));
    println!("checks ub={} ovf={}", ub(), ovf());
    println!("tri {} {}", tri(10), tri(100));
    let f4 = filled::<4>(9);
    let f10 = filled::<10>(3);
    let mut sum = 0u32;
    let mut i = 0;
    while i < 4 { sum += f4[i] as u32; i += 1; }
    i = 0;
    while i < 10 { sum += f10[i] as u32 * 100; i += 1; }
    println!("filled {}", sum);
    println!("digits {} {}", digit_code::<4>(digits::<4>(Digit::One)), digit_code::<10>(digits::<10>(Digit::Two)));
}
