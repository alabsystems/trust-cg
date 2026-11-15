// CORPUS FIXTURE (lane types-dyn-fndef-uninhabited, #2) — UNINHABITED /
// zero-sized enums, typed by rustc's OWN layout. `Option<Infallible>` and
// `Result<Infallible, E>` (the `?` residuals) and `Infallible` itself have
// `size == 0`; the bridge used to fail closed on `Ty::option::Option<convert::
// Infallible>` / `Ty::convert::Infallible` when they crossed a signature
// (`FromResidual::from_residual(residual)`, `From<Infallible>::from(x)`). Now a
// zero-sized enum maps to `Unit` (no ABI slot, nothing read), while its static
// discriminant still comes from `Variants::Single { index }`.
// Uninhabited residual types: the `?` residuals `Option<Infallible>` and
// `Result<Infallible, E>` (both zero-sized), and a by-value `Infallible` param.
use core::convert::Infallible;
use core::num::TryFromIntError;
fn f(x: Option<u32>) -> Option<u32> { let v = x?; Some(v + 1) }
fn g(x: u64) -> Result<u32, TryFromIntError> { let a = u32::try_from(x)?; Ok(a * 2) }
fn absurd(x: Infallible) -> u32 { match x {} }
fn main() {
    let a = f(Some(4)).unwrap_or(0);
    let b = f(None).unwrap_or(0);
    let c = g(10).unwrap_or(0);
    let d = g(1u64 << 40).is_err() as u32;
    let p: fn(Infallible) -> u32 = absurd;
    let e = (p as usize != 0) as u32;
    println!("{} {} {} {} {}", a, b, c, d, e);
}
