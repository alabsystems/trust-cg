// CORPUS FIXTURE — lane types-slices-str-arrays #2: ARRAY shapes.
//
//   * `[T; 0]` is a ZST (`TrustIrTy::Unit`): a `-> [u8; 0]` return, a `&[u8; 0]`
//     parameter, and `&[]` — bound to rustc's aligned dangling pointer — unsized
//     to an empty `&[u8]` whose length is rustc's const 0;
//   * a `[u8; 4]` passed / returned by value and a `[u8; 16]`-field struct read
//     element-wise, both through the memory-aggregate slot at rustc's layout.
// `keep` launders lengths past the fmt interception's own `.len()` gate.
#[inline(never)]
fn keep(x: usize) -> u64 { x as u64 }
#[inline(never)]
fn make() -> [u8; 4] { [1, 2, 3, 4] }
#[inline(never)]
fn sum4(a: [u8; 4]) -> u32 { a[0] as u32 + a[1] as u32 * 10 + a[2] as u32 * 100 + a[3] as u32 * 1000 }
#[inline(never)]
fn zero() -> [u8; 0] { [] }
#[inline(never)]
fn as_slice0(a: &[u8; 0]) -> &[u8] { a }
#[inline(never)]
fn empty_slice() -> &'static [u8] { &[] }
#[inline(never)]
fn first_or(s: &[u8], d: u8) -> u8 { if s.is_empty() { d } else { s[0] } }
struct Ip([u8; 16]);
#[inline(never)]
fn ip_new(a: u16, b: u16) -> Ip {
    Ip([(a >> 8) as u8, a as u8, (b >> 8) as u8, b as u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
}
#[inline(never)]
fn ip_sum(ip: &Ip) -> u32 { let mut t = 0u32; let mut i = 0; while i < 16 { t += ip.0[i] as u32; i += 1; } t }
fn main() {
    // (every placeholder is a plain integer local: the fmt interception traces
    // only value locals and refuses a `.len()` placeholder itself)
    let a = make();
    let s4 = sum4(a);
    let z0 = keep(zero().len());
    println!("{} {}", s4, z0);
    let z: [u8; 0] = zero();
    let zl = keep(as_slice0(&z).len());
    let zl2 = keep(as_slice0(&[]).len());
    println!("{} {}", zl, zl2);
    let e = empty_slice();
    let el = keep(e.len());
    let ef = first_or(e, 42);
    println!("{} {}", el, ef);
    let ip = ip_new(0x1234, 0x5678);
    let i0 = ip.0[0];
    let i3 = ip.0[3];
    let i15 = ip.0[15];
    let isum = ip_sum(&ip);
    println!("{} {} {} {}", i0, i3, i15, isum);
}
