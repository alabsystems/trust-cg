// CORPUS FIXTURE — lane `self-host-no-interception`, program 3 (O0 and O2).
// COMPILE WITH `--crate-name std` (add it to the standard FLAGS).
//
// THE RULE ITSELF (`std_def_is_interceptable`): every type below is a LOCAL
// look-alike of a std iterator the bridge recognizes by ITEM NAME + DEFINING
// CRATE (+ def-path segments) — `Chars`, `slice::Windows`, `array::IntoIter`,
// `vec::IntoIter`, `str::Bytes`, `iter::adapters::map::Map`. Named `std`,
// this crate satisfies every crate-name gate, so before the rule the bridge
// took these for the std types and modeled them with its own cursors
// (measured at bb935688: an ICE, `index out of bounds` in the iterator-chain
// resolver reading generic args a local `Map { n }` does not have). Under the
// rule a local def is never intercepted: each `next`/`new`/`size_hint` runs its
// REAL body. Values are order-sensitive so a substituted model cannot match.
pub struct Chars { p: usize }
impl Chars {
    pub fn next(&mut self) -> Option<char> {
        if self.p < 3 { self.p += 1; Some((b'a' + self.p as u8) as char) } else { None } }
}
pub mod slice {
    pub struct Windows<'a> { pub v: &'a [u64; 3], pub i: usize }
    impl<'a> Windows<'a> {
        pub fn new(v: &'a [u64; 3]) -> Self { Windows { v, i: 0 } }
        pub fn next(&mut self) -> Option<u64> {
            if self.i < self.v.len() { self.i += 1; Some(self.v[self.i - 1] * 3) } else { None } }
    }
}
pub mod array {
    pub struct IntoIter { pub k: u32 }
    impl IntoIter {
        pub fn next(&mut self) -> Option<u32> {
            if self.k > 0 { self.k -= 1; Some(self.k * 11) } else { None } }
        pub fn size_hint(&self) -> usize { self.k as usize + 100 }
    }
}
pub mod vec {
    pub struct IntoIter { pub n: i64 }
    impl IntoIter {
        pub fn next(&mut self) -> Option<i64> {
            if self.n < 30 { self.n += 7; Some(self.n) } else { None } }
    }
}
pub mod str {
    pub struct Bytes { pub b: u8 }
    impl Bytes {
        pub fn next(&mut self) -> Option<u8> {
            if self.b < 200 { self.b = self.b.wrapping_mul(3).wrapping_add(1); Some(self.b) } else { None } }
    }
}
pub mod iter { pub mod adapters { pub mod map {
    pub struct Map { pub n: i64 }
    impl Map {
        pub fn next(&mut self) -> Option<i64> {
            if self.n < 40 { self.n += 10; Some(self.n) } else { None } }
    }
} } }
fn main() {
    let mut c = Chars { p: 0 };
    let mut s: u64 = 0;
    while let Some(ch) = c.next() { s = s * 256 + ch as u64; }
    let v = [2u64, 5, 9];
    let mut w = slice::Windows::new(&v);
    let mut ws = 0;
    while let Some(x) = w.next() { ws = ws * 100 + x; }
    let mut a = array::IntoIter { k: 4 };
    let l = a.size_hint();
    let mut asum = 0;
    while let Some(x) = a.next() { asum = asum * 100 + x; }
    let mut vi = vec::IntoIter { n: 0 };
    let mut vs = 0;
    while let Some(x) = vi.next() { vs = vs * 100 + x; }
    let mut by = str::Bytes { b: 1 };
    let mut bs: u64 = 0;
    while let Some(x) = by.next() { bs = bs * 1000 + x as u64; }
    let mut m = iter::adapters::map::Map { n: 0 };
    let mut ms = 0;
    while let Some(x) = m.next() { ms = ms * 100 + x; }
    println!("{s} {ws} {l} {asum} {vs} {bs} {ms}");
}
