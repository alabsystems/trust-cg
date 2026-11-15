// (l) The minimal shape of the multi-block-inliner return-join defect, kept as a
// separate row because it needs no enum at all: what matters is a callee with
// more than one `Return` block whose return type is NARROWER than the ABI
// register (u8/i8/u16 — a u32 return already wired through `Copy` and was
// always correct). `rd` is inlined at -O2 in every arm below; each must print
// its own value, not the last return path's.
#[inline(never)] fn rd8(x: &u8) -> u8 { match *x { 0 => 100, 1 => 200, _ => 55 } }
#[inline(never)] fn rd16(x: &u8) -> u16 { match *x { 0 => 1000, 1 => 2000, _ => 3000 } }
#[inline(never)] fn rdi8(x: &u8) -> i8 { match *x { 0 => 100, 1 => -100, _ => 7 } }
#[inline(never)] fn rd32(x: &u8) -> u32 { match *x { 0 => 100000, 1 => 200000, _ => 5 } }
fn main() {
    let a = 0u8; let b = 1u8; let c = 9u8;
    println!("{} {} {}", rd8(&a), rd8(&b), rd8(&c));
    println!("{} {} {}", rd16(&a), rd16(&b), rd16(&c));
    println!("{} {} {}", rdi8(&a), rdi8(&b), rdi8(&c));
    println!("{} {} {}", rd32(&a), rd32(&b), rd32(&c));
}
