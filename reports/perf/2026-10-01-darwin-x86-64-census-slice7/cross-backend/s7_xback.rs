// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Slice-7 cross-backend rows in the format `m145_xback.py --test` extracts
// (a reproducer kept with the report, not compiled as a test): calls through
// memory across the backend boundary. The callee crate holds the callees that
// return through a hidden buffer (`make3`, `triple`, `pair_opt`, `mixed`) or
// write an out-parameter (`bump`, `fill`) or read one (`peek`), and their
// callers (each passes a private slot's address); every row folds a caller's
// results over 100 argument pairs and exits with the fold mod 251, which the
// LLVM rlib x LLVM bin oracle fixes.
//
//   m145_xback.py <bridge dylib> 0 --test s7_xback.rs --no-controls

const CALLEE_SRC: &str = r#"
pub struct Three { pub a: u64, pub b: u64, pub c: u64 }
#[inline(never)] pub fn make3(x: u64) -> Three { Three { a: x, b: x.wrapping_add(1), c: x.wrapping_mul(3) } }
#[inline(never)] pub fn triple(x: u64) -> (u64, u64, u64) { (x, x ^ 5, x.wrapping_sub(2)) }
#[inline(never)] pub fn pair_opt(x: u64) -> Option<(u64, u64)> { if x & 1 == 1 { Some((x, x >> 1)) } else { None } }
#[inline(never)] pub fn mixed(x: u64) -> (u64, u32, bool) { (x, (x as u32) ^ 3, x & 4 != 0) }
#[inline(never)] pub fn bump(p: &mut u64) { *p = p.wrapping_add(1); }
#[inline(never)] pub fn peek(p: &u64) -> u64 { p.wrapping_mul(7) }
#[inline(never)] pub fn fill(o: &mut Option<u64>, x: u64) { if x > 3 { *o = Some(x) } }
#[inline(never)] pub fn twice(x: u64) -> u64 { x.wrapping_mul(2) }
#[inline(never)] pub fn sum3(x: u64) -> u64 { let t = make3(x); t.a.wrapping_add(t.b).wrapping_add(t.c) }
#[inline(never)] pub fn field3(x: u64) -> u64 { make3(x).b }
#[inline(never)] pub fn mid(x: u64) -> u64 { triple(x).1 }
#[inline(never)] pub fn two_buffers(x: u64, y: u64) -> u64 { make3(x).a.wrapping_add(make3(y).c) }
#[inline(never)] pub fn fwd3(x: u64) -> Three { make3(x) }
#[inline(never)] pub fn branch_sret(c: bool, x: u64) -> u64 { if c { make3(x).c } else { x } }
#[inline(never)] pub fn opt_xor(x: u64) -> u64 { match pair_opt(x) { Some((a, b)) => a ^ b, None => 9 } }
#[inline(never)] pub fn mixed_sum(x: u64) -> u64 { let r = mixed(x); r.0 ^ (r.1 as u64) ^ (r.2 as u64) }
#[inline(never)] pub fn out_param(x: u64) -> u64 { let mut v = x; bump(&mut v); v }
#[inline(never)] pub fn out_twice(x: u64) -> u64 { let mut v = x; bump(&mut v); bump(&mut v); v }
#[inline(never)] pub fn read_ref(x: u64) -> u64 { let v = x; peek(&v) }
#[inline(never)] pub fn out_then_call(x: u64, y: u64) -> u64 { let mut v = x; bump(&mut v); twice(y).wrapping_add(v) }
#[inline(never)] pub fn out_then_store(p: &mut u64, x: u64) { let mut v = x; bump(&mut v); *p = v; }
#[inline(never)] pub fn opt_out(x: u64) -> u64 { let mut o = None; fill(&mut o, x); match o { Some(v) => v, None => 0 } }
"#;

const CALLER_HDR: &str = "use std::hint::black_box as bb;\n\
    use callee::*;\n\
    const V: [u64; 10] = [0, 1, 2, 5, 7, 0x7f, 0x80, 200, 1 << 63, u64::MAX];\n\
    fn exit(v: u64) -> ! { std::process::exit(((v >> 32) % 251) as i32) }\n\
    fn fold(f: impl Fn(u64, u64) -> u64) -> u64 { let mut h = 0u64; for &a in &V { for &b in &V { h = (h.rotate_left(5) ^ f(bb(a), bb(b))).wrapping_mul(0x9E37_79B9_7F4A_7C15); } } h }\n";

/// `(shape, caller body, expected exit code)`: the LLVM oracle's fold.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        ("sum3", r#"fn main() { exit(fold(|a, _| sum3(a))) }"#, 9),
        ("field3", r#"fn main() { exit(fold(|a, _| field3(a))) }"#, 124),
        ("mid", r#"fn main() { exit(fold(|a, _| mid(a))) }"#, 7),
        ("two_buffers", r#"fn main() { exit(fold(|a, b| two_buffers(a, b))) }"#, 125),
        ("fwd3", r#"fn main() { exit(fold(|a, _| { let t = fwd3(a); t.a ^ t.b ^ t.c })) }"#, 130),
        ("branch_sret", r#"fn main() { exit(fold(|a, b| branch_sret(a < b, a))) }"#, 63),
        ("opt_xor", r#"fn main() { exit(fold(|a, _| opt_xor(a))) }"#, 191),
        ("mixed_sum", r#"fn main() { exit(fold(|a, _| mixed_sum(a))) }"#, 117),
        ("out_param", r#"fn main() { exit(fold(|a, _| out_param(a))) }"#, 124),
        ("out_twice", r#"fn main() { exit(fold(|a, _| out_twice(a))) }"#, 102),
        ("read_ref", r#"fn main() { exit(fold(|a, _| read_ref(a))) }"#, 213),
        ("out_then_call", r#"fn main() { exit(fold(|a, b| out_then_call(a, b))) }"#, 224),
        ("out_then_store", r#"fn main() { exit(fold(|a, _| { let mut s = 99u64; out_then_store(bb(&mut s), a); s })) }"#, 124),
        ("opt_out", r#"fn main() { exit(fold(|a, _| opt_out(a))) }"#, 92),
    ]
}
