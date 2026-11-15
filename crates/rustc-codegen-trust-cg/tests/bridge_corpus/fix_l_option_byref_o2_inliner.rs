// (l) FIXED — the same multi-block-inliner return-join defect as
// `fix_l_enum_byref_o2_inliner.rs`, on `Option<u8>`: `match &opt { None => 100,
// Some(v) => *v }` returned `16 0` for `100 9` at -O2 and was correct at -O0.
// The `-O2` binary has no `rd` symbol either way — the callee IS inlined; what
// changed is that every return path now joins the call result through a `Copy`.
// Differential-OK at -O0 and -O2.
#[inline(never)] fn en(c: bool) -> Option<u8> { if c { None } else { Some(9) } }
#[inline(never)] fn rd(e: &Option<u8>) -> u8 { match e { None => 100, Some(v) => *v } }
fn main() { let e1 = en(true); let e2 = en(false); println!("{} {}", rd(&e1), rd(&e2)); }
