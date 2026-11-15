// CORPUS FIXTURE — lane `self-host-no-interception`, program 1 (O0 and O2).
//
// REGRESSION GUARD for the self-host rule (`std_def_is_interceptable`): every
// interception below is keyed on a NON-LOCAL std def (this is a user crate
// linking the sysroot's core/alloc/std), so the rule must leave all of them
// exactly as they were — Range / RangeInclusive / slice::Iter chains with
// map/filter/zip/chain/rev/enumerate, the try_fold short-circuit family
// (any/position), str::Chars, and String. (The stride and owning iterator
// families are program 2, O0-only.) Every printed value depends on the
// intercepted body's semantics (order-sensitive accumulations, not sums).
fn main() {
    let mut acc: u64 = 0;
    for i in 0..7u64 { acc = acc * 3 + i; }
    let incl: u64 = (1..=10u64).sum();
    let mut v: Vec<i64> = Vec::new();
    for x in [3i64, -1, 4, 1, -5, 9, 2, 6].iter() { v.push(*x); }
    let w: Vec<i64> = v.iter().map(|x| x + 1).collect();
    let mf: i64 = v.iter().map(|x| x * 2).filter(|x| *x > 0).sum();
    let anyneg = v.iter().any(|x| *x < 0);
    let pos = v.iter().position(|x| *x == 9).unwrap_or(99);
    let z: i64 = v.iter().zip(w.iter()).map(|(a, b)| a * b).sum();
    let ch: i64 = (1..4i64).chain(10..12i64).fold(0, |a, x| a * 10 + x);
    let mut en: i64 = 0;
    for (i, x) in v.iter().enumerate() { en += (i as i64 + 1) * x; }
    let mut chars: u32 = 0;
    for c in "héllo".chars() { chars = chars * 31 + c as u32; }
    let mut s = String::new();
    s.push_str("ab"); s.push_str("cde");
    let mut sl: u32 = 0;
    for c in s.chars() { sl = sl * 2 + c as u32; }
    println!("{acc} {incl} {mf} {anyneg} {pos} {z} {ch} {en} {chars} {sl}");
}
