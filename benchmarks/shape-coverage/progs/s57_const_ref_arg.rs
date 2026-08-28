// unwrap_or(&const) / passing &CONST refs to fns — O1 promotes &0 to a const
// pointer arg; must compile+match at all opts (was O1 decline).
use std::hint::black_box as bb;
fn f(s: &[u64]) -> u64 {
    let a = *s.first().unwrap_or(&7);
    let b = *s.last().unwrap_or(&11);
    let c = *s.get(100).unwrap_or(&99);
    let d = s.iter().max().unwrap_or(&0);
    a.wrapping_add(b).wrapping_add(c).wrapping_add(*d)
}
fn main(){ let v=[bb(10u64),bb(20),bb(30)]; std::process::exit((f(&v)%233) as i32); }
