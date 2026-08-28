// array subslice with a CONSTANT range (&arr[1..5]) — sum the sub-slices.
// O1 mir-opt folds the range to a const; must compile+match at ALL opts (was O1 decline).
use std::hint::black_box as bb;
fn sum(s: &[u64]) -> u64 { s.iter().fold(0u64, |a, &x| a.wrapping_add(x)) }
fn main() { let d = [bb(10u64),bb(20),bb(30),bb(40),bb(50),bb(60)];
let mut acc=0u64; acc=acc.wrapping_add(sum(&d[1..5])).wrapping_add(sum(&d[2..4])).wrapping_add(sum(&d[0..3]));
std::process::exit((acc%233) as i32); }
