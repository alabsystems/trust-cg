// Vec subslice with CONSTANT ranges (Range/RangeTo/RangeFrom): &v[1..5], &v[..4],
// &v[6..] — O1 folds these to const ranges; must compile+match at all opts.
use std::hint::black_box as bb;
fn sum(s:&[u64])->u64{s.iter().fold(0u64,|a,&x|a.wrapping_add(x))}
fn main(){let mut v:Vec<u64>=Vec::new(); for i in 0..bb(10u64){v.push(i);} 
let acc=sum(&v[..4]).wrapping_add(sum(&v[6..])).wrapping_add(sum(&v[2..8]));
std::process::exit((acc%233) as i32);}
