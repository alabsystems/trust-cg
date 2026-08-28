// complex control flow: labeled break/continue 'outer, break-with-value from a
// loop, nested loops, while+continue — stresses CFG edges and block-param threading.
use std::hint::black_box as bb;
fn main() {
    let mut acc: u64 = 0;
    let n = bb(40u64);
    'outer: for i in 0..n {
        for j in 0..n {
            if i.wrapping_mul(j) > bb(500) { acc = acc.wrapping_add(i); continue 'outer; }
            if i.wrapping_add(j) == bb(37) { acc = acc.wrapping_add(1000); break 'outer; }
            acc = acc.wrapping_add(j & 3);
        }
    }
    // break with value from loop
    let mut k = 0u64;
    let found = loop {
        k = k.wrapping_add(bb(7));
        if k % bb(13) == 0 { break k; }
        if k > bb(10000) { break 0; }
    };
    acc = acc.wrapping_add(found);
    // while-let-ish via manual counter with continue
    let mut m = bb(100u64);
    while m > 0 {
        m -= 1;
        if m % 3 == 0 { continue; }
        acc = acc.wrapping_add(m & 7);
    }
    std::process::exit((acc % 251) as i32);
}
