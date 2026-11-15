// format! into a String; observe the result through a byte checksum. (A
// runtime-length `&str` placeholder and a `.len()`-derived placeholder are
// separate unsupported lanes, so neither is used here.)
fn main() {
    let n: i32 = -13;
    let f = format!("v={} w={}", n, 5u32);
    let b: &[u8] = f.as_bytes();
    let mut i: usize = 0;
    let mut sum: u64 = 0;
    let mut count: u64 = 0;
    while i < b.len() {
        sum = sum * 31 + (b[i] as u64);
        count += 1;
        i += 1;
    }
    println!("count={}", count);
    println!("sum={}", sum);
}
