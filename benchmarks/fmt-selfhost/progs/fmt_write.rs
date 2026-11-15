// write! into a String via `<String as fmt::Write>::write_fmt`, twice (append).
use std::fmt::Write;
fn main() {
    let mut s = String::new();
    write!(s, "a={} ", 1i32).unwrap();
    write!(s, "b={}", 22u16).unwrap();
    let b: &[u8] = s.as_bytes();
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
