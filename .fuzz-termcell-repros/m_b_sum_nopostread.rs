fn main() {
    let a = [2i64, 7, 3];
    let b = [1i64, 5, 4, 6];
    let first: i64 = a.iter().sum();
    let s: i64 = b.iter().map(|&y| y ^ first).sum();
    std::process::exit(s.rem_euclid(128) as i32)
}
