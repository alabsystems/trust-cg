fn main() {
    let k: i64 = 3;
    let a = [2i64, 7, 3];
    let b = [1i64, 5, 4, 6];
    let first: i64 = a.iter().map(|&x| x * k).sum();
    let second: i64 = b.iter().map(|&y| (y ^ first) % 7).sum();
    std::process::exit((second * 2 + first).rem_euclid(128) as i32)
}
