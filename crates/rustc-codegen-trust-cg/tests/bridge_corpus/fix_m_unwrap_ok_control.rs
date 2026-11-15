// (m) CONTROL: the intercepted `write!` result IS statically `Ok(())`, so its
// `.unwrap()` stays a no-op and the program reaches `exit(3)` on both sides.
use std::fmt::Write;
fn main() {
    let mut s = String::new();
    write!(s, "{}", 5).unwrap();
    if s.len() != 1 { std::process::exit(9); }
    std::process::exit(3);
}
