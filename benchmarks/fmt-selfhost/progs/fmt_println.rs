// println!/print! with integer and &str placeholders — the non-local (user-crate)
// `core::fmt` interception lane. Must behave identically before/after the
// self-host layout change, which only fires when the fmt types are LOCAL.
fn main() {
    let n: i32 = 42;
    let m: u64 = 7;
    let s: &str = "abc";
    println!("hello");
    println!("n={} m={} s={}", n, m, s);
    print!("no-newline {}\n", n);
    eprintln!("err {}", m);
}
