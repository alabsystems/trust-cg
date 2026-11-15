// A formatted panic!: the `panic_fmt` consumer. Exit code (not text) is compared.
fn f(x: i32) -> i32 {
    if x > 3 { panic!("too big: {}", x); }
    x * 2
}
fn main() {
    println!("{}", f(1));
    println!("{}", f(9));
}
