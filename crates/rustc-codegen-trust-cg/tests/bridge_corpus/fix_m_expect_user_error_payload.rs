// (m) `.expect()` on `Err(Error(7))` with a non-ZST user `Error(u8)` must
// panic (exit 134); the name-keyed no-op let it fall through to `exit(3)`.
#[derive(Debug)]
struct Error(u8);
#[inline(never)]
fn f(x: i32) -> Result<(), Error> { if x > 0 { Err(Error(7)) } else { Ok(()) } }
#[inline(never)]
fn one() -> i32 { 1 }
fn main() {
    f(one()).expect("must abort here");
    std::process::exit(3);
}
