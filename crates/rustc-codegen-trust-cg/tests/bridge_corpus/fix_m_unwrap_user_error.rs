// (m) `.unwrap()` on a `Result<(), Error>` whose `Error` is a USER type merely
// NAMED `Error`: `is_write_result_ty` keyed on the item NAME, so
// `lower_fmt_call` no-op'd the unwrap (exit 3 where LLVM aborts, 134). Now keyed
// on the `core::fmt::Error` DefId AND on the receiver carrying a static `Ok`
// discriminant binding (the intercepted `write_fmt` result). Expected: exit 134.
#[derive(Debug)]
struct Error;
#[inline(never)]
fn f(x: i32) -> Result<(), Error> { if x > 0 { Err(Error) } else { Ok(()) } }
#[inline(never)]
fn one() -> i32 { 1 }
fn main() {
    let r = f(one());
    r.unwrap();
    std::process::exit(3);
}
