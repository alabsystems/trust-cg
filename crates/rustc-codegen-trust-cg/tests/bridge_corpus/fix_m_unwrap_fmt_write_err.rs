// (m) A REAL `core::fmt::Error` from a USER `fmt::Write` impl (never intercepted):
// the receiver has no static `Ok` binding, so `.unwrap()` must lower for real
// and panic (exit 134). The type-only key used to no-op it (exit 3).
use std::fmt;
struct W;
impl fmt::Write for W {
    fn write_str(&mut self, _s: &str) -> fmt::Result { Err(fmt::Error) }
}
fn main() {
    let mut w = W;
    let r = fmt::Write::write_str(&mut w, "x");
    r.unwrap();
    std::process::exit(3);
}
