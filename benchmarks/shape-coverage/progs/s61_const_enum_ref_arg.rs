// passing &CONST_ENUM to a fn (ev(&E::A(7))) — O1 promotes to a const &E arg;
// must compile+match at all opts (was O1 decline). Completes the const-ref-arg class.
use std::hint::black_box as bb;
#[derive(Clone,Copy)] enum E { A(u64), B { v: u64 }, C }
fn ev(e: &E) -> u64 { match e { E::A(v) => *v, E::B { v } => v.wrapping_mul(2), E::C => 99 } }
fn main() {
    let x = E::A(bb(10));
    let acc = ev(&x).wrapping_add(ev(&E::B { v: 5 })).wrapping_add(ev(&E::C)).wrapping_add(ev(&E::A(7)));
    std::process::exit((acc % 233) as i32);
}
