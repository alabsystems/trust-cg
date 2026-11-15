// CALLER: exits 42 when the returned integer pair arrives intact.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassiret;
fn main() {
    let q = regclassiret::make(20);
    std::process::exit(q.a + q.b);
}
