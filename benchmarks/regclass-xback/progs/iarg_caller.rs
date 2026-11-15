// CALLER: exits 42 when the by-value integer pair arrives intact.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassiarg;
use regclassiarg::Q;
fn main() {
    std::process::exit(regclassiarg::take(Q { a: 20, b: 22 }));
}
