// CALLER: exits 42 when the by-value float pair arrives intact.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassfarg;
use regclassfarg::P;
fn main() {
    std::process::exit(regclassfarg::take(P { a: 4.0, b: 40.0 }));
}
