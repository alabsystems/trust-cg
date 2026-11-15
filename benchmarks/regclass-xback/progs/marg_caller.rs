// CALLER: exits 42 when the mixed-width by-value pair arrives intact.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassmarg;
use regclassmarg::M;
fn main() {
    std::process::exit(regclassmarg::take(M { a: 10, b: 22 }));
}
