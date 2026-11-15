// CORPUS FIXTURE — `core::ptr::eq` over two `BTreeMap`s / `HashMap`s is refused
// by name.
//
// WHAT IT PINS. The map interceptors recognized a map method from a crate test
// on the callee, the first argument's type with one reference or raw pointer
// peeled, and the item name. `ptr::eq::<BTreeMap<_, _>>` is a std callee taking
// a map that is not one of the map's own inherent methods, so none of the map
// arms stands in for it. Where the call reaches the bridge (-O0/-O1) it is now
// refused by name (`[TCG-MAP-CALLEE]`); at -O2/-O3 rustc inlines `ptr::eq` into
// a raw-pointer comparison and the program must match LLVM.
//
// HOW IT FAILS IF THE FIX IS REVERTED. The bridge still refuses at -O0/-O1, but
// without naming `[TCG-MAP-CALLEE]`: measured on 6b108b81d, "`BTreeMap::<u64,
// u64>::eq` is not an intercepted BTreeMap method" and the same for `HashMap`.

use std::collections::{BTreeMap, HashMap};
use std::hint::black_box as bb;

#[inline(never)]
fn same_btree(a: &BTreeMap<u64, u64>, b: &BTreeMap<u64, u64>) -> bool {
    std::ptr::eq(a, b)
}

#[inline(never)]
fn same_hash(a: &HashMap<u64, u64>, b: &HashMap<u64, u64>) -> bool {
    std::ptr::eq(a, b)
}

fn main() {
    let mut x: BTreeMap<u64, u64> = BTreeMap::new();
    x.insert(bb(1), 2);
    let mut y: BTreeMap<u64, u64> = BTreeMap::new();
    y.insert(bb(1), 2);
    let mut h: HashMap<u64, u64> = HashMap::new();
    h.insert(bb(1), 2);
    let mut code = 0;
    if same_btree(&x, &y) {
        code |= 1;
    }
    if !same_btree(&x, &x) {
        code |= 2;
    }
    if !same_hash(&h, &h) {
        code |= 4;
    }
    std::process::exit(code + 3);
}
