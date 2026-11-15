extern crate real_map_provider;
use std::collections::BTreeMap;
type Map = BTreeMap<u64, u64>;

fn check_layout() {
    assert_eq!(
        real_map_provider::map_layout(),
        (std::mem::size_of::<Map>(), std::mem::align_of::<Map>())
    );
}
fn check_contents(value: &Map, filled: bool) {
    assert_eq!(value.len(), if filled { 2 } else { 0 });
    assert_eq!(value.get(&11).copied(), filled.then_some(101));
    assert_eq!(value.get(&29).copied(), filled.then_some(203));
}

#[inline(never)]
pub fn run_owned(consume: fn(Box<Map>) -> u64) {
    check_layout();
    for filled in [false, true] {
        let value = real_map_provider::make_map(filled);
        check_contents(&value, filled);
        assert_eq!(consume(value), 7);
        assert_eq!(
            real_map_provider::observation(),
            (1, 0),
            "real map outer allocation must be freed once with its real layout"
        );
    }
    println!(
        "REAL_MAP_DYN_ORIGIN|kind=owned|scenarios=2|outer_frees=2|bad_layout=0|provider=LLVM|oracle=LLVM"
    );
}

#[inline(never)]
pub fn run_borrowed(consume: fn(&Map) -> u64) {
    check_layout();
    for filled in [false, true] {
        let value = real_map_provider::make_map(filled);
        check_contents(&value, filled);
        assert_eq!(consume(&value), 7);
        assert_eq!(
            real_map_provider::observation(),
            (0, 0),
            "a borrow must not free the outer allocation"
        );
        check_contents(&value, filled);
        drop(value);
        assert_eq!(
            real_map_provider::observation(),
            (1, 0),
            "LLVM owner must free its real map once after the borrow"
        );
    }
    println!(
        "REAL_MAP_DYN_ORIGIN|kind=borrowed|scenarios=2|outer_frees=2|bad_layout=0|provider=LLVM|oracle=LLVM"
    );
}
