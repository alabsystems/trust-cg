use std::collections::BTreeMap;
type Map = BTreeMap<u64, u64>;

trait Marker {
    fn marker(&self) -> u64;
}
impl Marker for Map {
    #[inline(never)]
    fn marker(&self) -> u64 {
        7
    }
}

#[cfg(real_map_owned)]
#[inline(never)]
fn consume_owned(value: Box<Map>) -> u64 {
    let object: Box<dyn Marker> = value;
    let result = object.marker();
    drop(object);
    result
}

#[cfg(real_map_borrowed)]
#[inline(never)]
fn consume_borrowed(value: &Map) -> u64 {
    let object: &dyn Marker = value;
    object.marker()
}

extern crate real_map_oracle;
#[cfg(real_map_owned)]
fn main() {
    real_map_oracle::run_owned(consume_owned);
}
#[cfg(real_map_borrowed)]
fn main() {
    real_map_oracle::run_borrowed(consume_borrowed);
}
