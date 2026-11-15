//! LLVM-compiled provider: every map here has rustc's real layout. The keys
//! (10, 30, 50 -> 100, 300, 500) are chosen so a bridge that reads one of
//! these maps as its own `{ptr,cap,len}` slot image cannot land on an answer
//! by coincidence (a slot misread of a B-tree leaf returns a key or garbage).
use std::collections::{BTreeMap, HashMap};
pub type Map = BTreeMap<u64, u64>;
pub type Hash = HashMap<u64, u64>;
#[inline(never)]
fn filled() -> Map {
    let mut m = Map::new();
    m.insert(10, 100);
    m.insert(30, 300);
    m.insert(50, 500);
    m
}
#[inline(never)]
fn filled_hash() -> Hash {
    let mut h = Hash::new();
    h.insert(10, 100);
    h.insert(30, 300);
    h.insert(50, 500);
    h
}
#[inline(never)]
pub fn plain() -> u64 {
    std::hint::black_box(99)
}
#[inline(never)]
pub fn with_hash(f: fn(&Hash) -> u64) -> u64 {
    let h = filled_hash();
    f(&h)
}
#[inline(never)]
pub fn with_pair(f: fn(&(Map, u64)) -> u64) -> u64 {
    let pair = (filled(), 7);
    f(&pair)
}
#[inline(never)]
pub fn with_map_mut(f: fn(&mut Map) -> u64) -> u64 {
    let mut m = filled();
    let r = f(&mut m);
    r * 10 + m.len() as u64
}
#[inline(never)]
pub fn own_hash(f: fn(Box<Hash>) -> u64) -> u64 {
    f(Box::new(filled_hash()))
}
#[inline(never)]
pub fn make_map() -> Box<Map> {
    Box::new(filled())
}
#[inline(never)]
pub fn make_hash() -> Box<Hash> {
    Box::new(filled_hash())
}
#[inline(never)]
pub fn make_pair() -> Box<(Map, u64)> {
    Box::new((filled(), 7))
}
#[inline(never)]
pub fn count(m: &Map) -> u64 {
    m.len() as u64 * 10 + m.get(&30).copied().unwrap_or(9)
}
#[inline(never)]
pub fn count_hash(h: &Hash) -> u64 {
    h.len() as u64 * 10 + h.get(&30).copied().unwrap_or(9)
}
#[inline(never)]
pub fn add_one(m: &mut Map) {
    m.insert(70, 700);
}
// --- functions NAMED like std's map constructors that are not std's ---
#[inline(never)]
pub fn new() -> Map {
    filled()
}
pub struct Reg;
impl Reg {
    #[inline(never)]
    pub fn with_capacity(_n: usize) -> Hash {
        filled_hash()
    }
}
// --- type-erased sinks: LLVM code downcasting what it is handed ---
#[inline(never)]
pub fn any_ref(a: &dyn std::any::Any) -> u64 {
    if let Some(m) = a.downcast_ref::<Map>() {
        return count(m);
    }
    if let Some(h) = a.downcast_ref::<Hash>() {
        return count_hash(h);
    }
    1
}
#[inline(never)]
pub fn any_box(b: Box<dyn std::any::Any>) -> u64 {
    let r = any_ref(&*b);
    drop(b);
    r
}
pub struct Bag<'a> {
    pub a: &'a dyn std::any::Any,
}
#[inline(never)]
pub fn bag(b: Bag<'_>) -> u64 {
    any_ref(b.a)
}
// --- drop glue: an LLVM `Drop` reading a map, and shared map glue ---
pub static OUT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub struct Peek<'a> {
    pub m: &'a Map,
}
impl Drop for Peek<'_> {
    fn drop(&mut self) {
        OUT.store(count(self.m) + 1000, std::sync::atomic::Ordering::SeqCst);
    }
}
#[inline(never)]
pub fn peek_self() -> u64 {
    let m = filled();
    {
        let _p = Peek { m: &m };
    }
    OUT.load(std::sync::atomic::Ordering::SeqCst)
}
#[inline(never)]
pub fn out() -> u64 {
    OUT.load(std::sync::atomic::Ordering::SeqCst)
}
#[inline(never)]
pub fn touch() -> u64 {
    let b: Box<dyn std::any::Any> = Box::new(filled());
    drop(b);
    filled().len() as u64
}
// --- a real `Entry` into a map this crate built ---
#[inline(never)]
pub fn leaked_entry() -> std::collections::btree_map::Entry<'static, u64, u64> {
    Box::leak(Box::new(filled())).entry(30)
}
#[inline(never)]
pub fn leaked_hash_entry() -> std::collections::hash_map::Entry<'static, u64, u64> {
    Box::leak(Box::new(filled_hash())).entry(30)
}
// --- a map's address handed over as an integer or an untyped pointer ---
#[inline(never)]
pub fn count_hash_at(addr: usize) -> u64 {
    count_hash(unsafe { &*(addr as *const Hash) })
}
#[inline(never)]
pub fn count_hash_bytes(bytes: &[u8]) -> u64 {
    count_hash(unsafe { &*(bytes.as_ptr() as *const Hash) })
}
#[inline(never)]
pub fn count_hash_in(slot: &[usize; 1]) -> u64 {
    count_hash(unsafe { &*(slot[0] as *const Hash) })
}
