#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a slot-modeled `BTreeMap` / `HashMap` the bridge did NOT
// construct must never be read, written or freed as the bridge's own slot
// image ([TCG-FOREIGN-MAP]).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE DEFECT. The bridge represents a `BTreeMap<int, int>` / `HashMap<int, int>`
// as a pointer to its own `{ptr,cap,len}` entry slot and lowers the map's
// methods (`len`, `get`, `insert`, `contains_key`, `remove`, `entry`, ...), the
// inlined `len()` field reads and the drop itself against that image. It
// decided "this is my image" from the map's TYPE. A map built by LLVM-compiled
// code — an upstream crate's function result, the argument an LLVM caller
// passes to a callback, a `static` — has rustc's real B-tree / hash-table
// layout, and the bridge read its first word (a root-node / control pointer)
// as a slot address. In the other direction a map the bridge built and handed
// to LLVM code was read by that code at rustc's layout. Every row below was
// compiled and RUN against the unpatched backend (origin/main f7a29670f,
// aarch64-apple-darwin; LLVM provider rlib, bridge consumer):
//
//   callback_hash_ref        O0/O1 exit 51 (LLVM 31)       — silent wrong value
//   callback_hash_dyn        O0/O1 exit 52 (LLVM 32)       — silent wrong value
//   callresult_box_len       O0/O1 exit 70 (LLVM 43)       — silent wrong value
//   callresult_hash_dyn      O0 exit 99, O1 exit 35 (LLVM 33)
//   callback_pair_get        O0..O3 SIGSEGV
//   callresult_box_get       O0..O3 SIGSEGV
//   callresult_pair_get, callresult_hash_box_len, callback_map_mut_insert
//                            O0/O1 SIGSEGV
//   callback_hash_box_drop   O0..O3 abort (free of a non-heap address)
//   static_map_len           O0 SIGSEGV
//   pass_map_ref             O0..O3 abort (LLVM `count` panics on the slot)
//   pass_hash_ref            O0 exit 9 (LLVM 23), O1/O3 hang, O2 SIGSEGV
//   pass_map_mut             O0/O1/O3 SIGSEGV, O2 abort
//   fnptr_foreign            O0/O1/O3 SIGSEGV, O2 abort
//
// ROUND 2 (origin/main 238e14a16, which carries the round-1 fix): five more
// ways a map crossed between the two layouts, each with rows below that state
// their measured outcome on that base: a constructor recognized by its NAME
// (`provider::new()` returning a filled map read `len() == 0`), a bridge map
// erased into `dyn Any` and downcast by LLVM code, drop glue compiled
// elsewhere (an LLVM `Drop` reading the map; a vtable drop slot bound to the
// provider's glue), an `Entry` record that outlived its local's value, an
// `Entry` whose variant a `match` read as a constant, and an `Entry` used
// other than by `or_insert*` (an arm's payload, `key()`, `mem::replace`).
// The `match_entry_variant_*` rows must now MATCH (the variant is read from
// the map), and the `foreign_box_dyn_provider_glue*` and
// `foreign_any_box_no_mint` rows pin what the new boundaries must keep: a map
// the provider built, destroyed by its glue or erased and handed back, in a
// crate that constructs no map of that kind.
//
// ROUND 3 (round 2's fix, 3080dc1bd): four more classes, each with rows below
// stating their outcome on that base: an `Entry` record that survived a loop
// back edge (every later iteration used the first entry), an aggregate of two
// entries that carried one record, an entry read after a join that merged an
// entry this function made with one LLVM code made (the read went to memory
// the intercepted `entry()` never wrote), and a map's address erased to an
// integer or an untyped pointer (a cast in a helper, a union field, a byte
// slice, a pointer forged from an integer buffer) and handed to LLVM code.
// Two more were found while fixing them: an entry carried onto a one-field
// wrapper whose field's variant, or whose `Drop` impl, read the wrapper's
// memory, which the carry never stored. The `entry_loop_rebind_own`,
// `entry_loop_match_hash`, `entry_join_two_own` and
// `entry_wrapper_field_variant` rows must now MATCH (the record of the path
// taken is read from the local's record cell; the variant from the map), and
// `box_dyn_over_local_map_dropped` pins what the erasure check must keep:
// std's own `Box` allocating and freeing a box over a map.
//
// The provider's keys (10/30/50) are chosen so that no misread can land on the
// right answer by coincidence: with keys 1/3/5 a B-tree leaf read as a slot
// returns key[1] == 3 == len, and such rows "matched" on the unpatched backend.
//
// THE ORACLE IS EXIT STATUS + STDOUT. Each program exits with its answer. The
// LLVM oracle is asserted against the expected value FIRST, so a row that
// measures something else says so instead of passing. The binaries run under
// macOS's `MallocScribble` / `MallocGuardEdges` / `MallocErrorAbort` (inert
// elsewhere) and under a deadline, so a hang is a failure, not a stuck test.
//
// VERDICTS. No cell may build and disagree with LLVM. A FOREIGN row may match
// (a future backend that lowers the real layout) or fail closed with a named
// [TCG-...] refusal; at the opt levels listed in `foreign_map_at` a refusal must
// be the provenance one, [TCG-FOREIGN-MAP], so an unrelated earlier gate cannot
// hide a lifted provenance check. The CONTROL row — maps this program builds
// and uses in one function, plus an ordinary cross-crate call — must build and
// match at every level: the receipts must not cost the supported shape.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes
// `no-proof-certs` (certificates refuse every AArch64 program with
// [TCG-PROOF-465], unrelated to this lane).

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const PROVIDER: &str = include_str!("support/foreign_map_provenance/provider.rs");
const FOREIGN_MAP: &str = "[TCG-FOREIGN-MAP]";
const ENTRY_USE: &str = "[TCG-MAP-ENTRY-USE]";
// Linux AArch64 refuses these calls before the helper can be scheduled from
// its caller. Keep these original programs as exact stable-address controls;
// exported copies below independently require the type-erasure guard itself.
#[cfg(all(
    target_os = "linux",
    target_arch = "aarch64",
    target_pointer_width = "64"
))]
const HELPER_CALL_REFUSAL: &[&str] = &["[TCG-REF-ARG-STORAGE]"];
#[cfg(not(all(
    target_os = "linux",
    target_arch = "aarch64",
    target_pointer_width = "64"
)))]
const HELPER_CALL_REFUSAL: &[&str] = &[FOREIGN_MAP];

const EXPORTED_HELPERS: [(&str, &str); 4] = [
    ("map_addr_cast_exported_helper", "map_addr_cast_in_helper"),
    ("map_addr_union_exported_helper", "map_addr_union_field"),
    ("map_bytes_exported_helper", "map_bytes_slice"),
    (
        "map_ref_exported_forged_pointer",
        "map_ref_written_through_forged_pointer",
    ),
];

const OPTS: [&str; 4] = ["0", "1", "2", "3"];

#[derive(Clone, Copy)]
struct Row<'a> {
    name: &'static str,
    src: &'a str,
    /// The exit code the LLVM oracle must produce.
    exit: i32,
    /// `None`: a control that must build and match at every level.
    /// `Some(levels)`: a foreign-provenance row; a refusal at one of `levels`
    /// must carry `refusal`.
    foreign_map_at: Option<&'static [&'static str]>,
    /// The named refusals (any one of them) the `foreign_map_at` levels
    /// require.
    refusal: &'static [&'static str],
    /// Levels at which a foreign row must BUILD and match LLVM: a capability
    /// a provenance check must not cost (a map built elsewhere and destroyed
    /// by the glue of the crate that built it).
    must_match_at: &'static [&'static str],
}

const ALL: &[&str] = &["0", "1", "2", "3"];
const LOW: &[&str] = &["0", "1"];
const NONE: &[&str] = &[];

const ROWS: &[Row<'static>] = &[
    // --- an LLVM caller hands a callback its real map (`&`, `&mut`, `Box`) ---
    Row {
        name: "callback_hash_ref",
        src: r#"extern crate provider;
#[inline(never)]
fn f(h: &provider::Hash) -> u64 {
    h.len() as u64 * 10 + 1
}
fn main() {
    std::process::exit(provider::with_hash(f) as i32);
}
"#,
        exit: 31,
        foreign_map_at: Some(LOW),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callback_hash_dyn",
        src: r#"extern crate provider;
trait Tr {
    fn n(&self) -> u64;
}
impl Tr for provider::Hash {
    #[inline(never)]
    fn n(&self) -> u64 {
        self.len() as u64 * 10 + 2
    }
}
#[inline(never)]
fn f(h: &provider::Hash) -> u64 {
    let d: &dyn Tr = h;
    d.n()
}
fn main() {
    std::process::exit(provider::with_hash(f) as i32);
}
"#,
        exit: 32,
        foreign_map_at: Some(LOW),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callback_pair_get",
        src: r#"extern crate provider;
#[inline(never)]
fn f(pair: &(provider::Map, u64)) -> u64 {
    pair.0.get(&30).copied().unwrap_or(770) / 10 + pair.1
}
fn main() {
    std::process::exit(provider::with_pair(f) as i32);
}
"#,
        exit: 37,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callback_map_mut_insert",
        src: r#"extern crate provider;
#[inline(never)]
fn f(m: &mut provider::Map) -> u64 {
    m.insert(9, 9);
    m.len() as u64
}
fn main() {
    std::process::exit(provider::with_map_mut(f) as i32);
}
"#,
        exit: 44,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callback_hash_box_drop",
        src: r#"extern crate provider;
#[inline(never)]
fn f(b: Box<provider::Hash>) -> u64 {
    drop(b);
    5
}
fn main() {
    std::process::exit(provider::own_hash(f) as i32);
}
"#,
        exit: 5,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- an LLVM function returns its real map (boxed, or in a pair) ---
    Row {
        name: "callresult_box_get",
        src: r#"extern crate provider;
fn main() {
    let b = provider::make_map();
    std::process::exit((b.get(&30).copied().unwrap_or(770) / 10) as i32);
}
"#,
        exit: 30,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callresult_box_len",
        src: r#"extern crate provider;
fn main() {
    let b = provider::make_map();
    std::process::exit(b.len() as i32 + 40);
}
"#,
        exit: 43,
        foreign_map_at: Some(LOW),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callresult_hash_box_len",
        src: r#"extern crate provider;
fn main() {
    let b = provider::make_hash();
    std::process::exit(b.len() as i32 * 10 + b.contains_key(&30) as i32);
}
"#,
        exit: 31,
        foreign_map_at: Some(LOW),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callresult_hash_dyn",
        src: r#"extern crate provider;
trait Tr {
    fn n(&self) -> u64;
}
impl Tr for provider::Hash {
    #[inline(never)]
    fn n(&self) -> u64 {
        self.len() as u64 * 10 + 3
    }
}
fn main() {
    let b = provider::make_hash();
    let d: Box<dyn Tr> = b;
    let r = d.n();
    drop(d);
    std::process::exit(r as i32);
}
"#,
        exit: 33,
        foreign_map_at: Some(LOW),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "callresult_pair_get",
        src: r#"extern crate provider;
trait Tr {
    fn n(&self) -> u64;
}
impl Tr for (provider::Map, u64) {
    #[inline(never)]
    fn n(&self) -> u64 {
        self.0.get(&30).copied().unwrap_or(770) / 10 + self.1
    }
}
fn main() {
    let b = provider::make_pair();
    let d: Box<dyn Tr> = b;
    let r = d.n();
    drop(d);
    std::process::exit(r as i32);
}
"#,
        exit: 37,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- a const-evaluated `static` has rustc's layout too ---
    Row {
        name: "static_map_len",
        src: r#"extern crate provider;
static M: provider::Map = provider::Map::new();
fn main() {
    std::process::exit(M.len() as i32 + std::hint::black_box(6));
}
"#,
        exit: 6,
        foreign_map_at: Some(&["0"]),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- the other direction: a map this program built reaches LLVM code ---
    Row {
        name: "pass_map_ref",
        src: r#"extern crate provider;
fn main() {
    let mut m = provider::Map::new();
    m.insert(std::hint::black_box(10), 1);
    m.insert(30, 2);
    std::process::exit(provider::count(&m) as i32);
}
"#,
        exit: 22,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "pass_hash_ref",
        src: r#"extern crate provider;
fn main() {
    let mut h = provider::Hash::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    std::process::exit(provider::count_hash(&h) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "pass_map_mut",
        src: r#"extern crate provider;
fn main() {
    let mut m = provider::Map::new();
    m.insert(std::hint::black_box(10), 1);
    provider::add_one(&mut m);
    std::process::exit(m.len() as i32 + 50);
}
"#,
        exit: 52,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "fnptr_foreign",
        src: r#"extern crate provider;
fn main() {
    let mut m = provider::Map::new();
    m.insert(std::hint::black_box(30), 4);
    let g: fn(&provider::Map) -> u64 = provider::count;
    std::process::exit(g(&m) as i32);
}
"#,
        exit: 14,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- round 2: the construction receipt is minted by callee IDENTITY ---
    // A function NAMED like std's constructor, returning a FILLED map, was
    // replaced by an empty bridge slot (base: exit 40 / 30 / 25 at every
    // level where LLVM exits 43 / 33 / 27).
    Row {
        name: "spoof_new",
        src: r#"extern crate provider;
fn main() {
    let m = provider::new();
    std::process::exit(m.len() as i32 + 40);
}
"#,
        exit: 43,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "spoof_assoc_with_capacity_hash",
        src: r#"extern crate provider;
fn main() {
    let h = provider::Reg::with_capacity(3);
    std::process::exit(h.len() as i32 + 30);
}
"#,
        exit: 33,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "spoof_local_new",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
struct Cfg;
impl Cfg {
    #[inline(never)]
    fn new() -> BTreeMap<u64, u64> {
        let mut m = BTreeMap::new();
        m.insert(std::hint::black_box(1), 2);
        m.insert(3, 4);
        m
    }
}
fn main() {
    let m = Cfg::new();
    std::process::exit(m.len() as i32 + 25 + (provider::plain() as i32 - 99));
}
"#,
        exit: 27,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // `HashMap`'s `RandomState` construction step is modeled as dead: a call
    // to a non-std function returning one was DROPPED, with its effects
    // (base: exit 1 at every level where LLVM exits 8).
    Row {
        name: "user_hasher_fn",
        src: r#"extern crate provider;
use std::collections::HashMap;
use std::hash::RandomState;
use std::sync::atomic::{AtomicU64, Ordering};
static N: AtomicU64 = AtomicU64::new(0);
#[inline(never)]
fn mk() -> RandomState {
    N.fetch_add(7, Ordering::SeqCst);
    RandomState::new()
}
fn main() {
    let mut h: HashMap<u64, u64, RandomState> = HashMap::with_hasher(mk());
    h.insert(std::hint::black_box(1), 2);
    std::process::exit((h.len() as u64 + N.load(Ordering::SeqCst) + provider::plain() - 99) as i32);
}
"#,
        exit: 8,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- round 2: a bridge-built map erased into a trait object ---
    // The provider downcasts the `dyn Any` and reads the slot image as a real
    // map (base: `any_ref_hash` hangs at -O0/-O1, `bag_any_hash` SIGSEGV at
    // -O0/-O1, `any_box_empty_map` SIGABRT at -O2/-O3).
    Row {
        name: "any_ref_hash",
        src: r#"extern crate provider;
use std::collections::HashMap;
fn main() {
    let mut h = HashMap::<u64, u64>::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    std::process::exit(provider::any_ref(&h) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "any_box_empty_map",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let b: Box<dyn std::any::Any> = Box::new(BTreeMap::<u64, u64>::new());
    std::process::exit(provider::any_box(b) as i32);
}
"#,
        exit: 9,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "bag_any_hash",
        src: r#"extern crate provider;
use std::collections::HashMap;
fn main() {
    let mut h = HashMap::<u64, u64>::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    std::process::exit(provider::bag(provider::Bag { a: &h }) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- round 2: drop glue is a code boundary ---
    // The provider's LLVM `drop_glue::<Peek>` runs `Peek::drop`, reading the
    // bridge's slot as a real map (shared generics; base: SIGABRT at
    // -O0/-O1).
    Row {
        name: "drop_guard_peek",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let s = provider::peek_self();
    let m = BTreeMap::<u64, u64>::new();
    {
        let _p = provider::Peek { m: &m };
    }
    std::process::exit((provider::out() - 1000) as i32 + (s % 7) as i32);
}
"#,
        exit: 9,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // The vtable's drop slot bound the provider's `drop_glue::<BTreeMap>`
    // (shared generics; base: SIGSEGV at -O0/-O1); at -O2/-O3 the glue is this
    // crate's own and the row matches.
    Row {
        name: "vtable_drop_slot_upstream_glue",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
trait Tr {
    fn n(&self) -> u64 {
        5
    }
}
impl Tr for BTreeMap<u64, u64> {}
fn main() {
    let t = provider::touch();
    let b: Box<dyn Tr> = Box::new(BTreeMap::<u64, u64>::new());
    let n = b.n();
    drop(b);
    std::process::exit((n + t % 2) as i32);
}
"#,
        exit: 6,
        foreign_map_at: Some(LOW),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- round 2: an `Entry` record must not outlive its local's value ---
    // `or_insert` ran on the bridge's own map instead of the reassigned
    // provider entry (base: exit 10 at every level where LLVM exits 3).
    Row {
        name: "entry_stale_record",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    let mut e = m.entry(std::hint::black_box(1));
    e = provider::leaked_entry();
    let v = *e.or_insert(5);
    std::process::exit((v / 100 + m.len() as u64 * 10) as i32);
}
"#,
        exit: 3,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "entry_stale_record_hash",
        src: r#"extern crate provider;
use std::collections::HashMap;
fn main() {
    let mut m = HashMap::<u64, u64>::new();
    let mut e = m.entry(std::hint::black_box(1));
    e = provider::leaked_hash_entry();
    let v = *e.or_insert(5);
    std::process::exit((v / 100 + m.len() as u64 * 10) as i32);
}
"#,
        exit: 3,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "entry_overwritten_through_borrow",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    let mut e = m.entry(std::hint::black_box(1));
    {
        let p = &mut e;
        *p = provider::leaked_entry();
    }
    let v = *e.or_insert(5);
    std::process::exit((v / 100 + m.len() as u64 * 10) as i32);
}
"#,
        exit: 3,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP, ENTRY_USE],
        must_match_at: NONE,
    },
    // `mem::replace(&mut e, ..)` hands the unmaterialized entry's address to
    // `replace` (base: exit 10 at every level where LLVM exits 3).
    Row {
        name: "entry_mem_replace",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    let mut e = m.entry(std::hint::black_box(1));
    let _old = std::mem::replace(&mut e, provider::leaked_entry());
    let v = *e.or_insert(5);
    std::process::exit((v / 100 + m.len() as u64 * 10) as i32);
}
"#,
        exit: 3,
        foreign_map_at: Some(ALL),
        refusal: &[ENTRY_USE, FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- round 2: any other use of an entry (the bridge never builds it) ---
    // `Entry::key` reads the entry through `&e` (base: exit 10 at -O0/-O1
    // where LLVM exits 17). An arm reading the payload of a `match` on the
    // entry (base: `match_entry_btree` SIGABRT, `match_entry_hash` exit 1
    // where LLVM exits 30, both at -O0/-O1).
    Row {
        name: "entry_key_read",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(3), 30);
    let k = *m.entry(std::hint::black_box(7)).key();
    std::process::exit((k + m.len() as u64 * 10) as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 17,
        foreign_map_at: Some(ALL),
        refusal: &[ENTRY_USE],
        must_match_at: NONE,
    },
    Row {
        name: "match_entry_btree",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(3), 30);
    let r = match m.entry(std::hint::black_box(3)) {
        Entry::Occupied(o) => *o.get(),
        Entry::Vacant(_) => 1,
    };
    std::process::exit(r as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 30,
        foreign_map_at: Some(ALL),
        refusal: &[ENTRY_USE],
        must_match_at: NONE,
    },
    Row {
        name: "match_entry_hash",
        src: r#"extern crate provider;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
fn main() {
    let mut m = HashMap::<u64, u64>::new();
    m.insert(std::hint::black_box(3), 30);
    let r = match m.entry(std::hint::black_box(3)) {
        Entry::Occupied(o) => *o.get(),
        Entry::Vacant(_) => 1,
    };
    std::process::exit(r as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 30,
        foreign_map_at: Some(ALL),
        refusal: &[ENTRY_USE],
        must_match_at: NONE,
    },
    // --- round 2: an entry's VARIANT is a fact about the map ---
    // The bridge never builds the `Entry`, so a `match` on it took a constant
    // arm (the Vacant index of `hash_map::Entry`, the Occupied index of
    // `btree_map::Entry`): base exit 1 / 30 / 207 at every level where LLVM
    // exits 30 / 2 / 217 (at -O2/-O3 the user match is threaded through std's
    // own `RustcEntry` diamond). The variant is `Occupied` exactly when the
    // key is present, so these must build and MATCH at every level.
    Row {
        name: "match_entry_variant_only_hash",
        src: r#"extern crate provider;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
fn main() {
    let mut m = HashMap::<u64, u64>::new();
    m.insert(std::hint::black_box(3), 30);
    let r = match m.entry(std::hint::black_box(3)) {
        Entry::Occupied(_) => 30,
        Entry::Vacant(_) => 1,
    };
    std::process::exit(r + (provider::plain() as i32 - 99));
}
"#,
        exit: 30,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    Row {
        name: "match_entry_variant_only_btree_absent",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(3), 30);
    let r = match m.entry(std::hint::black_box(4)) {
        Entry::Occupied(_) => 30,
        Entry::Vacant(_) => 2,
    };
    std::process::exit(r + (provider::plain() as i32 - 99));
}
"#,
        exit: 2,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    Row {
        name: "matches_entry_then_or_insert_hash",
        src: r#"extern crate provider;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
fn main() {
    let mut m = HashMap::<u64, u64>::new();
    m.insert(std::hint::black_box(3), 30);
    let present = matches!(m.entry(std::hint::black_box(3)), Entry::Occupied(_));
    let v = *m.entry(std::hint::black_box(5)).or_insert(7);
    let r = present as u64 * 10 + v + m.len() as u64 * 100;
    std::process::exit(r as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 217,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    // --- capability: a map built ELSEWHERE, destroyed by its builder's glue ---
    // This crate constructs no map of the family, so the vtable's drop slot
    // binding the provider's shared `drop_glue::<(BTreeMap, u64)>` /
    // `drop_glue::<HashMap>` (-O0/-O1) frees a real map at its real layout.
    // The drop-glue boundary must not refuse it (both match on base).
    Row {
        name: "foreign_box_dyn_provider_glue",
        src: r#"extern crate provider;
trait Tr {
    fn n(&self) -> u64;
}
impl Tr for (provider::Map, u64) {
    #[inline(never)]
    fn n(&self) -> u64 {
        self.1 - 1
    }
}
fn main() {
    let d: Box<dyn Tr> = provider::make_pair();
    let r = d.n();
    drop(d);
    std::process::exit((r + provider::plain() - 99) as i32);
}
"#,
        exit: 6,
        foreign_map_at: Some(NONE),
        refusal: &[FOREIGN_MAP],
        must_match_at: LOW,
    },
    Row {
        name: "foreign_box_dyn_provider_glue_hash",
        src: r#"extern crate provider;
trait Tr {
    fn n(&self) -> u64;
}
impl Tr for provider::Hash {
    #[inline(never)]
    fn n(&self) -> u64 {
        7
    }
}
fn main() {
    let d: Box<dyn Tr> = provider::make_hash();
    let r = d.n();
    drop(d);
    std::process::exit((r + provider::plain() - 99) as i32);
}
"#,
        exit: 7,
        foreign_map_at: Some(NONE),
        refusal: &[FOREIGN_MAP],
        must_match_at: LOW,
    },
    // --- capability: a map built ELSEWHERE, erased and handed back ---
    // This crate constructs no `HashMap`, so the provider's real map coerced to
    // `Box<dyn Any>` holds no slot image, and the erasure survey must not make
    // the `dyn Any` it crosses back as look like one (matches on base).
    Row {
        name: "foreign_any_box_no_mint",
        src: r#"extern crate provider;
fn main() {
    let b: Box<dyn std::any::Any> = provider::make_hash();
    std::process::exit((provider::any_box(b) % 100) as i32);
}
"#,
        exit: 30,
        foreign_map_at: Some(NONE),
        refusal: &[FOREIGN_MAP],
        must_match_at: LOW,
    },
    // --- round 3: an `Entry` record across a loop back edge ---
    // The back edge is lowered after the header, so the entry edge's record
    // survived it and every later iteration used the FIRST entry (base: exit
    // 30 / 3 at every level where LLVM exits 80 / 1). A loop that rebinds the
    // local to entries of maps this function built must now MATCH (the
    // record of the path taken is in the local's record cell); one that
    // rebinds it to an entry LLVM code made must refuse (base: exit 33 / 0
    // where LLVM exits 31 / 20).
    Row {
        name: "entry_loop_rebind_own",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut a = BTreeMap::<u64, u64>::new();
    a.insert(1, 10);
    let mut b = BTreeMap::<u64, u64>::new();
    let mut e = a.entry(std::hint::black_box(1));
    let mut total = 0;
    for i in 0..3u64 {
        total += *e.or_insert(5);
        e = b.entry(10 + i);
    }
    let r = total + b.len() as u64 * 30;
    std::process::exit(r as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 80,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    Row {
        name: "entry_loop_match_hash",
        src: r#"extern crate provider;
use std::collections::hash_map::{Entry, HashMap};
fn main() {
    let mut a = HashMap::<u64, u64>::new();
    a.insert(1, 10);
    let mut b = HashMap::<u64, u64>::new();
    let mut e = a.entry(std::hint::black_box(1));
    let mut occupied = 0;
    for i in 0..3u64 {
        if let Entry::Occupied(_) = e {
            occupied += 1;
        }
        e = b.entry(10 + i);
    }
    let _ = &e;
    std::process::exit(occupied + (provider::plain() as i32 - 99));
}
"#,
        exit: 1,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    Row {
        name: "entry_loop_rebind_foreign",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(1), 10);
    let mut e = m.entry(std::hint::black_box(1));
    let mut total = 0u64;
    let mut i = 0u64;
    loop {
        total += *e.or_insert(5) % 97;
        i += 1;
        if i == std::hint::black_box(3) {
            break;
        }
        e = provider::leaked_entry();
    }
    std::process::exit((total + m.len() as u64 * 3) as i32);
}
"#,
        exit: 31,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "entry_loop_variant_foreign",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    let mut e = m.entry(std::hint::black_box(1));
    let mut occupied = 0u64;
    for _ in 0..std::hint::black_box(3u64) {
        if let Entry::Occupied(_) = e {
            occupied += 1;
        }
        e = provider::leaked_entry();
    }
    let _ = &e;
    std::process::exit((occupied * 10) as i32);
}
"#,
        exit: 20,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP, ENTRY_USE],
        must_match_at: NONE,
    },
    // --- round 3: an aggregate of two entries carried ONE record ---
    // A carry kept the last recorded operand of the tuple, and a field read
    // of it copied that record, so both `or_insert`s ran on `b` (base: exit
    // 10 / 15 at -O0 where LLVM exits 16 / 18). The tuple is gone from the
    // MIR above -O0, where each entry keeps its own record and must match.
    Row {
        name: "entry_tuple_two_own",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut a = BTreeMap::<u64, u64>::new();
    a.insert(1, 10);
    let mut b = BTreeMap::<u64, u64>::new();
    let (x, y) = (a.entry(std::hint::black_box(1)), b.entry(2));
    let x = *x.or_insert(5);
    let y = *y.or_insert(6);
    std::process::exit((x + y) as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 16,
        foreign_map_at: Some(&["0"]),
        refusal: &[ENTRY_USE],
        must_match_at: &["1", "2", "3"],
    },
    Row {
        name: "entry_tuple_own_foreign",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    let (a, b) = (m.entry(std::hint::black_box(1)), provider::leaked_entry());
    let x = *a.or_insert(5);
    let y = *b.or_insert(6);
    std::process::exit((x + y / 100 + m.len() as u64 * 10) as i32);
}
"#,
        exit: 18,
        foreign_map_at: Some(ALL),
        refusal: &[ENTRY_USE, FOREIGN_MAP],
        must_match_at: NONE,
    },
    // --- round 3: an entry read where the paths into a join disagree ---
    // A join of an own entry and an entry LLVM code made dropped the record,
    // and the read then went to memory the intercepted `entry()` never wrote
    // (base: exit 41 at every level where LLVM exits 40; the arm's payload
    // read 1, 105 or SIGSEGV where LLVM reads 20). A join of two entries of
    // maps this function built must MATCH (base refused it).
    Row {
        name: "entry_join_own_or_foreign_variant",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(2), 20);
    let e = if std::hint::black_box(true) {
        m.entry(std::hint::black_box(2))
    } else {
        provider::leaked_entry()
    };
    std::process::exit(matches!(e, Entry::Vacant(_)) as i32 + 40);
}
"#,
        exit: 40,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "entry_join_own_or_foreign_payload",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(2), 20);
    let e = if std::hint::black_box(true) {
        m.entry(std::hint::black_box(2))
    } else {
        provider::leaked_entry()
    };
    let r = match e {
        Entry::Occupied(o) => *o.get(),
        Entry::Vacant(_) => 1,
    };
    std::process::exit(r as i32);
}
"#,
        exit: 20,
        foreign_map_at: Some(ALL),
        refusal: &[FOREIGN_MAP],
        must_match_at: NONE,
    },
    Row {
        name: "entry_join_two_own",
        src: r#"extern crate provider;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
fn main() {
    let mut a = HashMap::<u64, u64>::new();
    a.insert(1, 10);
    let mut b = HashMap::<u64, u64>::new();
    let pick_a = std::hint::black_box(false);
    let e = if pick_a { a.entry(std::hint::black_box(1)) } else { b.entry(std::hint::black_box(2)) };
    let r = match e {
        Entry::Occupied(_) => 30,
        Entry::Vacant(_) => 7,
    };
    let f = if pick_a { a.entry(std::hint::black_box(1)) } else { b.entry(std::hint::black_box(2)) };
    let v = *f.or_insert(5);
    let s = r + v + a.len() as u64 * 20 + b.len() as u64 * 40;
    std::process::exit(s as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 72,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    // --- round 3: an entry carried onto a one-field wrapper ---
    // The carry stores nothing, so the wrapper's memory holds no entry. A
    // variant read through the wrapper's field went to that memory (base:
    // exit 2 at -O0 where LLVM exits 31); it is the entry itself and must
    // MATCH at every level (the variant is read from the map). The drop glue
    // of a wrapper with a `Drop` impl read the same memory (base: exit 2 at
    // every level where LLVM exits 31) and must refuse.
    Row {
        name: "entry_wrapper_field_variant",
        src: r#"extern crate provider;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
struct W<'a>(Entry<'a, u64, u64>);
fn main() {
    let mut m = BTreeMap::<u64, u64>::new();
    m.insert(std::hint::black_box(1), 10);
    let w = W(m.entry(std::hint::black_box(1)));
    let r = match w.0 {
        Entry::Occupied(_) => 30,
        Entry::Vacant(_) => 1,
    };
    std::process::exit(r + m.len() as i32 + (provider::plain() as i32 - 99));
}
"#,
        exit: 31,
        foreign_map_at: Some(NONE),
        refusal: &[ENTRY_USE],
        must_match_at: ALL,
    },
    Row {
        name: "entry_wrapper_drop_glue",
        src: r#"extern crate provider;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::sync::atomic::{AtomicU64, Ordering};
static OUT: AtomicU64 = AtomicU64::new(0);
struct W<'a>(Entry<'a, u64, u64>);
impl Drop for W<'_> {
    fn drop(&mut self) {
        let v = if let Entry::Occupied(_) = self.0 { 30 } else { 1 };
        OUT.store(v, Ordering::SeqCst);
    }
}
fn main() {
    let mut m = HashMap::<u64, u64>::new();
    m.insert(std::hint::black_box(1), 10);
    {
        let _w = W(m.entry(std::hint::black_box(1)));
    }
    let r = OUT.load(Ordering::SeqCst) as i32 + m.len() as i32;
    std::process::exit(r + (provider::plain() as i32 - 99));
}
"#,
        exit: 31,
        foreign_map_at: Some(ALL),
        refusal: &[ENTRY_USE],
        must_match_at: NONE,
    },
    // --- round 3: a map's address erased to an integer or untyped pointer ---
    // In a helper (only casts written in `main` refused, by unrelated gates),
    // through a union, as a byte slice, and written through a pointer forged
    // from an integer buffer, then handed to LLVM code that reads it back as
    // a map (base: 9, SIGSEGV or a hang where LLVM gives 23).
    Row {
        name: "map_addr_cast_in_helper",
        src: r#"extern crate provider;
use std::collections::HashMap;
#[inline(never)]
fn launder(h: &HashMap<u64, u64>) -> usize {
    h as *const HashMap<u64, u64> as usize
}
fn main() {
    let mut h = HashMap::<u64, u64>::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    std::process::exit(provider::count_hash_at(launder(&h)) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: HELPER_CALL_REFUSAL,
        must_match_at: NONE,
    },
    Row {
        name: "map_addr_union_field",
        src: r#"extern crate provider;
use std::collections::HashMap;
union U<'a> {
    r: &'a HashMap<u64, u64>,
    n: usize,
}
#[inline(never)]
fn launder(h: &HashMap<u64, u64>) -> usize {
    unsafe { U { r: h }.n }
}
fn main() {
    let mut h = HashMap::<u64, u64>::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    std::process::exit(provider::count_hash_at(launder(&h)) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: HELPER_CALL_REFUSAL,
        must_match_at: NONE,
    },
    Row {
        name: "map_bytes_slice",
        src: r#"extern crate provider;
use std::collections::HashMap;
#[inline(never)]
fn bytes(h: &HashMap<u64, u64>) -> &[u8] {
    let n = std::mem::size_of::<HashMap<u64, u64>>();
    unsafe { std::slice::from_raw_parts(h as *const HashMap<u64, u64> as *const u8, n) }
}
fn main() {
    let mut h = HashMap::<u64, u64>::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    std::process::exit(provider::count_hash_bytes(bytes(&h)) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: HELPER_CALL_REFUSAL,
        must_match_at: NONE,
    },
    Row {
        name: "map_ref_written_through_forged_pointer",
        src: r#"extern crate provider;
use std::collections::HashMap;
#[inline(never)]
fn stash(slot: &mut [usize; 1], h: &HashMap<u64, u64>) {
    unsafe { *(slot.as_mut_ptr() as *mut &HashMap<u64, u64>) = h };
}
fn main() {
    let mut h = HashMap::<u64, u64>::new();
    h.insert(std::hint::black_box(10), 1);
    h.insert(30, 3);
    let mut slot = [0usize; 1];
    stash(&mut slot, &h);
    std::process::exit(provider::count_hash_in(&slot) as i32);
}
"#,
        exit: 23,
        foreign_map_at: Some(ALL),
        refusal: HELPER_CALL_REFUSAL,
        must_match_at: NONE,
    },
    // --- capability: std's own `Box` allocates and frees a box over a map ---
    // `Box::new` makes a `*mut T` of the allocator's `*mut u8`, and `<Box<T>
    // as Drop>::drop` hands the `*mut u8` of the box back to it: neither
    // lets the map leave as an integer, so the erasure check must not refuse
    // them (matches on base at every level). No provider crate is loaded, so
    // the box's drop glue is this crate's own.
    Row {
        name: "box_dyn_over_local_map_dropped",
        src: r#"use std::collections::BTreeMap;
trait Tr {
    fn n(&self) -> u64 {
        5
    }
}
impl Tr for BTreeMap<u64, u64> {}
fn main() {
    let b: Box<dyn Tr> = Box::new(BTreeMap::<u64, u64>::new());
    let r = b.n();
    drop(b);
    std::process::exit((r + 6) as i32);
}
"#,
        exit: 11,
        foreign_map_at: Some(NONE),
        refusal: &[FOREIGN_MAP],
        must_match_at: ALL,
    },
    // --- control: maps built and used in one function stay intercepted ---
    Row {
        name: "control_local_maps",
        src: r#"extern crate provider;
use std::collections::{BTreeMap, HashMap};
use std::hint::black_box;
fn main() {
    let n = black_box(6u64);
    let mut b = BTreeMap::<u64, u64>::new();
    let mut h = HashMap::<u64, u64>::new();
    for i in 0..n {
        b.insert(i, i * 3);
        h.insert(i * 2, i);
        *b.entry(i % 2).or_insert(0) += 1;
    }
    let removed = b.remove(&4).unwrap_or(0);
    let mut sum = 0;
    for i in 0..n {
        sum += b.get(&i).copied().unwrap_or(0);
        if h.contains_key(&i) {
            sum += h.get(&i).copied().unwrap_or(0);
        }
    }
    let r = sum + removed + b.len() as u64 * 10 + h.len() as u64 + provider::plain();
    std::process::exit((r % 256) as i32);
}
"#,
        exit: 209,
        foreign_map_at: None,
        refusal: &[FOREIGN_MAP],
        must_match_at: ALL,
    },
];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_foreign_map_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The bridge's named refusal tag, if `stderr` is a fail-closed refusal rather
/// than a crash. An ICE, a panic, or a refusal with no `[TCG-...]` tag is not.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Exit(i32, String),
    Signal(i32),
    Hung,
}

/// Run `bin` under the macOS malloc checks with a deadline.
fn run(bin: &Path) -> Outcome {
    let mut child = Command::new(bin)
        .env("MallocScribble", "1")
        .env("MallocGuardEdges", "1")
        .env("MallocErrorAbort", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn compiled binary");
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().expect("poll compiled binary") {
            let mut stdout = String::new();
            if let Some(mut pipe) = child.stdout.take() {
                use std::io::Read;
                let _ = pipe.read_to_string(&mut stdout);
            }
            if let Some(code) = status.code() {
                return Outcome::Exit(code, stdout.trim().to_owned());
            }
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt;
                if let Some(signal) = status.signal() {
                    return Outcome::Signal(signal);
                }
            }
            return Outcome::Signal(-1);
        }
        if start.elapsed() > Duration::from_secs(30) {
            let _ = child.kill();
            let _ = child.wait();
            return Outcome::Hung;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn compile(
    dir: &Path,
    provider: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (std::process::Output, PathBuf) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write consumer source");
    let bin = dir.join(name);
    let _ = std::fs::remove_file(&bin);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-L")
        .arg(dir);
    let mut extern_arg = std::ffi::OsString::from("provider=");
    extern_arg.push(provider);
    cmd.arg("--extern").arg(extern_arg);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    (cmd.output().expect("spawn the compiler"), bin)
}

#[test]
fn foreign_maps_refuse_and_local_maps_match_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "foreign_maps_refuse_and_local_maps_match_llvm",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("diff");

    // The provider is LLVM-compiled: every map it builds has rustc's layout.
    let provider_src = dir.join("provider.rs");
    std::fs::write(&provider_src, PROVIDER).expect("write provider");
    let provider = dir.join("libprovider.rlib");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "provider"])
        .args(["-Cpanic=abort", "-Ccodegen-units=1", "-Copt-level=0"])
        .arg("-o")
        .arg(&provider)
        .arg(&provider_src);
    let out = cmd.output().expect("spawn the compiler");
    assert!(
        out.status.success(),
        "the LLVM provider did not build: <<<{}>>>",
        String::from_utf8_lossy(&out.stderr)
    );

    // Exporting makes the exact same helper a mono-item root. Its body is
    // checked even if a caller has already failed the stable-address guard.
    // Preserve every original source byte and add only the export attribute.
    let exported_bases: Vec<_> = EXPORTED_HELPERS
        .iter()
        .map(|(_, original)| {
            ROWS.iter()
                .find(|row| row.name == *original)
                .expect("original helper row")
        })
        .collect();
    let exported_sources: Vec<_> = exported_bases
        .iter()
        .map(|row| {
            assert_eq!(row.src.matches("#[inline(never)]").count(), 1);
            row.src
                .replacen("#[inline(never)]", "#[no_mangle]\n#[inline(never)]", 1)
        })
        .collect();
    let mut rows = ROWS.to_vec();
    for (((name, _), original), src) in EXPORTED_HELPERS
        .iter()
        .zip(&exported_bases)
        .zip(&exported_sources)
    {
        rows.push(Row {
            name,
            src,
            exit: original.exit,
            foreign_map_at: Some(ALL),
            refusal: &[FOREIGN_MAP],
            must_match_at: NONE,
        });
    }
    assert_eq!(ROWS.len() * OPTS.len(), 216, "retain every original cell");
    assert_eq!(
        rows.len() * OPTS.len(),
        232,
        "include sixteen exported guard witnesses"
    );

    let mut failures = Vec::new();
    let (mut cells, mut matched, mut refused, mut foreign_named, mut controls) = (0, 0, 0, 0, 0);
    let (mut entry_use_named, mut kept) = (0, 0);
    for row in &rows {
        for opt in OPTS {
            cells += 1;
            let (out, bin) = compile(
                &dir,
                &provider,
                &format!("{}_o{opt}_llvm", row.name),
                row.src,
                None,
                opt,
            );
            assert!(
                out.status.success(),
                "LLVM compile of `{}` failed at -O{opt}: <<<{}>>>",
                row.name,
                String::from_utf8_lossy(&out.stderr)
            );
            let oracle = run(&bin);
            assert_eq!(
                oracle,
                Outcome::Exit(row.exit, String::new()),
                "the LLVM oracle for `{}` at -O{opt} is not the row's answer; this row \
                 measures something else",
                row.name
            );
            let (out, bin) = compile(
                &dir,
                &provider,
                &format!("{}_o{opt}_tcg", row.name),
                row.src,
                Some(&dylib),
                opt,
            );
            if out.status.success() && bin.exists() {
                let ran = run(&bin);
                if ran == oracle {
                    matched += 1;
                    controls += usize::from(row.foreign_map_at.is_none());
                    kept += usize::from(
                        row.foreign_map_at.is_some() && row.must_match_at.contains(&opt),
                    );
                } else {
                    failures.push(format!(
                        "-O{opt} `{}`: trust-cg binary DISAGREES with LLVM: {ran:?} vs \
                         {oracle:?} — a map crossed between the bridge's slot image and \
                         rustc's real layout",
                        row.name
                    ));
                }
                continue;
            }
            let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
            let Some(tag) = named_refusal(&stderr) else {
                failures.push(format!(
                    "-O{opt} `{}`: trust-cg failed WITHOUT a named [TCG-...] refusal: <<<{}>>>",
                    row.name,
                    stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                ));
                continue;
            };
            if row.foreign_map_at.is_some() && row.must_match_at.contains(&opt) {
                failures.push(format!(
                    "-O{opt} `{}`: REFUSED ({tag}), but this cell must build and match: a \
                     capability the map checks must keep (a map read from the map itself, or \
                     built elsewhere and destroyed or handed back there) is lost: <<<{}>>>",
                    row.name,
                    stderr
                        .lines()
                        .filter(|l| l.contains(" - "))
                        .take(3)
                        .collect::<Vec<_>>()
                        .join(" | ")
                ));
                continue;
            }
            match row.foreign_map_at {
                None => failures.push(format!(
                    "-O{opt} `{}`: the control REFUSED ({tag}) — maps a function builds and \
                     uses itself must stay intercepted: <<<{}>>>",
                    row.name,
                    stderr
                        .lines()
                        .filter(|l| l.contains(" - "))
                        .take(3)
                        .collect::<Vec<_>>()
                        .join(" | ")
                )),
                Some(levels)
                    if levels.contains(&opt)
                        && !row.refusal.iter().any(|tag| stderr.contains(tag)) =>
                {
                    failures.push(format!(
                        "-O{opt} `{}`: refused, but not by {}: an earlier gate now decides \
                         this cell, so a lifted provenance check would go unseen: <<<{}>>>",
                        row.name,
                        row.refusal.join(" / "),
                        stderr
                            .lines()
                            .filter(|l| l.contains(" - "))
                            .take(3)
                            .collect::<Vec<_>>()
                            .join(" | ")
                    ))
                }
                Some(_) => {
                    refused += 1;
                    foreign_named += usize::from(stderr.contains(FOREIGN_MAP));
                    entry_use_named += usize::from(stderr.contains(ENTRY_USE));
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} foreign-map provenance cell(s) failed ({matched} matched, {refused} refused):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    let control_cells = rows
        .iter()
        .filter(|row| row.foreign_map_at.is_none())
        .count()
        * OPTS.len();
    assert_eq!(
        controls, control_cells,
        "every control cell must build and match LLVM"
    );
    assert_eq!(matched + refused, cells, "every cell must close");
    let kept_cells: usize = rows
        .iter()
        .filter(|row| row.foreign_map_at.is_some())
        .map(|row| row.must_match_at.len())
        .sum();
    assert_eq!(
        kept, kept_cells,
        "every must-match capability cell must build and match LLVM"
    );
    assert!(
        foreign_named > 0,
        "no cell reached {FOREIGN_MAP}; the provenance check is unwitnessed"
    );
    assert!(
        entry_use_named > 0,
        "no cell reached {ENTRY_USE}; the entry-use check is unwitnessed"
    );
    eprintln!(
        "FOREIGN_MAP_PROVENANCE cells={cells} matched={matched} refused={refused} \
         foreign_map={foreign_named} entry_use={entry_use_named} controls={controls} \
         kept={kept}"
    );
}
