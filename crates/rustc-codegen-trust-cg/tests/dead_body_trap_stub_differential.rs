#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a body the bridge classifies as DEAD (its call sites are
// replaced by an intercepted operation) and fails to lower is replaced by a
// trapping stub under its real symbol, or dropped. Either is sound only when
// nothing can reach that symbol.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. `failure_route` admits a failed body to a trapping stub by its
// def path (`is_dead_std_iterator_reduction_body`,
// `is_dead_intercepted_heap_alloc_glue`), a decision about THIS crate's call
// sites. Ways to reach such a symbol anyway, each measured on origin/main
// 6a57e8ab9 (proofs-off lane, `-Ccodegen-units=1 -Cpanic=abort`, LLVM caller):
//
//   * SHARE-GENERICS EXPORT. Under `-Zshare-generics` (rustc's default at
//     `-Copt-level=0`, `1`, `s` and `z`) rustc lists the generic instances a
//     library instantiates in its metadata, and a downstream crate links them
//     instead of instantiating its own. A library whose only API is scalar but
//     which runs `a.iter().chain(a.iter()).take(5).count()` at `-O1` exported
//     its stubbed `<Chain<..> as Iterator>::try_fold::<..,
//     Take::try_fold::check<..>>`, and the caller's OWN chain count linked it:
//     SIGTRAP where LLVM prints `chain 5`. The `-O0` library's stubbed
//     `SpecTake::spec_fold` was reached the same way by an `-O3` caller built
//     with `-Zshare-generics=yes`.
//   * A DROPPED EXPORT. The same list carried an owning iterator's drop glue the
//     bridge could not lower and DROPPED (`drop_glue::<vec::IntoIter<u32>>`,
//     `<vec::IntoIter<u32> as Drop>::drop`, `drop_glue::<array::IntoIter<u32,
//     4>>`), so an `-O0`/`-O1` caller dropping its own iterator of that type
//     failed to link (closed, but no binary for a correct program).
//   * A STATIC'S FUNCTION-POINTER SLOT. `pub static DROP_VEC: unsafe fn(*mut
//     Vec<u32>) = drop_in_place::<Vec<u32>>` named the dead-heap-glue stub; a
//     library's reference graph held only its functions' references, so
//     `[TCG-HEAP-GLUE-STUB-REACHABLE]` never saw it, and a caller dropping its
//     own `Vec` through the pointer died with SIGTRAP at `-O0`..`-O3`.
//   * A SURVIVING CALL. At `-O2`/`-O3`, `repeat(x).take(n).count()` inlines to
//     `<Take<Repeat<u32>> as SpecTake>::spec_fold`, which the bridge does not
//     drive; a call to the stubbed body survives. Refused by name
//     (`[TCG-ITER-STUB-REACHABLE]` in a library, `[TCG-ITER-UNMODELED]` on the
//     executable path), never run.
//
// THE LANES. Where Trust lets a codegen backend provide queries (the proofs-off
// lane every compile below starts from) the bridge withholds its generic
// instances from the export list (`withheld_exported_generic_symbols`), so a
// downstream crate instantiates its own and every share-generics row must
// MATCH. Where Trust requires rustc's own list (verification,
// `-Ztrust-ir-lower`, a Trust test monitor) the export stands, and a dead body
// rustc exports is refused instead (`[TCG-DEAD-BODY-EXPORTED]`); the
// `canonical` rows reach that lane with `-Ztrust-ir-lower=on`, which keeps
// verification off.
//
// THE GATE, per row. Each row is ONE library compiled by LLVM (the oracle) and
// by the bridge at the row's level; the caller is always compiled by LLVM, and
// whole-program rows compile one binary with each backend.
//   * `Expect::Match`: the bridge must compile, and the program must print
//     exactly what the oracle prints and exit with its code.
//   * `Expect::MatchOrRefusal(codes)`: the same, OR the bridge refuses with one
//     of the bracketed `[codes]` and no compiler panic.
//   * Anything else fails: a different stdout or exit code (a signal is exit
//     code `None`), a run past `RUN_TIMEOUT`, a caller that does not link, an
//     ICE, or another refusal.
// The oracle is asserted first on every row, so a row cannot pass vacuously.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const DEAD_BODY_EXPORTED: &str = "TCG-DEAD-BODY-EXPORTED";
const HEAP_GLUE_STUB_REACHABLE: &str = "TCG-HEAP-GLUE-STUB-REACHABLE";
const ITER_STUB_REACHABLE: &str = "TCG-ITER-STUB-REACHABLE";
const ITER_UNMODELED: &str = "TCG-ITER-UNMODELED";
/// The lane in which Trust requires rustc's own export list (see THE LANES).
const CANONICAL_PROVIDERS_LANE: &[&str] = &["-Ztrust-ir-lower=on"];
const RUN_TIMEOUT: Duration = Duration::from_secs(30);

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// Compiles, and the program's stdout and exit code equal LLVM's.
    Match,
    /// `Match`, or a refusal carrying one of the `[codes]`.
    MatchOrRefusal(&'static [&'static str]),
}

struct Row {
    name: &'static str,
    /// The library's optimization level.
    opt: &'static str,
    /// The LLVM caller's optimization level.
    main_opt: &'static str,
    /// Extra flags for the LLVM caller's compile.
    main_flags: &'static [&'static str],
    /// Frontend flags for both library compiles, oracle and bridge alike.
    lane: &'static [&'static str],
    lib: String,
    main: String,
    expect: Expect,
}

// ---- generic instances exported under `-Zshare-generics` ------------------

/// A library whose only API is scalar, but which instantiates (and so, under
/// `-Zshare-generics`, would export) the collection code it uses locally.
fn c5_lib(body: &str) -> String {
    format!("#[inline(never)]\npub fn k(s: &str) -> usize {{\n    {body}\n}}\n")
}

/// The caller drops and grows collections of its OWN, never ones the library
/// returned. Its argv is never read, so the only drops are the ones written
/// here.
fn c5_main() -> String {
    "use std::hint::black_box;\n\
     fn main() {\n\
     \x20   let n = klib::k(black_box(\"abc\"));\n\
     \x20   println!(\"k {n}\");\n\
     \x20   let s = String::from(black_box(\"driver-owned\"));\n\
     \x20   println!(\"string {}\", s.len());\n\
     \x20   drop(s);\n\
     \x20   let v: Vec<u8> = black_box(vec![1u8, 2, 3]);\n\
     \x20   println!(\"vec_u8 {}\", v.len());\n\
     \x20   drop(v);\n\
     \x20   let mut w: Vec<u32> = black_box(vec![4u32, 5]);\n\
     \x20   for i in 0..black_box(5u32) {\n\
     \x20       w.push(i * 3);\n\
     \x20   }\n\
     \x20   println!(\"vec_u32 {} {:?}\", w.len(), w);\n\
     \x20   drop(w);\n\
     \x20   let x: Vec<i64> = black_box(vec![6i64]);\n\
     \x20   println!(\"vec_i64 {}\", x.len());\n\
     \x20   drop(x);\n\
     \x20   println!(\"dropped\");\n\
     }\n"
    .to_owned()
}

/// The same shape for the dead ITERATOR bodies (`Chain::try_fold`,
/// `SpecTake::spec_fold`) and the array iterator: the caller runs the same
/// reductions on values of its own.
fn c5_iter_main() -> String {
    "use std::hint::black_box;\n\
     fn main() {\n\
     \x20   let n = klib::k(black_box(\"abc\"));\n\
     \x20   println!(\"k {n}\");\n\
     \x20   let a = black_box(b\"wxyz\".as_slice());\n\
     \x20   println!(\"chain {}\", a.iter().chain(a.iter()).take(5).count());\n\
     \x20   let x: [u32; 4] = black_box([5, 6, 7, 8]);\n\
     \x20   println!(\"array {}\", x.into_iter().sum::<u32>());\n\
     }\n"
    .to_owned()
}

const STRING_LOCAL: &str = "let mut t = String::new();\n    t.push_str(s);\n    t.len()";
const VEC_U32_LOCAL: &str = "let mut v: Vec<u32> = Vec::new();\n    \
                             for i in 0..s.len() {\n        v.push(i as u32);\n    }\n    v.len()";
const CHAIN_TAKE_COUNT: &str =
    "let a = s.as_bytes();\n    a.iter().chain(a.iter()).take(5).count()";
const HASHMAP_LOCAL: &str = "let m: std::collections::HashMap<u64, u64> = \
                             std::collections::HashMap::new();\n    m.len() + s.len()";

/// The same shape for the intercepted map's dead drop glue
/// (`drop_glue::<HashMap<u64, u64>>`) and the `RandomState` key cell: the
/// caller builds, grows and drops a `HashMap<u64, u64>` of its own.
fn c5_map_main() -> String {
    "use std::hint::black_box;\n\
     fn main() {\n\
     \x20   let n = klib::k(black_box(\"abc\"));\n\
     \x20   println!(\"k {n}\");\n\
     \x20   let mut m: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();\n\
     \x20   m.insert(black_box(5), 50);\n\
     \x20   m.insert(black_box(7), 70);\n\
     \x20   println!(\"map {} {:?}\", m.len(), m.get(&5));\n\
     \x20   drop(m);\n\
     \x20   println!(\"dropped\");\n\
     }\n"
    .to_owned()
}

/// A share-generics kernel: (name, library body, caller, library levels).
type C5Kernel = (
    &'static str,
    &'static str,
    fn() -> String,
    &'static [&'static str],
);

fn c5_rows(rows: &mut Vec<Row>) {
    const ALL_LEVELS: &[&str] = &["0", "1", "2", "3"];
    let kernels: [C5Kernel; 6] = [
        ("string_local", STRING_LOCAL, c5_main, ALL_LEVELS),
        (
            "vec_u8_local",
            "let mut v: Vec<u8> = Vec::new();\n    \
             for i in 0..s.len() {\n        v.push(i as u8);\n    }\n    v.len()",
            c5_main,
            ALL_LEVELS,
        ),
        ("vec_u32_local", VEC_U32_LOCAL, c5_main, ALL_LEVELS),
        // Before the export list was withheld, the `-O1` library exported its
        // stubbed `Chain::try_fold` (measured: SIGTRAP in the caller's own chain
        // count, after `k 5`).
        (
            "chain_take_count",
            CHAIN_TAKE_COUNT,
            c5_iter_main,
            ALL_LEVELS,
        ),
        // The share-generics sum over the caller's own array, beside the chain.
        // Only the sharing levels, as on the branch this row comes from: the
        // `-O2`/`-O3` library sum is pinned by the `array::IntoIter` rows.
        (
            "iter_chain_array_local",
            "let a = s.as_bytes();\n    \
             let n = a.iter().chain(a.iter()).take(5).count();\n    \
             let arr = [a.len() as u32, 1, 2, 3];\n    \
             n + arr.into_iter().sum::<u32>() as usize",
            c5_iter_main,
            &["0", "1"],
        ),
        // Before the export list was withheld, the `-O0` library exported the
        // dead `drop_glue::<HashMap<u64, u64>>` and was refused unnamed (the
        // heap-glue shared guard), and the `-O1` library's dropped
        // `LocalKey::with` (the `RandomState` key cell) left the caller's own
        // `HashMap::new` an undefined symbol.
        ("hashmap_local", HASHMAP_LOCAL, c5_map_main, ALL_LEVELS),
    ];
    for (name, body, main, levels) in kernels {
        // The proofs-off lane: the library exports no generic instance, at any
        // level, so every row must compile and match.
        for &opt in levels {
            rows.push(Row {
                name,
                opt,
                main_opt: "0",
                main_flags: &[],
                lane: &[],
                lib: c5_lib(body),
                main: main(),
                expect: Expect::Match,
            });
        }
    }
    // The canonical-provider lane: rustc's export list stands. A collection's
    // lowered body uses rustc's own `{cap,ptr,len}` image, so a caller linking it
    // agrees; `-O3` shares no generic instance here.
    for (name, body) in [
        ("string_local", STRING_LOCAL),
        ("vec_u32_local", VEC_U32_LOCAL),
    ] {
        for opt in ["0", "1", "3"] {
            rows.push(Row {
                name,
                opt,
                main_opt: "0",
                main_flags: &[],
                lane: CANONICAL_PROVIDERS_LANE,
                lib: c5_lib(body),
                main: c5_main(),
                expect: Expect::Match,
            });
        }
    }
    // A generic method on a struct that holds a `String` in a field (not a
    // newtype of it): the library instantiates `Rec::slen::<u8>`, and the
    // caller calls the same instance on a `Rec` of its OWN. An
    // `#[inline(never)]` generic is exported at every level where rustc's list
    // stands.
    let rec_lib = "pub struct Rec { pub s: String, pub n: u32 }\n\
                   impl Rec {\n\
                   \x20   #[inline(never)]\n\
                   \x20   pub fn slen<T: Copy>(&self, _t: T) -> usize { self.s.len() }\n\
                   }\n\
                   #[inline(never)]\n\
                   pub fn k(r: &Rec) -> usize { r.slen(3u8) }\n";
    let rec_main = "use std::hint::black_box;\n\
                    fn main() {\n\
                    \x20   let r = klib::Rec { s: String::from(black_box(\"driver-owned\")), n: 4 };\n\
                    \x20   println!(\"slen {} {}\", r.slen(black_box(5u8)), r.n);\n\
                    \x20   std::mem::forget(r);\n\
                    }\n";
    for &opt in ALL_LEVELS {
        rows.push(Row {
            name: "struct_field_string_method",
            opt,
            main_opt: "0",
            main_flags: &[],
            lane: &[],
            lib: rec_lib.to_owned(),
            main: rec_main.to_owned(),
            expect: Expect::Match,
        });
    }
    for opt in ["0", "1", "3"] {
        rows.push(Row {
            name: "struct_field_string_method",
            opt,
            main_opt: "0",
            main_flags: &[],
            lane: CANONICAL_PROVIDERS_LANE,
            lib: rec_lib.to_owned(),
            main: rec_main.to_owned(),
            expect: Expect::Match,
        });
    }
    // A dead iterator body rustc exports in the canonical lane: refused as an
    // exported dead body, or a match. At `-O1` the caller's own chain count
    // links the stubbed `Chain::try_fold` (measured before: SIGTRAP).
    for opt in ["0", "1"] {
        rows.push(Row {
            name: "chain_take_count",
            opt,
            main_opt: "0",
            main_flags: &[],
            lane: CANONICAL_PROVIDERS_LANE,
            lib: c5_lib(CHAIN_TAKE_COUNT),
            main: c5_iter_main(),
            expect: Expect::MatchOrRefusal(&[DEAD_BODY_EXPORTED]),
        });
    }
    // A caller above the library's level: an `-O3` caller built with
    // `-Zshare-generics=yes` links, for its own chain count, the `-O0`
    // library's dead `<Take<Chain<..>> as SpecTake>::spec_fold::<usize,
    // count::{closure}>` stub when rustc lists it (measured before, in both
    // lanes: SIGTRAP in that stub; an `-O0` or `-O1` caller did not reach it).
    rows.push(Row {
        name: "chain_take_count_sharing_o3_caller",
        opt: "0",
        main_opt: "3",
        main_flags: &["-Zshare-generics=yes"],
        lane: &[],
        lib: c5_lib(CHAIN_TAKE_COUNT),
        main: c5_iter_main(),
        expect: Expect::Match,
    });
    rows.push(Row {
        name: "chain_take_count_sharing_o3_caller",
        opt: "0",
        main_opt: "3",
        main_flags: &["-Zshare-generics=yes"],
        lane: CANONICAL_PROVIDERS_LANE,
        lib: c5_lib(CHAIN_TAKE_COUNT),
        main: c5_iter_main(),
        expect: Expect::MatchOrRefusal(&[DEAD_BODY_EXPORTED]),
    });
    // Dead heap glue rustc exports in the canonical lane (the `-O0` map drop
    // glue): refused by name, never a stub a downstream drop links. Not `-O1`:
    // there the library DROPS the `LocalKey::with` it exports (the `RandomState`
    // key cell) and the caller's link fails closed, the canonical-lane gap
    // LIMITATIONS.md records for dropped exported bodies.
    rows.push(Row {
        name: "hashmap_local",
        opt: "0",
        main_opt: "0",
        main_flags: &[],
        lane: CANONICAL_PROVIDERS_LANE,
        lib: c5_lib(HASHMAP_LOCAL),
        main: c5_map_main(),
        expect: Expect::MatchOrRefusal(&[DEAD_BODY_EXPORTED]),
    });
}

// ---- owning-iterator glue the bridge drops -------------------------------

/// The library instantiates the drop glue of two owning iterators
/// (`array::IntoIter<u32, 4>`, `vec::IntoIter<u32>`) and cannot lower it
/// (`[TCG-OWNING-ITER-METHOD]`), so it drops the bodies; the caller drops
/// iterators of the same types of its OWN, and also hands the library one.
fn owning_iter_rows(rows: &mut Vec<Row>) {
    let lib = "#[inline(never)]\n\
               pub fn a4_sum(a: [u32; 4]) -> u32 {\n\
               \x20   a.into_iter().sum()\n\
               }\n\
               #[inline(never)]\n\
               pub fn vec_sum(it: std::vec::IntoIter<u32>) -> u32 {\n\
               \x20   it.sum()\n\
               }\n";
    let main = "use std::hint::black_box;\n\
                fn main() {\n\
                \x20   println!(\"{}\", klib::a4_sum(black_box([1, 2, 3, 4])));\n\
                \x20   println!(\"{}\", klib::vec_sum(black_box(vec![5u32, 6, 7]).into_iter()));\n\
                \x20   let x: [u32; 4] = black_box([5, 6, 7, 8]);\n\
                \x20   println!(\"{}\", x.into_iter().sum::<u32>());\n\
                \x20   let mut arr_it = black_box([1u32, 2, 3, 4]).into_iter();\n\
                \x20   println!(\"{:?}\", arr_it.next());\n\
                \x20   drop(arr_it);\n\
                \x20   let mut it = black_box(vec![1u32, 2, 3]).into_iter();\n\
                \x20   println!(\"{:?}\", it.next());\n\
                \x20   drop(it);\n\
                \x20   println!(\"dropped\");\n\
                }\n";
    for opt in ["0", "1", "2", "3"] {
        rows.push(Row {
            name: "owning_iter_glue_dropped",
            opt,
            main_opt: opt,
            main_flags: &[],
            lane: &[],
            lib: lib.to_owned(),
            main: main.to_owned(),
            expect: Expect::Match,
        });
    }
}

// ---- a `Take` reduction over a source the bridge does not model ------------

fn n1_lib(body: &str) -> String {
    format!("#[inline(never)]\npub fn k(x: u32, n: usize) -> u64 {{\n    {body}\n}}\n")
}

fn n1_main() -> String {
    "use std::hint::black_box;\n\
     fn main() {\n\
     \x20   for &(x, n) in &[(3u32, 4usize), (3, 0), (5, 1), (7, 6)] {\n\
     \x20       println!(\"x={x} n={n} k={}\", klib::k(black_box(x), black_box(n)));\n\
     \x20   }\n\
     }\n"
    .to_owned()
}

fn n1_rows(rows: &mut Vec<Row>) {
    // A library that reaches the stub through a surviving call is refused by
    // `[TCG-ITER-STUB-REACHABLE]`; the call sites that refuse first say
    // `[TCG-ITER-UNMODELED]`.
    const REFUSED: Expect = Expect::MatchOrRefusal(&[ITER_UNMODELED, ITER_STUB_REACHABLE]);
    // (name, body, levels, expectation)
    let table: [(&str, &str, &[&str], Expect); 10] = [
        // The minimal repro, at every level.
        (
            "repeat_take_count",
            "std::iter::repeat(x).take(n).count() as u64",
            &["0", "1", "2", "3"],
            REFUSED,
        ),
        (
            "range_from_take_sum",
            "(x as u64..).take(n).sum::<u64>()",
            &["0", "3"],
            REFUSED,
        ),
        (
            "repeat_with_take_fold",
            "std::iter::repeat_with(|| 3u64).take(n).fold(1u64, |a, b| a.wrapping_mul(31).wrapping_add(b))",
            &["0", "3"],
            REFUSED,
        ),
        (
            "once_take_last",
            "std::iter::once(x).take(n).last().map_or(0, |v| v as u64 + 1)",
            &["0", "3"],
            REFUSED,
        ),
        (
            "cycle_take_sum",
            "(0..x as u64).cycle().take(n).sum::<u64>()",
            &["0", "3"],
            REFUSED,
        ),
        (
            "successors_take_product",
            "std::iter::successors(Some(1u64), |&v| Some(v + x as u64)).take(n).product::<u64>()",
            &["0", "3"],
            REFUSED,
        ),
        (
            "range_from_take_take_sum",
            "(x as u64..).take(n + 1).take(n).sum::<u64>()",
            &["0", "3"],
            REFUSED,
        ),
        (
            "range_from_map_take_sum",
            "(x as u64..).map(|v| v * 2).take(n).sum::<u64>()",
            &["0", "3"],
            REFUSED,
        ),
        // Controls: `Take` over a modeled source is intercepted at every level,
        // and its collector-required `spec_fold` stays a genuinely dead stub.
        (
            "range_take_sum_control",
            "(x as u64..x as u64 + 100).take(n).sum::<u64>()",
            &["0", "3"],
            Expect::Match,
        ),
        (
            "range_take_count_control",
            "(0..x as u64 * 10).take(n).count() as u64",
            &["0", "3"],
            Expect::Match,
        ),
    ];
    for (name, body, levels, expect) in table {
        for &opt in levels {
            rows.push(Row {
                name,
                opt,
                main_opt: "3",
                main_flags: &[],
                lane: &[],
                lib: n1_lib(body),
                main: n1_main(),
                expect,
            });
        }
    }
}

// ---- a collection unsized into an owning `Box<dyn>` --------------------------

fn n2_lib(prelude: &str, body: &str) -> String {
    format!(
        "use std::any::Any;\n{prelude}\n#[inline(never)]\npub fn k(n: u32) -> u64 {{\n    {body}\n}}\n"
    )
}

fn n2_main() -> String {
    "use std::hint::black_box;\n\
     fn main() {\n\
     \x20   for n in [0u32, 1, 3, 7] {\n\
     \x20       println!(\"n={n} k={}\", klib::k(black_box(n)));\n\
     \x20   }\n\
     }\n"
    .to_owned()
}

const PUSHED_VEC: &str =
    "let mut v: Vec<u32> = Vec::new();\n    for i in 0..n {\n        v.push(i);\n    }\n    ";

/// The trait object's `drop_in_place` slot names rustc's glue for the
/// collection, which the bridge LOWERS over rustc's image (`heap_image_glue`):
/// every row must match.
fn n2_rows(rows: &mut Vec<Row>) {
    let table: Vec<(&str, &str, String)> = vec![
        (
            "dyn_any_vec_new",
            "",
            "let b: Box<dyn Any> = Box::new(Vec::<u32>::new());\n    drop(b);\n    n as u64"
                .to_owned(),
        ),
        (
            "dyn_any_vec_pushed",
            "",
            format!("{PUSHED_VEC}let b: Box<dyn Any> = Box::new(v);\n    drop(b);\n    n as u64"),
        ),
        (
            "dyn_any_vec_scope_end",
            "",
            format!("{PUSHED_VEC}let _b: Box<dyn Any> = Box::new(v);\n    n as u64 + 1"),
        ),
        (
            "dyn_any_vec_u8",
            "",
            "let mut v: Vec<u8> = Vec::new();\n    for i in 0..n {\n        v.push(i as u8);\n    }\n    \
             let b: Box<dyn Any> = Box::new(v);\n    drop(b);\n    n as u64"
                .to_owned(),
        ),
        (
            "dyn_any_string",
            "",
            "let mut s = String::new();\n    s.push('a');\n    \
             let b: Box<dyn Any> = Box::new(s);\n    drop(b);\n    n as u64"
                .to_owned(),
        ),
        (
            "dyn_user_trait_vec",
            "pub trait Len { fn len_(&self) -> usize; }\n\
             impl Len for Vec<u32> { fn len_(&self) -> usize { self.len() } }",
            format!("{PUSHED_VEC}let b: Box<dyn Len> = Box::new(v);\n    b.len_() as u64"),
        ),
        (
            "dyn_generic_erase",
            "#[inline(never)]\nfn erase<T: Any>(t: T) -> Box<dyn Any> { Box::new(t) }",
            format!("{PUSHED_VEC}drop(erase(v));\n    n as u64"),
        ),
        (
            "dyn_any_box_box_vec",
            "",
            format!(
                "{PUSHED_VEC}let b: Box<dyn Any> = Box::new(Box::new(v));\n    drop(b);\n    n as u64"
            ),
        ),
        (
            "dyn_any_vec_forgotten",
            "",
            format!("{PUSHED_VEC}let b: Box<dyn Any> = Box::new(v);\n    std::mem::forget(b);\n    n as u64"),
        ),
        (
            "plain_box_vec_control",
            "",
            format!("{PUSHED_VEC}let b: Box<Vec<u32>> = Box::new(v);\n    b.len() as u64"),
        ),
        (
            "dyn_any_box_u64_control",
            "",
            "let b: Box<dyn Any> = Box::new(Box::new(n as u64 * 3));\n    drop(b);\n    n as u64"
                .to_owned(),
        ),
    ];
    for (name, prelude, body) in table {
        for opt in ["0", "3"] {
            rows.push(Row {
                name,
                opt,
                main_opt: "3",
                main_flags: &[],
                lane: &[],
                lib: n2_lib(prelude, &body),
                main: n2_main(),
                expect: Expect::Match,
            });
        }
    }
}

// ---- a library static's fn-pointer slot naming a dead body -------------------

/// The library exports a `static` whose initializer is a function pointer to
/// the dead `Vec<u32>` drop body; its only function is scalar. The LLVM caller
/// drops a `Vec<u32>` of its OWN through that pointer. Measured at every level
/// on 6a57e8ab9: the relocation named the trapping stub and the caller died
/// with SIGTRAP after `len 3`, where LLVM prints `dropped`.
fn static_slot_rows(rows: &mut Vec<Row>) {
    let lib = "pub static DROP_VEC: unsafe fn(*mut Vec<u32>) = \
               std::ptr::drop_in_place::<Vec<u32>>;\n\
               #[inline(never)]\npub fn k(n: u32) -> u64 {\n    n as u64 + 1\n}\n"
        .to_owned();
    let main = "use std::hint::black_box;\n\
                use std::mem::ManuallyDrop;\n\
                fn main() {\n\
                \x20   println!(\"k {}\", klib::k(black_box(4)));\n\
                \x20   let mut v = ManuallyDrop::new(black_box(vec![1u32, 2, 3]));\n\
                \x20   println!(\"len {}\", v.len());\n\
                \x20   unsafe { (klib::DROP_VEC)(&mut *v as *mut Vec<u32>) };\n\
                \x20   println!(\"dropped\");\n\
                }\n"
    .to_owned();
    for opt in ["0", "1", "2", "3"] {
        rows.push(Row {
            name: "static_fn_pointer_to_dead_vec_glue",
            opt,
            main_opt: "0",
            main_flags: &[],
            lane: &[],
            lib: lib.clone(),
            main: main.clone(),
            expect: Expect::MatchOrRefusal(&[HEAP_GLUE_STUB_REACHABLE]),
        });
    }
}

// ---- harness ----------------------------------------------------------------

fn workdir(stem: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("tcg_dead_body_stub_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn base_command(opt: &str) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(format!("-Copt-level={opt}"));
    cmd
}

fn add_backend(cmd: &mut Command, dylib: &Path) {
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(backend_arg);
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
}

fn compile(cmd: &mut Command) -> Result<(), String> {
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Compile the row's library; `Err` carries the compiler's stderr.
fn compile_lib(dir: &Path, row: &Row, backend: Option<&Path>, rlib: &Path) -> Result<(), String> {
    let src = dir.join("klib.rs");
    std::fs::write(&src, &row.lib).expect("write library source");
    let mut cmd = base_command(row.opt);
    cmd.args(row.lane);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(&src);
    compile(&mut cmd)
}

/// Link the LLVM-compiled caller against `rlib`.
fn compile_main(dir: &Path, row: &Row, rlib: &Path, bin: &Path) {
    let src = dir.join("kmain.rs");
    std::fs::write(&src, &row.main).expect("write caller source");
    let mut cmd = base_command(row.main_opt);
    cmd.args(row.main_flags);
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(&src);
    if let Err(stderr) = compile(&mut cmd) {
        panic!(
            "row {}@O{}: the LLVM-compiled caller did not build (an undefined symbol here \
             is a library that dropped a body a downstream crate links): <<<{stderr}>>>",
            row.name, row.opt
        );
    }
}

fn run_with_timeout(bin: &Path) -> Option<Output> {
    let mut child = Command::new(bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the compiled program");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("poll the compiled program")
            .is_some()
        {
            return Some(child.wait_with_output().expect("collect program output"));
        }
        if start.elapsed() >= RUN_TIMEOUT {
            child.kill().expect("kill the timed-out program");
            let _ = child.wait_with_output();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Every `[TCG-...]` code in `stderr`.
fn refusal_codes(stderr: &str) -> Vec<String> {
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let Some(end) = tail.find(']') else {
            break;
        };
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    codes
}

/// The verdict for a bridge build that failed: a refusal the row admits, or a
/// panic naming what it was instead.
fn judge_refusal(label: &str, expect: Expect, stderr: &str) -> String {
    assert!(
        !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
        "row {label}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
    );
    let codes = refusal_codes(stderr);
    match expect {
        Expect::Match => panic!(
            "row {label}: this shape compiles and runs correctly and must not be refused \
             (codes {codes:?}): <<<{stderr}>>>"
        ),
        Expect::MatchOrRefusal(admitted) => {
            let named = admitted
                .iter()
                .find(|code| codes.iter().any(|c| c == *code));
            assert!(
                stderr.contains("error: ") && named.is_some(),
                "row {label}: expected a match or a refusal naming one of {admitted:?}; got \
                 codes {codes:?}: <<<{stderr}>>>"
            );
            format!("REFUSED [{}] (fail-closed)", named.unwrap())
        }
    }
}

/// The suffix naming a row's lane in labels and reports.
fn lane_tag(row: &Row) -> &'static str {
    if row.lane.is_empty() {
        ""
    } else {
        "+canonical"
    }
}

/// The oracle's output, then the bridge's verdict for one library row.
fn check_row(dylib: &Path, row: &Row) -> String {
    let label = format!("{}@O{}{}", row.name, row.opt, lane_tag(row));
    let dir = workdir(&label);
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");

    compile_lib(&dir, row, None, &oracle_rlib).unwrap_or_else(|e| {
        panic!("row {label}: the LLVM oracle library did not build: <<<{e}>>>")
    });
    let oracle_bin = dir.join("llvm_kmain");
    compile_main(&dir, row, &oracle_rlib, &oracle_bin);
    let oracle = run_with_timeout(&oracle_bin)
        .unwrap_or_else(|| panic!("row {label}: the LLVM oracle did not finish"));
    let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
    assert!(
        oracle.status.success() && !oracle_stdout.is_empty(),
        "row {label}: the LLVM oracle must print and exit 0; status {:?}, stdout \
         <<<{oracle_stdout}>>>",
        oracle.status
    );

    let verdict = match compile_lib(&dir, row, Some(dylib), &bridge_rlib) {
        Ok(()) => {
            let bridge_bin = dir.join("bridge_kmain");
            compile_main(&dir, row, &bridge_rlib, &bridge_bin);
            let Some(bridge) = run_with_timeout(&bridge_bin) else {
                panic!(
                    "row {label}: the bridge-compiled library did not finish within \
                     {RUN_TIMEOUT:?}; oracle printed <<<{oracle_stdout}>>>"
                );
            };
            let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
            assert_eq!(
                (bridge.status.code(), bridge_stdout.as_str()),
                (oracle.status.code(), oracle_stdout.as_str()),
                "row {label}: the bridge-compiled library disagrees with LLVM (exit code \
                 None is a signal: a trapping stub was reached). A dead-body stub may be \
                 emitted only under a symbol nothing references and no crate links; \
                 refuse the shape with a named code rather than relaxing this assertion. \
                 stderr <<<{}>>>",
                String::from_utf8_lossy(&bridge.stderr)
            );
            "MATCHED LLVM".to_owned()
        }
        Err(stderr) => judge_refusal(&label, row.expect, &stderr),
    };
    let _ = std::fs::remove_dir_all(&dir);
    verdict
}

fn run_rows(test: &str, rows: &[Row]) {
    let dylib = backend_artifact_support::current_test_backend();
    let mut report = Vec::new();
    for row in rows {
        let verdict = check_row(&dylib, row);
        let lane = lane_tag(row);
        eprintln!("row {}@O{}{lane}: {verdict}", row.name, row.opt);
        report.push(format!("{}@O{}{lane} {verdict}", row.name, row.opt));
    }
    eprintln!("{test} ({} rows): {report:#?}", rows.len());
}

#[test]
fn share_generics_exported_dead_glue_matches_llvm_or_refuses() {
    if toolchain_support::skip_without_backend_knobs(
        "share_generics_exported_dead_glue_matches_llvm_or_refuses",
    ) {
        return;
    }
    let mut rows = Vec::new();
    c5_rows(&mut rows);
    run_rows("share-generics exported dead glue", &rows);
}

#[test]
fn dropped_owning_iterator_glue_links_and_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "dropped_owning_iterator_glue_links_and_matches_llvm",
    ) {
        return;
    }
    let mut rows = Vec::new();
    owning_iter_rows(&mut rows);
    run_rows("dropped owning-iterator glue", &rows);
}

#[test]
fn take_reduction_over_unmodeled_source_matches_llvm_or_refuses() {
    if toolchain_support::skip_without_backend_knobs(
        "take_reduction_over_unmodeled_source_matches_llvm_or_refuses",
    ) {
        return;
    }
    let mut rows = Vec::new();
    n1_rows(&mut rows);
    run_rows("take reduction over an unmodeled source", &rows);
}

#[test]
fn boxed_collection_trait_object_drop_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "boxed_collection_trait_object_drop_matches_llvm",
    ) {
        return;
    }
    let mut rows = Vec::new();
    n2_rows(&mut rows);
    run_rows("boxed collection trait-object drop", &rows);
}

#[test]
fn static_fn_pointer_to_dead_body_matches_llvm_or_refuses() {
    if toolchain_support::skip_without_backend_knobs(
        "static_fn_pointer_to_dead_body_matches_llvm_or_refuses",
    ) {
        return;
    }
    let mut rows = Vec::new();
    static_slot_rows(&mut rows);
    run_rows("library static fn-pointer slot", &rows);
}

/// The surviving-call and vtable-slot shapes with the WHOLE program compiled by
/// the bridge, the executable path whose demand-driven lowering reaches a dead
/// body only through a reference, so it refuses that body instead of stubbing.
#[test]
fn whole_program_dead_body_stubs_match_llvm_or_refuse() {
    if toolchain_support::skip_without_backend_knobs(
        "whole_program_dead_body_stubs_match_llvm_or_refuse",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let programs: [(&str, &str, &[&str], Expect); 4] = [
        (
            "wp_repeat_take_count",
            "use std::hint::black_box;\n\
             #[inline(never)]\n\
             fn k(x: u32, n: usize) -> usize { std::iter::repeat(x).take(n).count() }\n\
             fn main() {\n\
             \x20   for n in [4usize, 0, 9] {\n\
             \x20       println!(\"{}\", k(black_box(3), black_box(n)));\n\
             \x20   }\n\
             }\n",
            &["0", "2", "3"],
            Expect::MatchOrRefusal(&[ITER_UNMODELED]),
        ),
        (
            "wp_boxdyn_vec_drop",
            "use std::any::Any;\n\
             use std::hint::black_box;\n\
             #[inline(never)]\n\
             fn k(n: u32) -> u64 {\n\
             \x20   let mut v: Vec<u32> = Vec::new();\n\
             \x20   for i in 0..n { v.push(i); }\n\
             \x20   let b: Box<dyn Any> = Box::new(v);\n\
             \x20   drop(b);\n\
             \x20   n as u64\n\
             }\n\
             fn main() {\n\
             \x20   for n in [0u32, 3] {\n\
             \x20       println!(\"{}\", k(black_box(n)));\n\
             \x20   }\n\
             }\n",
            &["0", "3"],
            Expect::Match,
        ),
        // Controls: a modeled `Take` reduction and a concrete `Box<Vec<u32>>`.
        (
            "wp_range_take_sum_control",
            "use std::hint::black_box;\n\
             #[inline(never)]\n\
             fn k(x: u64, n: usize) -> u64 { (x..x + 100).take(n).sum::<u64>() }\n\
             fn main() {\n\
             \x20   for n in [4usize, 0, 9] {\n\
             \x20       println!(\"{}\", k(black_box(3), black_box(n)));\n\
             \x20   }\n\
             }\n",
            &["0", "3"],
            Expect::Match,
        ),
        (
            "wp_plain_box_vec_control",
            "use std::hint::black_box;\n\
             #[inline(never)]\n\
             fn k(n: u32) -> u64 {\n\
             \x20   let mut v: Vec<u32> = Vec::new();\n\
             \x20   for i in 0..n { v.push(i); }\n\
             \x20   let b: Box<Vec<u32>> = Box::new(v);\n\
             \x20   b.len() as u64\n\
             }\n\
             fn main() {\n\
             \x20   for n in [0u32, 3] {\n\
             \x20       println!(\"{}\", k(black_box(n)));\n\
             \x20   }\n\
             }\n",
            &["0", "3"],
            Expect::Match,
        ),
    ];
    let mut report = Vec::new();
    for (name, source, levels, expect) in programs {
        for &opt in levels {
            let label = format!("{name}@O{opt}");
            let dir = workdir(&label);
            let src = dir.join("whole.rs");
            std::fs::write(&src, source).expect("write program source");
            let build = |backend: Option<&Path>, bin: &Path| -> Result<(), String> {
                let mut cmd = base_command(opt);
                cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
                if let Some(dylib) = backend {
                    add_backend(&mut cmd, dylib);
                }
                cmd.arg("-o").arg(bin).arg(&src);
                compile(&mut cmd)
            };
            let oracle_bin = dir.join("llvm_whole");
            build(None, &oracle_bin).unwrap_or_else(|e| {
                panic!("{label}: the LLVM oracle program did not build: <<<{e}>>>")
            });
            let oracle = run_with_timeout(&oracle_bin)
                .unwrap_or_else(|| panic!("{label}: the LLVM oracle did not finish"));
            let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
            assert!(
                oracle.status.success() && !oracle_stdout.is_empty(),
                "{label}: the LLVM oracle must print and exit 0; status {:?}",
                oracle.status
            );
            let bridge_bin = dir.join("bridge_whole");
            let verdict = match build(Some(&dylib), &bridge_bin) {
                Ok(()) => {
                    let bridge = run_with_timeout(&bridge_bin).unwrap_or_else(|| {
                        panic!("{label}: the bridge-compiled program did not finish")
                    });
                    let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
                    assert_eq!(
                        (bridge.status.code(), bridge_stdout.as_str()),
                        (oracle.status.code(), oracle_stdout.as_str()),
                        "{label}: the bridge-compiled program disagrees with LLVM (exit code \
                         None is a signal: a trapping stub was reached); stderr <<<{}>>>",
                        String::from_utf8_lossy(&bridge.stderr)
                    );
                    "MATCHED LLVM".to_owned()
                }
                Err(stderr) => judge_refusal(&label, expect, &stderr),
            };
            eprintln!("{label}: {verdict}");
            report.push(format!("{label} {verdict}"));
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    eprintln!("whole-program dead-body stub rows: {report:#?}");
}
