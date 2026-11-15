//! Closure bodies across the backend boundary, by SYMBOL. The programs are the
//! wrong-code routes four verifier rounds of the L06-P16 repair measured
//! (2026-10-03, AArch64 Linux) against the bridge `main` then had, which
//! declared a closure body's `Pair` argument as one whole slot and its by-value
//! environment as a pointer. That line refused each by name where the body's
//! symbol crossed a crate boundary (the symbol rule,
//! `instance_symbol_crosses_crates`, docs/decision-record.md LD-19). Round 10
//! (OD-RUST-CALL-ONE-RULE-20261008) declares every closure body as rustc's
//! `FnAbi` lists it and compares every declaration's byte placement with
//! rustc's (`check_signature_placement`), so the symbol rule had no
//! disagreement left to guard and was not landed (LD-26). Every cell below
//! must now compile and print LLVM's value, and each cell's LLVM control (the
//! same crates, levels and flags built by LLVM) must print the independently
//! computed oracle. The routes:
//!
//! 1. A closure body a bridge binary LINKS from an LLVM library, taking a
//!    whole-slot `Pair` that holds a `bool` (`impl Fn(u64, (u64, bool))`,
//!    exported by an O1 `-Clink-dead-code` library, or an `#[inline(never)]`
//!    closure at O2). rustc marks the `bool` `zeroext`, LLVM's body tests all 32
//!    bits of its register, and the bridge's lane carried the pair's padding
//!    (0xAB here): `v 122 1125` against `v 122 132`. The bridge body exported
//!    to an LLVM binary, and a `(u64, u8)` pair (no extension) linked from
//!    LLVM, ran correctly.
//! 2. Bodies rustc EXPORTS, which another crate's code reached by symbol in
//!    each verifier round by a route the reachability walk the symbol rule
//!    replaced did not read: an LLVM binary's own copy of an exported
//!    `mk::<u8>` holding an `#[inline(never)]` closure (SIGSEGV against `v
//!    105298 105298`; the `&str` argument is at register exhaustion); a
//!    `type_alias_impl_trait` alias handing the closure's type to another
//!    crate, an upstream crate's included (SIGSEGV at O0 against `v 105294
//!    105294`); another crate's MIR inliner (SIGSEGV against `v
//!    1378546575549278007 1378546575549278007`); and a `Drop` impl of a struct
//!    holding the closure (SIGSEGV against `v 105302 105302`, and a by-value
//!    `FnOnce` environment), in both directions (a bridge library under an
//!    LLVM binary, and a bridge binary linking an LLVM library's body), and
//!    with an `#[inline(never)]` consumer or defining function.
//! 3. An instance rustc gives external linkage without exporting it
//!    (`mk::<{closure in use_here}>`, whose type argument no other crate can
//!    name), with and without generic sharing.
//! 4. Controls: closures whose arguments fit the registers, and the same
//!    closures at O2 / O3, where rustc gives a closure body that is not
//!    `#[inline(never)]` a private copy in each codegen unit that calls it,
//!    with the binary's MIR inliner and generic sharing on.
//!
//! Diagnostic native execution under `no-proof-certs`; it does not qualify
//! mandatory machine proof.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// A buffer of 0xAB bytes with the pair's fields written at their offsets: the
/// pair's padding stays 0xAB. `main` reads the pair straight out of it, so the
/// padding reaches the call (a helper returning the pair by value would rebuild
/// it in registers, and the padding would not survive).
const DIRTY: &str = r#"
#[inline(never)]
fn dirty_words(fields: &[(usize, &[u8])]) -> Vec<u64> {
    let mut w = vec![0xABAB_ABAB_ABAB_ABABu64; 4];
    let p = w.as_mut_ptr() as *mut u8;
    for (off, bytes) in fields {
        for (i, b) in bytes.iter().enumerate() {
            unsafe { *p.add(off + i) = *b };
        }
    }
    w
}
"#;

const PAIR_LIBRARY: &str = r#"use std::hint::black_box as bb;
pub fn mkp(s: u64) -> impl Fn(u64, (u64, bool)) -> u64 {
    move |a: u64, t: (u64, bool)| a * 10 + s + (if t.1 { 1000 } else { 7 } + t.0)
}
#[inline(never)]
pub fn use_here(s: u64) -> u64 {
    let f = mkp(s);
    f(1, (5, bb(false)))
}
"#;

const PAIR_INLINE_NEVER_LIBRARY: &str = r#"#![feature(stmt_expr_attributes)]
use std::hint::black_box as bb;
pub fn mkp(s: u64) -> impl Fn(u64, (u64, bool)) -> u64 {
    let c = #[inline(never)]
    move |a: u64, t: (u64, bool)| a * 10 + s + (if t.1 { 1000 } else { 7 } + t.0);
    c
}
#[inline(never)]
pub fn use_here(s: u64) -> u64 {
    let f = mkp(s);
    f(1, (5, bb(false)))
}
"#;

const U8_PAIR_LIBRARY: &str = r#"use std::hint::black_box as bb;
pub fn mkp(s: u64) -> impl Fn(u64, (u64, u8)) -> u64 {
    move |a: u64, t: (u64, u8)| a * 10 + s + t.0 + t.1 as u64
}
#[inline(never)]
pub fn use_here(s: u64) -> u64 {
    let f = mkp(s);
    f(1, (5, bb(3)))
}
"#;

/// `mkp(100)(2, t)` with `t` read out of a buffer whose padding is 0xAB.
fn pair_driver(ty: &str) -> String {
    format!(
        "use std::hint::black_box as bb;\nuse std::mem::offset_of;\n{DIRTY}\nfn main() {{\n    \
         let a = fixture::use_here(bb(100));\n    let f = fixture::mkp(bb(100));\n    \
         let w = dirty_words(&[(offset_of!({ty}, 0), &5u64.to_ne_bytes()), \
         (offset_of!({ty}, 1), &[{second}])]);\n    let t: {ty} = unsafe {{ \
         std::ptr::read(w.as_ptr() as *const {ty}) }};\n    println!(\"v {{a}} {{}}\", f(bb(2), t));\n}}\n",
        second = if ty.contains("bool") { "0u8" } else { "3u8" },
    )
}

/// The closure `mk` defines: its `&str` is argument 7, after the environment
/// pointer and six `u64`, so rustc splits it across `x7` and the stack.
const STR_CLOSURE: &str = "move |a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, x: &'static \
                           str| -> u64 {\n        a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + \
                           (x.len() as u64) * 100 + (x.as_bytes()[0] as u64) * 1000 + s\n    }";
const STR_CALL: &str = "bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(\"hello, world\")";

/// A generic `mk` whose closure is (or is not) `#[inline(never)]`, calling it
/// as `body` does; `run` is the consumer `body` may hand it to.
fn copy_library(closure_attr: &str, body: &str, run_attr: &str) -> String {
    format!(
        "#![feature(stmt_expr_attributes)]\nuse std::hint::black_box as bb;\n{run_attr}pub fn \
         run<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64>(f: F) -> u64 {{\n    \
         f({STR_CALL})\n}}\npub fn mk<T: Copy + Into<u64>>(t: T) -> u64 {{\n    let s: u64 = \
         t.into();\n    let c = {closure_attr}{STR_CLOSURE};\n    {body}\n}}\n#[inline(never)]\n\
         pub fn use_here() -> u64 {{\n    mk(bb(7u8))\n}}\n"
    )
}

const COPY_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                           fixture::use_here();\n    let b = fixture::mk(bb(7u8));\n    \
                           println!(\"v {a} {b}\");\n}\n";

const TAIT_HEAD: &str = "#![feature(type_alias_impl_trait)]\nuse std::hint::black_box as bb;\n";
const TAIT_CLOSURE: &str = "move |a: u64, b: u64, c: u64, d: u64, e: u64, g: u64, x: &'static \
                            str| -> u64 {\n            a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * g \
                            + (x.len() as u64) * 100 + (x.as_bytes()[0] as u64) * 1000 + s\n        }";
const TAIT_TY: &str = "Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64";
const FIT_CLOSURE: &str = "move |a: u64, x: &'static str| -> u64 {\n            a + (x.len() \
                           as u64) * 100 + (x.as_bytes()[0] as u64) * 1000 + s\n        }";
const FIT_TY: &str = "Fn(u64, &'static str) -> u64";
const FIT_CALL: &str = "bb(1), bb(\"hello, world\")";

/// `pub type F = impl ..; pub struct Wr { pub f: F }` and `mk(s) -> Wr`.
fn field_library(closure: &str, ty: &str, call: &str) -> String {
    format!(
        "{TAIT_HEAD}pub type F = impl {ty};\npub struct Wr {{\n    pub f: F,\n}}\n\
         #[define_opaque(F)]\n#[inline(never)]\npub fn mk(s: u64) -> Wr {{\n    Wr {{\n        f: \
         {closure},\n    }}\n}}\n#[inline(never)]\npub fn use_here() -> u64 {{\n    let w = \
         mk(bb(3));\n    (w.f)({call})\n}}\n"
    )
}

/// The alias defined by `install`, which returns nothing; `get` names it.
fn slot_library() -> String {
    format!(
        "{TAIT_HEAD}pub type F = impl {TAIT_TY};\npub struct Wr {{\n    pub f: F,\n}}\n\
         #[define_opaque(F)]\n#[inline(never)]\npub fn install(slot: &mut Option<F>, s: u64) {{\n    \
         *slot = Some({TAIT_CLOSURE});\n}}\n#[inline(never)]\npub fn get(s: u64) -> Wr {{\n    let \
         mut slot = None;\n    install(&mut slot, s);\n    Wr {{ f: slot.unwrap() }}\n}}\n\
         #[inline(never)]\npub fn use_here() -> u64 {{\n    let w = get(bb(3));\n    \
         (w.f)({STR_CALL})\n}}\n"
    )
}

fn field_driver(make: &str, call: &str) -> String {
    format!(
        "use std::hint::black_box as bb;\nfn main() {{\n    let a = fixture::use_here();\n    let \
         w = {make}(bb(3));\n    let b = (w.f)({call});\n    println!(\"v {{a}} {{b}}\");\n}}\n"
    )
}

/// An upstream crate's generic alias, whose closure the library instantiates
/// with its own `Loc` (and so exports at O0).
fn upstream_alias(closure: &str, ty: &str) -> String {
    format!(
        "#![feature(type_alias_impl_trait)]\npub type F<T: Copy + Into<u64>> = impl {ty};\npub \
         struct Wr<T: Copy + Into<u64>> {{\n    pub f: F<T>,\n}}\n#[define_opaque(F)]\npub fn \
         mk<T: Copy + Into<u64>>(t: T) -> Wr<T> {{\n    Wr {{\n        f: {},\n    }}\n}}\n",
        closure.replace("+ s", "+ t.into()")
    )
}

/// An upstream crate's alias that the closure's defining function `install`
/// defines through a parameter slot (it returns nothing) and that another item,
/// `get`, names in its returned struct, so the defining function's signature
/// never shows the closure. Non-generic and `#[inline]` (the library compiles
/// its own copies, so it instantiates and exports the closure body at O0), or
/// generic, instantiated with the library's own `Loc`. Measured before the
/// upstream crate's aliases were read (fifth verifier round of the L06-P16
/// repair, 2026-10-03): SIGSEGV at O0 against `v 105294 105294`, both ways.
fn upstream_slot(closure: &str, ty: &str, generic: bool) -> String {
    if generic {
        return format!(
            "#![feature(type_alias_impl_trait)]\npub type F<T: Copy + Into<u64>> = impl {ty};\npub \
             struct Wr<T: Copy + Into<u64>> {{\n    pub f: F<T>,\n}}\n#[define_opaque(F)]\npub fn \
             install<T: Copy + Into<u64>>(slot: &mut Option<F<T>>, t: T) {{\n    *slot = \
             Some({});\n}}\npub fn get<T: Copy + Into<u64>>(t: T) -> Wr<T> {{\n    let mut slot = \
             None;\n    install(&mut slot, t);\n    Wr {{ f: slot.unwrap() }}\n}}\n",
            closure.replace("+ s", "+ t.into()")
        );
    }
    format!(
        "#![feature(type_alias_impl_trait)]\npub type F = impl {ty};\npub struct Wr {{\n    pub f: \
         F,\n}}\n#[define_opaque(F)]\n#[inline]\npub fn install(slot: &mut Option<F>, s: u64) {{\n    \
         *slot = Some({closure});\n}}\n#[inline]\npub fn get(s: u64) -> Wr {{\n    let mut slot = \
         None;\n    install(&mut slot, s);\n    Wr {{ f: slot.unwrap() }}\n}}\n"
    )
}

/// The library over an upstream crate: `make` builds the struct (`Loc` is the
/// library's own type a generic upstream item can be instantiated with).
fn upstream_library(make: &str, call: &str) -> String {
    format!(
        "use std::hint::black_box as bb;\n#[derive(Clone, Copy)]\npub struct Loc(pub u64);\nimpl \
         From<Loc> for u64 {{\n    fn from(l: Loc) -> u64 {{\n        l.0\n    }}\n}}\n\
         #[inline(never)]\npub fn use_here() -> u64 {{\n    let w = {make};\n    (w.f)({call})\n}}\n"
    )
}

fn upstream_driver(make: &str, call: &str) -> String {
    format!(
        "use std::hint::black_box as bb;\nfn main() {{\n    let a = fixture::use_here();\n    let \
         w = {make};\n    let b = (w.f)({call});\n    println!(\"v {{a}} {{b}}\");\n}}\n"
    )
}

const UPSTREAM_MK: (&str, &str) = (
    "upstream::mk(Loc(bb(3)))",
    "upstream::mk(fixture::Loc(bb(3)))",
);
const UPSTREAM_GET: (&str, &str) = ("upstream::get(bb(3))", "upstream::get(bb(3))");
const UPSTREAM_GET_LOC: (&str, &str) = (
    "upstream::get(Loc(bb(3)))",
    "upstream::get(fixture::Loc(bb(3)))",
);

/// The helper the closures below call: an `#[inline(never)]` call in a loop
/// keeps each closure body too big for rustc's MIR inliner, so a crate that
/// inlines the defining function still calls the body by symbol.
const MIX_HEAD: &str = "use std::hint::black_box as bb;\n#[inline(never)]\npub fn mix(a: u64, b: \
                        u64) -> u64 {\n    a.wrapping_mul(31).wrapping_add(b) ^ (a >> 7)\n}\n";
/// A closure whose `&str` is argument 7 (rustc splits it across `x7` and the
/// stack), with a body the MIR inliner does not inline.
const LOOP_CLOSURE: &str = "move |a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, x: &'static \
                            str| -> u64 {\n        let mut acc: u64 = a + 2 * b + 3 * c + 4 * d \
                            + 5 * e + 6 * f + s;\n        for (i, ch) in x.bytes().enumerate() \
                            {\n            acc = mix(acc, ch as u64);\n            if bb(acc) % \
                            3 == 0 {\n                acc = mix(acc, i as u64);\n            \
                            }\n        }\n        acc.wrapping_add((x.len() as u64) * 100 + \
                            (x.as_bytes()[0] as u64) * 1000)\n    }";
const LOOP_CALL: &str = "1, 2, 3, 4, 5, 6, \"hello, world\"";

/// A generic `mk` (`#[inline(never)]` or not) calling its closure directly, or
/// handing it to `run` (`run_attr` on it). `use_here` makes the library
/// instantiate, and so export, `mk::<u8>` (and its closure body) at O0; with
/// `reify`, it also takes `mk::<u8>`'s address, which keeps the instance when
/// the library's own inliner inlines its calls.
fn inliner_library(mk_attr: &str, body: &str, run_attr: &str, reify: bool) -> String {
    let use_here = if reify {
        "let f: fn(u8, u64) -> u64 = bb(mk::<u8>);\n    f(bb(7), bb(7)).wrapping_add(mk(bb(7u8), \
         bb(7)))"
    } else {
        "mk(bb(7u8), bb(7))"
    };
    format!(
        "{MIX_HEAD}{run_attr}pub fn run<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> \
         u64>(f: F) -> u64 {{\n    f({LOOP_CALL})\n}}\n{mk_attr}pub fn mk<T: Copy>(_t: T, s: \
         u64) -> u64 {{\n    let c = {LOOP_CLOSURE};\n    {body}\n}}\n#[inline(never)]\npub fn \
         use_here() -> u64 {{\n    {use_here}\n}}\n"
    )
}

const INLINER_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                              fixture::use_here();\n    let b = fixture::mk(bb(7u8), bb(7));\n    \
                              println!(\"v {a} {b}\");\n}\n";

/// The library also defines `#[inline] outer` and generic `outer3`, into which
/// its own MIR inliner (`-Zinline-mir=yes`) puts `mk::<u8>`.
fn inliner_outer_library() -> String {
    format!(
        "{}#[inline]\npub fn outer(k: u64) -> u64 {{\n    mk(7u8, 7).wrapping_add(k)\n}}\npub fn \
         outer3<T: Into<u64>>(t: T) -> u64 {{\n    mk(7u8, 7).wrapping_add(t.into())\n}}\n",
        inliner_library("", &format!("c({LOOP_CALL})"), "", true)
    )
}

const INLINER_OUTER_DRIVER: &str = "use std::hint::black_box as bb;\npub struct W(pub u64);\nimpl \
                                    From<W> for u64 {\n    fn from(w: W) -> u64 {\n        w.0\n    \
                                    }\n}\nfn main() {\n    let a = fixture::use_here();\n    let b \
                                    = fixture::outer(bb(5));\n    let c = \
                                    fixture::outer3(W(bb(9)));\n    println!(\"v {a} {b} \
                                    {c}\");\n}\n";

/// An `#[inline]` non-generic `mk2` handing its closure to `run`, which `+ Copy`
/// (no cleanup) keeps cheap enough for the MIR inliner.
fn inliner_copy_consumer_library() -> String {
    format!(
        "{MIX_HEAD}pub fn run<F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64 + \
         Copy>(f: F) -> u64 {{\n    f({LOOP_CALL})\n}}\n#[inline]\npub fn mk2(s: u64) -> u64 \
         {{\n    let c = {LOOP_CLOSURE};\n    run(c)\n}}\n#[inline(never)]\npub fn use_here() \
         -> u64 {{\n    mk2(bb(7))\n}}\n"
    )
}

const INLINER_MK2_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                                  fixture::use_here();\n    let b = fixture::mk2(bb(7));\n    \
                                  println!(\"v {a} {b}\");\n}\n";

/// A generic `mk` whose closure moves out of its captured `Box<u64>`: an 8-byte
/// by-value (`FnOnce`) environment, which rustc passes in a register.
fn inliner_fnonce_library() -> String {
    format!(
        "{MIX_HEAD}pub fn mk<T: Copy>(_t: T, s: Box<u64>) -> u64 {{\n    let c = move |a: u64| \
         -> u64 {{\n        let owned: Box<u64> = s;\n        let mut acc: u64 = a + \
         *owned;\n        for i in 0..bb(9u64) {{\n            acc = mix(acc, i);\n            \
         if bb(acc) % 3 == 0 {{\n                acc = mix(acc, 7);\n            }}\n        \
         }}\n        drop(owned);\n        acc\n    }};\n    c(1)\n}}\n#[inline(never)]\npub \
         fn use_here() -> u64 {{\n    mk(bb(7u8), Box::new(bb(7)))\n}}\n"
    )
}

const INLINER_FNONCE_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                                     fixture::use_here();\n    let b = fixture::mk(bb(7u8), \
                                     Box::new(bb(7)));\n    println!(\"v {a} {b}\");\n}\n";

/// The `#[inline(never)]` control's driver also instantiates `mk::<u16>`, which
/// the library does not.
const INLINER_NEVER_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                                    fixture::use_here();\n    let b = fixture::mk(bb(7u8), \
                                    bb(7));\n    let c = fixture::mk(bb(7u16), bb(9));\n    \
                                    println!(\"v {a} {b} {c}\");\n}\n";

/// The third verifier round's route: `mk` stores the closure in a local `Guard`
/// whose `Drop` impl calls it, so its MIR names the closure only in an
/// aggregate and a drop. An LLVM binary that compiles its own `Guard::drop`
/// called the bridge library's exported body by symbol (SIGSEGV at O2 against
/// `v 105302 105302`, measured at `126896d73`).
fn drop_guard_library(closure_attr: &str) -> String {
    format!(
        "#![feature(stmt_expr_attributes)]\nuse std::cell::Cell;\nuse std::hint::black_box as \
         bb;\npub struct Guard<'a, F: Fn(u64, u64, u64, u64, u64, u64, &'static str) -> u64> \
         {{\n    f: F,\n    out: &'a Cell<u64>,\n}}\nimpl<'a, F: Fn(u64, u64, u64, u64, u64, u64, \
         &'static str) -> u64> Drop for Guard<'a, F> {{\n    fn drop(&mut self) {{\n        \
         self.out.set((self.f)({STR_CALL}));\n    }}\n}}\npub fn mk<T: Copy>(_t: T, s: u64) -> \
         u64 {{\n    let out = Cell::new(0u64);\n    {{\n        let _g = Guard {{\n            \
         f: {closure_attr}{STR_CLOSURE},\n            out: &out,\n        }};\n    }}\n    \
         out.get()\n}}\n#[inline(never)]\npub fn use_here() -> u64 {{\n    mk(bb(7u8), \
         bb(11))\n}}\n"
    )
}

const DROP_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                           fixture::use_here();\n    let b = fixture::mk(bb(7u8), bb(11));\n    \
                           println!(\"v {a} {b}\");\n}\n";

/// The same route with a by-value (`FnOnce`) environment: an 8-byte `Tok`
/// moved out of the capture, called from `OnceG`'s `Drop` impl (the third
/// verifier round's `D11`: SIGSEGV at O2 against `v 973456009 973456009`).
const DROP_ONCE_LIBRARY: &str = "#![feature(stmt_expr_attributes)]\nuse std::cell::Cell;\nuse \
                                 std::hint::black_box as bb;\npub struct Tok(u64);\npub struct \
                                 OnceG<'a, F: FnOnce() -> u64> {\n    f: Option<F>,\n    out: &'a \
                                 Cell<u64>,\n}\nimpl<'a, F: FnOnce() -> u64> Drop for OnceG<'a, \
                                 F> {\n    fn drop(&mut self) {\n        if let Some(f) = \
                                 self.f.take() {\n            self.out.set(f());\n        }\n    \
                                 }\n}\n#[inline(never)]\npub fn mix(a: u64, b: u64) -> u64 {\n    \
                                 a.wrapping_mul(31).wrapping_add(b) ^ (a >> 7)\n}\npub fn mk<T: \
                                 Copy>(_t: T, s: u64) -> u64 {\n    let out = \
                                 Cell::new(0u64);\n    let tok = Tok(s * 3 + 1);\n    {\n        \
                                 let _g = OnceG {\n            f: Some(#[inline(never)] move || \
                                 -> u64 {\n                let t = tok;\n                let mut \
                                 acc = t.0;\n                for i in 0..bb(5u64) {\n                \
                                 acc = mix(acc, i);\n                }\n                acc\n     \
                                 }),\n            out: &out,\n        };\n    }\n    \
                                 out.get()\n}\n#[inline(never)]\npub fn use_here() -> u64 {\n    \
                                 mk(bb(7u8), bb(11))\n}\n";

/// `mk::<{closure in use_here}>`: rustc leaves an instance whose type argument
/// holds a closure no other crate can reach out of `exported_generic_symbols`,
/// but under generic sharing its partitioner still gives the instance and its
/// closure body external linkage.
fn private_instance_library() -> String {
    format!(
        "use std::hint::black_box as bb;\npub fn mk<T: Copy>(_t: T, s: u64) -> u64 {{\n    let c \
         = {STR_CLOSURE};\n    c({STR_CALL})\n}}\n#[inline(never)]\npub fn use_here() -> u64 \
         {{\n    let k = |x: u8| x;\n    mk(k, bb(7))\n}}\n"
    )
}

const PRIVATE_INSTANCE_DRIVER: &str = "use std::hint::black_box as bb;\nfn main() {\n    let a = \
                                       fixture::use_here();\n    let b = fixture::mk(bb(7u8), \
                                       bb(7));\n    println!(\"v {a} {b}\");\n}\n";

/// One program: its crates and the value LLVM's build prints (computed by hand,
/// or, for a closure that loops over `mix`, read from the LLVM control, which
/// every cell checks first).
struct Program {
    name: &'static str,
    upstream: Option<String>,
    library: String,
    driver: String,
    oracle: &'static str,
}

/// One cell: the program, which backend builds the library and the binary, at
/// which levels, and with which extra library and binary flags. Every crate
/// must compile and the program must print the oracle.
struct Cell {
    program: usize,
    library: &'static str,
    binary: &'static str,
    library_opt: &'static str,
    binary_opt: &'static str,
    library_flags: &'static [&'static str],
    binary_flags: &'static [&'static str],
}

fn programs() -> Vec<Program> {
    vec![
        Program {
            name: "pair_bool",
            upstream: None,
            library: PAIR_LIBRARY.to_owned(),
            driver: pair_driver("(u64, bool)"),
            oracle: "v 122 132\n",
        },
        Program {
            name: "pair_bool_inline_never",
            upstream: None,
            library: PAIR_INLINE_NEVER_LIBRARY.to_owned(),
            driver: pair_driver("(u64, bool)"),
            oracle: "v 122 132\n",
        },
        Program {
            name: "pair_u8",
            upstream: None,
            library: U8_PAIR_LIBRARY.to_owned(),
            driver: pair_driver("(u64, u8)"),
            oracle: "v 118 128\n",
        },
        Program {
            name: "copy_direct",
            upstream: None,
            library: copy_library("#[inline(never)] ", &format!("c({STR_CALL})"), ""),
            driver: COPY_DRIVER.to_owned(),
            oracle: "v 105298 105298\n",
        },
        Program {
            name: "copy_consumer",
            upstream: None,
            library: copy_library("#[inline(never)] ", "run(c)", ""),
            driver: COPY_DRIVER.to_owned(),
            oracle: "v 105298 105298\n",
        },
        Program {
            name: "copy_consumer_inline_never",
            upstream: None,
            library: copy_library("#[inline(never)] ", "run(c)", "#[inline(never)]\n"),
            driver: COPY_DRIVER.to_owned(),
            oracle: "v 105298 105298\n",
        },
        Program {
            name: "copy_closure_inlinable",
            upstream: None,
            library: copy_library("", &format!("c({STR_CALL})"), ""),
            driver: COPY_DRIVER.to_owned(),
            oracle: "v 105298 105298\n",
        },
        Program {
            name: "alias_field",
            upstream: None,
            library: field_library(TAIT_CLOSURE, TAIT_TY, STR_CALL),
            driver: field_driver("fixture::mk", STR_CALL),
            oracle: "v 105294 105294\n",
        },
        Program {
            name: "alias_slot",
            upstream: None,
            library: slot_library(),
            driver: field_driver("fixture::get", STR_CALL),
            oracle: "v 105294 105294\n",
        },
        Program {
            name: "alias_upstream",
            upstream: Some(upstream_alias(TAIT_CLOSURE, TAIT_TY)),
            library: upstream_library(UPSTREAM_MK.0, STR_CALL),
            driver: upstream_driver(UPSTREAM_MK.1, STR_CALL),
            oracle: "v 105294 105294\n",
        },
        Program {
            name: "alias_field_fit",
            upstream: None,
            library: field_library(FIT_CLOSURE, FIT_TY, FIT_CALL),
            driver: field_driver("fixture::mk", FIT_CALL),
            oracle: "v 105204 105204\n",
        },
        Program {
            name: "alias_upstream_fit",
            upstream: Some(upstream_alias(FIT_CLOSURE, FIT_TY)),
            library: upstream_library(UPSTREAM_MK.0, FIT_CALL),
            driver: upstream_driver(UPSTREAM_MK.1, FIT_CALL),
            oracle: "v 105204 105204\n",
        },
        Program {
            name: "alias_upstream_slot",
            upstream: Some(upstream_slot(TAIT_CLOSURE, TAIT_TY, false)),
            library: upstream_library(UPSTREAM_GET.0, STR_CALL),
            driver: upstream_driver(UPSTREAM_GET.1, STR_CALL),
            oracle: "v 105294 105294\n",
        },
        Program {
            name: "alias_upstream_slot_generic",
            upstream: Some(upstream_slot(TAIT_CLOSURE, TAIT_TY, true)),
            library: upstream_library(UPSTREAM_GET_LOC.0, STR_CALL),
            driver: upstream_driver(UPSTREAM_GET_LOC.1, STR_CALL),
            oracle: "v 105294 105294\n",
        },
        Program {
            name: "alias_upstream_slot_fit",
            upstream: Some(upstream_slot(FIT_CLOSURE, FIT_TY, false)),
            library: upstream_library(UPSTREAM_GET.0, FIT_CALL),
            driver: upstream_driver(UPSTREAM_GET.1, FIT_CALL),
            oracle: "v 105204 105204\n",
        },
        Program {
            name: "inliner_direct",
            upstream: None,
            library: inliner_library("", &format!("c({LOOP_CALL})"), "", false),
            driver: INLINER_DRIVER.to_owned(),
            oracle: "v 1378546575549278007 1378546575549278007\n",
        },
        Program {
            name: "inliner_copy_consumer",
            upstream: None,
            library: inliner_copy_consumer_library(),
            driver: INLINER_MK2_DRIVER.to_owned(),
            oracle: "v 1378546575549278007 1378546575549278007\n",
        },
        Program {
            name: "inliner_fnonce",
            upstream: None,
            library: inliner_fnonce_library(),
            driver: INLINER_FNONCE_DRIVER.to_owned(),
            oracle: "v 6295504286919691690 6295504286919691690\n",
        },
        Program {
            name: "inliner_outer",
            upstream: None,
            library: inliner_outer_library(),
            driver: INLINER_OUTER_DRIVER.to_owned(),
            oracle: "v 2757093151098556014 1378546575549278012 1378546575549278016\n",
        },
        Program {
            name: "inliner_parent_never",
            upstream: None,
            library: inliner_library("#[inline(never)]\n", &format!("c({LOOP_CALL})"), "", false),
            driver: INLINER_NEVER_DRIVER.to_owned(),
            oracle: "v 1378546575549278007 1378546575549278007 2881834583411141704\n",
        },
        Program {
            name: "inliner_consumer_never",
            upstream: None,
            library: inliner_library("", "run(c)", "#[inline(never)]\n", false),
            driver: INLINER_DRIVER.to_owned(),
            oracle: "v 1378546575549278007 1378546575549278007\n",
        },
        Program {
            name: "drop_guard",
            upstream: None,
            library: drop_guard_library("#[inline(never)] "),
            driver: DROP_DRIVER.to_owned(),
            oracle: "v 105302 105302\n",
        },
        Program {
            name: "drop_guard_plain",
            upstream: None,
            library: drop_guard_library(""),
            driver: DROP_DRIVER.to_owned(),
            oracle: "v 105302 105302\n",
        },
        Program {
            name: "drop_once",
            upstream: None,
            library: DROP_ONCE_LIBRARY.to_owned(),
            driver: DROP_DRIVER.to_owned(),
            oracle: "v 973456009 973456009\n",
        },
        Program {
            name: "private_instance",
            upstream: None,
            library: private_instance_library(),
            driver: PRIVATE_INSTANCE_DRIVER.to_owned(),
            oracle: "v 105298 105298\n",
        },
    ]
}

const LINK_DEAD_CODE: &[&str] = &["-Clink-dead-code"];
/// Generic sharing off, on a crate at a level (O0) where it is on by default.
const NO_SHARE_GENERICS: &[&str] = &["-Zshare-generics=no"];
/// rustc's MIR inliner, on a crate at a level where it is off by default.
const INLINE_MIR: &[&str] = &["-Zinline-mir=yes"];
/// Generic sharing, on a crate at a level (O2 / O3) where the MIR inliner runs
/// by default and sharing is off by default.
const SHARE_GENERICS: &[&str] = &["-Zshare-generics=yes"];

fn cell(
    program: usize,
    library: &'static str,
    binary: &'static str,
    library_opt: &'static str,
    binary_opt: &'static str,
    library_flags: &'static [&'static str],
) -> Cell {
    Cell {
        program,
        library,
        binary,
        library_opt,
        binary_opt,
        library_flags,
        binary_flags: &[],
    }
}

/// A cell whose binary gets extra flags.
fn cell_binary_flags(
    program: usize,
    library: &'static str,
    binary: &'static str,
    (library_opt, binary_opt): (&'static str, &'static str),
    binary_flags: &'static [&'static str],
) -> Cell {
    Cell {
        binary_flags,
        ..cell(program, library, binary, library_opt, binary_opt, &[])
    }
}

/// The cells the symbol rule pinned (as refusals where it refused, as admitted
/// runs where it admitted), each now a row that must run to LLVM's value.
fn cells() -> Vec<Cell> {
    vec![
        // 1. A linked body's extended lane: a bridge binary over an LLVM
        //    library's `(u64, bool)` body (refused under the symbol rule, arm
        //    (a)), the bridge body under an LLVM binary, and a `(u64, u8)` pair.
        cell(0, "llvm", "cg", "1", "1", LINK_DEAD_CODE),
        cell(0, "llvm", "cg", "s", "s", LINK_DEAD_CODE),
        cell(0, "cg", "llvm", "1", "1", LINK_DEAD_CODE),
        cell(1, "llvm", "cg", "2", "2", &[]),
        cell(2, "llvm", "cg", "1", "1", LINK_DEAD_CODE),
        // 2. Bodies rustc exports (refused under the symbol rule, arm (b)). An
        //    `#[inline(never)]` closure in an exported generic `mk::<u8>`,
        //    copied by a binary without sharing.
        cell(3, "cg", "llvm", "0", "2", &[]),
        cell(3, "cg", "llvm", "1", "3", &[]),
        cell(4, "cg", "llvm", "0", "2", &[]),
        // Every crate links the `#[inline(never)]` `run`, so only this crate
        // calls the body.
        cell(5, "cg", "llvm", "0", "2", &[]),
        cell(6, "cg", "llvm", "0", "2", &[]),
        // At O2 the closure that is not `#[inline(never)]` gets a private copy
        // in each codegen unit (internal linkage), also against a binary that
        // inlines `mk` and shares generics.
        cell(6, "cg", "llvm", "2", "2", &[]),
        cell_binary_flags(6, "cg", "llvm", ("2", "2"), SHARE_GENERICS),
        cell(6, "llvm", "cg", "2", "2", &[]),
        //    A closure type behind a `type_alias_impl_trait` alias.
        cell(7, "cg", "llvm", "0", "0", &[]),
        cell(8, "cg", "llvm", "0", "0", &[]),
        cell(9, "cg", "llvm", "0", "0", &[]),
        cell(10, "cg", "llvm", "0", "0", &[]),
        cell(11, "cg", "llvm", "0", "0", &[]),
        cell(11, "cg", "cg", "0", "0", &[]),
        cell(12, "cg", "llvm", "0", "0", &[]),
        cell(13, "cg", "llvm", "0", "0", &[]),
        cell(14, "cg", "llvm", "0", "0", &[]),
        cell(14, "cg", "cg", "0", "0", &[]),
        //    Another crate's MIR inliner.
        cell_binary_flags(15, "cg", "llvm", ("0", "0"), INLINE_MIR),
        cell_binary_flags(15, "cg", "llvm", ("0", "2"), SHARE_GENERICS),
        cell_binary_flags(15, "llvm", "cg", ("0", "0"), INLINE_MIR),
        cell_binary_flags(16, "cg", "llvm", ("0", "0"), INLINE_MIR),
        cell_binary_flags(17, "cg", "llvm", ("0", "0"), INLINE_MIR),
        cell(18, "cg", "llvm", "0", "0", INLINE_MIR),
        // An `#[inline(never)]` defining function and an `#[inline(never)]`
        // consumer: rustc exports the body at O0, gives it internal linkage at
        // O2 / O3.
        cell_binary_flags(19, "cg", "llvm", ("0", "0"), INLINE_MIR),
        cell_binary_flags(19, "cg", "llvm", ("2", "2"), SHARE_GENERICS),
        // The bridge binary links `mk::<u8>` and instantiates its own
        // `mk::<u16>` and closure body, which it gives internal linkage.
        cell_binary_flags(19, "llvm", "cg", ("0", "0"), INLINE_MIR),
        cell_binary_flags(20, "cg", "llvm", ("0", "0"), INLINE_MIR),
        cell_binary_flags(20, "cg", "llvm", ("3", "3"), SHARE_GENERICS),
        //    A `Drop` impl of a struct holding the closure (third verifier
        //    round): no call names the closure in `mk`'s MIR.
        cell(21, "cg", "llvm", "2", "2", &[]),
        cell(21, "llvm", "cg", "2", "2", &[]),
        cell_binary_flags(21, "cg", "llvm", ("0", "0"), NO_SHARE_GENERICS),
        cell(22, "cg", "llvm", "0", "2", &[]),
        cell(22, "cg", "llvm", "2", "2", &[]),
        cell(22, "llvm", "cg", "2", "2", &[]),
        cell(23, "cg", "llvm", "2", "2", &[]),
        // 3. External linkage without an export (refused under the symbol
        //    rule, arm (b)), and the same library without generic sharing.
        cell(24, "cg", "llvm", "0", "0", &[]),
        cell(24, "cg", "llvm", "0", "0", NO_SHARE_GENERICS),
    ]
}

fn compile(
    backend: &Path,
    lane: &str,
    opt: &str,
    dir: &Path,
    args: &[String],
    log: &str,
) -> (Output, String) {
    // Every crate of a cell is built into `dir`, which is also where the
    // binary finds the library's own dependency (the upstream crate).
    let mut command = rustc_command();
    command
        .args([
            "--target",
            TARGET,
            "-Ccodegen-units=1",
            "-Ztrust-ir-lower=on",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Ldependency={}", dir.display()))
        .args(args);
    if lane == "cg" {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=no-proof-certs");
    }
    run_bounded(&mut command, 600, &dir.join(log))
}

/// Builds `program`'s crates in `dir` (the upstream crate always by LLVM, at
/// the library's level), returning the binary, or which crate failed to
/// compile with its transcript.
fn build(
    backend: &Path,
    root: &Path,
    program: &Program,
    dir: &Path,
    (library, library_opt, library_flags): (&str, &str, &[&str]),
    (binary, binary_opt, binary_flags): (&str, &str, &[&str]),
) -> Result<PathBuf, (&'static str, String)> {
    std::fs::create_dir_all(dir).unwrap();
    let mut externs = Vec::new();
    if program.upstream.is_some() {
        let rlib = dir.join("libupstream.rlib");
        let (output, transcript) = compile(
            backend,
            "llvm",
            library_opt,
            dir,
            &[
                "--crate-type=rlib".to_owned(),
                "--crate-name=upstream".to_owned(),
                "-o".to_owned(),
                rlib.display().to_string(),
                root.join(format!("{}_upstream.rs", program.name))
                    .display()
                    .to_string(),
            ],
            "upstream.log",
        );
        assert!(
            output.status.success(),
            "{} upstream: {transcript}",
            program.name
        );
        externs.push(format!("--extern=upstream={}", rlib.display()));
    }
    let rlib = dir.join("libfixture.rlib");
    let mut args = vec![
        "--crate-type=rlib".to_owned(),
        "--crate-name=fixture".to_owned(),
        "-o".to_owned(),
        rlib.display().to_string(),
    ];
    args.extend(library_flags.iter().map(|flag| (*flag).to_owned()));
    args.extend(externs.iter().cloned());
    args.push(
        root.join(format!("{}_fixture.rs", program.name))
            .display()
            .to_string(),
    );
    let (output, transcript) = compile(backend, library, library_opt, dir, &args, "fixture.log");
    if !output.status.success() {
        return Err(("library", transcript));
    }
    let program_path = dir.join("program");
    let mut args = vec![
        "--crate-type=bin".to_owned(),
        "--crate-name=driver".to_owned(),
        format!("--extern=fixture={}", rlib.display()),
        "-o".to_owned(),
        program_path.display().to_string(),
    ];
    args.extend(binary_flags.iter().map(|flag| (*flag).to_owned()));
    args.extend(externs);
    args.push(
        root.join(format!("{}_driver.rs", program.name))
            .display()
            .to_string(),
    );
    let (output, transcript) = compile(backend, binary, binary_opt, dir, &args, "driver.log");
    if !output.status.success() {
        return Err(("binary", transcript));
    }
    Ok(program_path)
}

fn run_program(what: &str, program: &Path, oracle: &str) {
    let dir = program.parent().unwrap();
    let ran = checked(&mut Command::new(program), 60, &dir.join("run.log"));
    assert!(ran.stderr.is_empty(), "{what} wrote stderr");
    assert_eq!(String::from_utf8(ran.stdout).unwrap(), oracle, "{what}");
}

#[test]
fn no_proof_closure_body_boundary_paths_match_llvm() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-closure-boundary.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-closure-boundary-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let programs = programs();
    for program in &programs {
        std::fs::write(
            root.join(format!("{}_fixture.rs", program.name)),
            &program.library,
        )
        .unwrap();
        std::fs::write(
            root.join(format!("{}_driver.rs", program.name)),
            &program.driver,
        )
        .unwrap();
        if let Some(upstream) = &program.upstream {
            std::fs::write(root.join(format!("{}_upstream.rs", program.name)), upstream).unwrap();
        }
    }
    let cells = cells();
    let (mut runs, mut controls) = (0, 0);
    let mut controlled = std::collections::BTreeSet::new();
    for (index, cell) in cells.iter().enumerate() {
        let program = &programs[cell.program];
        let what = format!(
            "{} ({} library at O{} {:?}, {} binary at O{} {:?})",
            program.name,
            cell.library,
            cell.library_opt,
            cell.library_flags,
            cell.binary,
            cell.binary_opt,
            cell.binary_flags
        );
        // The LLVM control: the same crates, levels and flags, all built by
        // LLVM, print the independently computed value.
        if controlled.insert((
            cell.program,
            cell.library_opt,
            cell.binary_opt,
            cell.library_flags,
            cell.binary_flags,
        )) {
            let dir = root.join(format!("control{index}"));
            let built = build(
                &backend,
                root,
                program,
                &dir,
                ("llvm", cell.library_opt, cell.library_flags),
                ("llvm", cell.binary_opt, cell.binary_flags),
            );
            let path = match built {
                Ok(path) => path,
                Err((side, transcript)) => {
                    panic!("{what}: the LLVM control's {side} does not build: {transcript}")
                }
            };
            run_program(&format!("{what}: LLVM control"), &path, program.oracle);
            controls += 1;
        }
        let dir = root.join(format!("cell{index}"));
        let built = build(
            &backend,
            root,
            program,
            &dir,
            (cell.library, cell.library_opt, cell.library_flags),
            (cell.binary, cell.binary_opt, cell.binary_flags),
        );
        match built {
            Ok(path) => {
                run_program(&what, &path, program.oracle);
                runs += 1;
            }
            Err((side, transcript)) => {
                panic!("{what}: the {side} must compile: {transcript}");
            }
        }
    }
    assert_eq!(sha256(&backend), digest);
    assert_eq!(runs, cells.len());
    eprintln!(
        "closure-body boundary paths: {runs} native runs, none refused, {controls} LLVM controls"
    );
}
