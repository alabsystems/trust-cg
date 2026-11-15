// trust-cg-codegen/tests/wasm_value_domain_differential.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Execution differential for the wasm lane's Rust-shaped value domain: the
//! trust-ir REFERENCE INTERPRETER and the COMPILED wasm module (run by node)
//! agree on every function below, over seeded inputs.
//!
//! One module, pinned to wasm32, is both interpreted (the interpreter executes
//! wasm32 layouts — 32-bit pointers, the canonical scalar table) and compiled.
//! Every function under test has the signature `(i64, i64) -> i64`, so node
//! can drive it with `BigInt`s; inside, the functions exercise what real Rust
//! lowers to and the pre-extension lane refused:
//!
//! * checked arithmetic (`add/sub/mul.overflow`) at every integer width;
//! * the bit intrinsics (`ctlz`, `cttz`, `bswap`, `bitreverse`, `ctpop`) and
//!   the rotates at every width;
//! * `fmin` / `fmax` (NaN yields the other operand), `fcopysign`, `frem`
//!   (through the closed module's trust-ir `fmod` helper);
//! * memory-carried values: structs built by `insertfield` and
//!   `make_aggregate`, passed to and returned from Rust-convention calls
//!   (by address / `sret`), swapped through block parameters of a loop (the
//!   two-phase edge copy), stored and loaded; nested tuples; constant arrays
//!   with dynamic `extractelement` / `insertelement`;
//! * enums: the canonical tagged union with per-variant layouts, explicit
//!   discriminants, and a producer niche descriptor round-tripped through
//!   memory;
//! * fat pointers, atomics, `memcopy` / `memset`, 128-bit resizes.
//!
//! A divergence is a miscompile. Node is required to execute the wasm; its
//! absence is a loud SKIP, never a silent pass.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};

/// Rename `%name` values and `bbname` blocks to the text format's numeric
/// spellings, per function, in order of first appearance — so the test IR can
/// be written with readable names.
fn number_names(text: &str) -> String {
    use std::collections::HashMap;
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.starts_with("fn ")
            || line.starts_with("internal fn ")
            || line.starts_with("rustcc fn ")
        {
            values.clear();
            blocks.clear();
        }
        let bytes = line.as_bytes();
        let mut i = 0;
        let ident_end = |mut j: usize| {
            while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                j += 1;
            }
            j
        };
        while i < bytes.len() {
            let word_start =
                i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
            if bytes[i] == b'%' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
                let end = ident_end(i + 1);
                let n = values.len();
                let id = *values.entry(line[i + 1..end].to_string()).or_insert(n);
                let _ = write!(out, "%{id}");
                i = end;
            } else if word_start
                && line[i..].starts_with("bb")
                && i + 2 < bytes.len()
                && bytes[i + 2].is_ascii_alphabetic()
            {
                let end = ident_end(i + 2);
                let n = blocks.len();
                let id = *blocks.entry(line[i + 2..end].to_string()).or_insert(n);
                let _ = write!(out, "bb{id}");
                i = end;
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }
        out.push('\n');
    }
    out
}

/// Integer types by (name, bits, signed).
const INTS: &[(&str, u32, bool)] = &[
    ("i8", 8, true),
    ("u8", 8, false),
    ("i16", 16, true),
    ("u16", 16, false),
    ("i32", 32, true),
    ("u32", 32, false),
    ("i64", 64, true),
    ("u64", 64, false),
];

/// `%x: T` from the i64 argument `%src` (truncate or reinterpret).
fn narrow_from_i64(t: &str, bits: u32, src: &str, dst: &str) -> String {
    match (bits, t) {
        (64, "i64") => format!("    %{dst} = copy i64 %{src}\n"),
        (64, _) => format!("    %{dst} = bitcast i64 %{src} to {t}\n"),
        _ => format!("    %{dst} = trunc i64 %{src} to {t}\n"),
    }
}

/// `%dst: i64` from `%src: T` (sign- or zero-extended).
fn widen_to_i64(t: &str, bits: u32, signed: bool, src: &str, dst: &str) -> String {
    match (bits, t) {
        (64, "i64") => format!("    %{dst} = copy i64 %{src}\n"),
        (64, _) => format!("    %{dst} = bitcast {t} %{src} to i64\n"),
        _ if signed => format!("    %{dst} = sext {t} %{src} to i64\n"),
        _ => format!("    %{dst} = zext {t} %{src} to i64\n"),
    }
}

/// The generated scalar-operator functions: `(name, body)`.
fn scalar_functions() -> Vec<(String, String)> {
    let mut out = Vec::new();
    for &(t, bits, signed) in INTS {
        for op in ["add", "sub", "mul"] {
            let mut body = String::new();
            body.push_str(&narrow_from_i64(t, bits, "a", "x"));
            body.push_str(&narrow_from_i64(t, bits, "b", "y"));
            let _ = writeln!(body, "    %v, %o = {op}.overflow {t} %x, %y");
            body.push_str(&widen_to_i64(t, bits, signed, "v", "w"));
            body.push_str("    %oz = zext bool %o to i64\n");
            body.push_str("    %c62 = const i64 62\n");
            body.push_str("    %ob = shl i64 %oz, %c62\n");
            body.push_str("    %r = xor i64 %w, %ob\n");
            body.push_str("    ret %r\n");
            out.push((format!("ovf_{op}_{t}"), body));
        }
        for op in ["ctlz", "cttz", "bswap", "bitreverse", "ctpop"] {
            let mut body = String::new();
            body.push_str(&narrow_from_i64(t, bits, "a", "x"));
            let _ = writeln!(body, "    %v = {op} {t} %x");
            body.push_str(&widen_to_i64(t, bits, signed, "v", "r"));
            body.push_str("    ret %r\n");
            out.push((format!("{op}_{t}"), body));
        }
        for op in ["rotl", "rotr"] {
            let mut body = String::new();
            body.push_str(&narrow_from_i64(t, bits, "a", "x"));
            body.push_str(&narrow_from_i64(t, bits, "b", "y"));
            let _ = writeln!(body, "    %v = {op} {t} %x, %y");
            body.push_str(&widen_to_i64(t, bits, signed, "v", "r"));
            body.push_str("    ret %r\n");
            out.push((format!("{op}_{t}"), body));
        }
    }
    for op in ["fmin", "fmax", "fcopysign", "frem", "fadd"] {
        out.push((
            format!("{op}_f64"),
            format!(
                "    %x = bitcast i64 %a to f64\n    %y = bitcast i64 %b to f64\n    \
                 %v = {op} f64 %x, %y\n    %r = bitcast f64 %v to i64\n    ret %r\n"
            ),
        ));
        out.push((
            format!("{op}_f32"),
            format!(
                "    %xi = trunc i64 %a to u32\n    %yi = trunc i64 %b to u32\n    \
                 %x = bitcast u32 %xi to f32\n    %y = bitcast u32 %yi to f32\n    \
                 %v = {op} f32 %x, %y\n    %vi = bitcast f32 %v to u32\n    \
                 %r = zext u32 %vi to i64\n    ret %r\n"
            ),
        ));
    }
    out
}

/// 128-bit integer functions: operands are full 128-bit patterns built from
/// both inputs, and every 128-bit result folds to `lo ^ hi * 31`.
fn wide_functions() -> Vec<(String, String)> {
    let mut out = Vec::new();
    for t in ["u128", "i128"] {
        let prelude = format!(
            "    %za = zext i64 %a to {t}\n    %zb = zext i64 %b to {t}\n    \
             %sa = sext i64 %a to {t}\n    %sb = sext i64 %b to {t}\n    \
             %c64 = const {t} 64\n    %hi = shl {t} %za, %c64\n    %x = or {t} %hi, %zb\n    \
             %y = mul {t} %sb, %sa\n    %c127 = const i64 127\n    %bm = and i64 %b, %c127\n    \
             %amt = zext i64 %bm to {t}\n"
        );
        let fold = format!(
            "    %lo = trunc {t} %r to u64\n    %sh = lshr {t} %r, %c64\n    \
             %h = trunc {t} %sh to u64\n    %c31 = const u64 31\n    %hm = mul u64 %h, %c31\n    \
             %f = xor u64 %lo, %hm\n    %out = bitcast u64 %f to i64\n    ret %out\n"
        );
        let mut bin = |name: &str, body: &str| {
            out.push((format!("w{name}_{t}"), format!("{prelude}{body}{fold}")));
        };
        for op in ["add", "sub", "mul", "and", "or", "xor"] {
            bin(op, &format!("    %r = {op} {t} %x, %y\n"));
        }
        for op in ["shl", "lshr", "ashr"] {
            bin(op, &format!("    %r = {op} {t} %x, %amt\n"));
        }
        for op in ["rotl", "rotr"] {
            bin(op, &format!("    %r = {op} {t} %x, %zb\n"));
        }
        let (div, rem) = if t == "u128" {
            ("udiv", "urem")
        } else {
            ("sdiv", "srem")
        };
        for op in [div, rem] {
            bin(
                op,
                &format!(
                    "    %one = const {t} 1\n    %d = or {t} %y, %one\n    %r = {op} {t} %x, %d\n"
                ),
            );
        }
        for op in ["add", "sub", "mul"] {
            bin(
                &format!("ovf{op}"),
                &format!(
                    "    %v, %o = {op}.overflow {t} %x, %y\n    %oz = zext bool %o to {t}\n    \
                     %c62 = const {t} 62\n    %ob = shl {t} %oz, %c62\n    %r = xor {t} %v, %ob\n"
                ),
            );
        }
        for op in ["neg", "not", "ctpop", "ctlz", "cttz", "bswap", "bitreverse"] {
            bin(op, &format!("    %r = {op} {t} %x\n"));
        }
        for cmp in [
            "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
        ] {
            out.push((
                format!("wcmp{cmp}_{t}"),
                format!(
                    "{prelude}    %c = icmp {cmp} {t} %x, %y\n    %r = zext bool %c to i64\n    \
                     ret %r\n"
                ),
            ));
        }
    }
    out
}

/// 128-bit `mul.overflow` over the edge classes of the lane's two-limb
/// lowering (`lower_wide_overflow`), each result folded as in
/// [`wide_functions`] with the overflow flag at bit 62. Over the input grid the
/// operands reach 0, 1, -1, MAX, MIN, `MIN * -1`, the 2^63/2^64 limb
/// boundaries (`(2^64-1)^2`), and power-of-two products whose exponents sum to
/// 126..=129: one bit below, on, and one bit above both the unsigned and the
/// signed overflow boundary, with either sign.
fn mul_overflow_edge_functions() -> Vec<(String, String)> {
    let mut out = Vec::new();
    for t in ["u128", "i128"] {
        let prelude = format!(
            "    %za = zext i64 %a to {t}\n    %zb = zext i64 %b to {t}\n    \
             %sa = sext i64 %a to {t}\n    %sb = sext i64 %b to {t}\n    \
             %c64 = const {t} 64\n    %one = const {t} 1\n    %c127 = const i64 127\n"
        );
        let fold = format!(
            "    %v, %o = mul.overflow {t} %x, %y\n    %oz = zext bool %o to {t}\n    \
             %c62 = const {t} 62\n    %ob = shl {t} %oz, %c62\n    %r = xor {t} %v, %ob\n    \
             %lo = trunc {t} %r to u64\n    %sh = lshr {t} %r, %c64\n    \
             %h = trunc {t} %sh to u64\n    %c31 = const u64 31\n    %hm = mul u64 %h, %c31\n    \
             %f = xor u64 %lo, %hm\n    %out = bitcast u64 %f to i64\n    ret %out\n"
        );
        // `{t}` in a body names the operand type.
        let mut case = |name: &str, body: &str| {
            let body = body.replace("{t}", t);
            out.push((format!("mulo_{name}_{t}"), format!("{prelude}{body}{fold}")));
        };
        // Both operands below 2^64: the largest product is (2^64-1)^2.
        case("narrow", "    %x = copy {t} %za\n    %y = copy {t} %zb\n");
        // A full-width pattern times a sign-extended 64-bit value: a = MIN,
        // b = 0 gives MIN; a = -1, b = -1 gives -1 (u128::MAX); b = -1 is -1.
        case(
            "wide_by_narrow",
            "    %hi = shl {t} %sa, %c64\n    %x = or {t} %hi, %zb\n    %y = copy {t} %sb\n",
        );
        // Two full-width patterns.
        case(
            "wide_by_wide",
            "    %hi = shl {t} %sa, %c64\n    %x = or {t} %hi, %zb\n    \
             %hy = shl {t} %sb, %c64\n    %y = or {t} %hy, %za\n",
        );
        // `(a << 64) * b`: a = MIN and b = -1 is `MIN * -1`.
        case(
            "high_by_narrow",
            "    %x = shl {t} %sa, %c64\n    %y = copy {t} %sb\n",
        );
        // 2^i * (+-2^j) with i + j = 126 + (b & 3), and i = a & 127.
        case(
            "pow2",
            "    %i = and i64 %a, %c127\n    %iz = zext i64 %i to {t}\n    \
             %x = shl {t} %one, %iz\n    %c3 = const i64 3\n    %b3 = and i64 %b, %c3\n    \
             %c126 = const i64 126\n    %e = add i64 %c126, %b3\n    %d = sub i64 %e, %i\n    \
             %j = and i64 %d, %c127\n    %jz = zext i64 %j to {t}\n    \
             %y0 = shl {t} %one, %jz\n    %c4 = const i64 4\n    %b4 = and i64 %b, %c4\n    \
             %zero = const i64 0\n    %ng = icmp ne i64 %b4, %zero\n    %yn = neg {t} %y0\n    \
             %y = select {t} %ng, %yn, %y0\n",
        );
    }
    out
}

/// Hand-written functions over memory-carried values (text bodies after the
/// `fn` line; each gets `bbentry(%a: i64, %b: i64)`).
const AGGREGATE_FUNCTIONS: &str = r#"
rustcc fn @p_weigh(functy.1) {
bbentry(%p: struct.0):
    %x = extractfield i32 %p, 0
    %y = extractfield i32 %p, 1
    %c3 = const i32 3
    %x3 = mul i32 %x, %c3
    %s = sub i32 %x3, %y
    ret %s
}

rustcc fn @p_make(functy.2) {
bbentry(%x: i32, %y: i32):
    %p = make_aggregate struct.0 (%y, %x)
    ret %p
}

rustcc fn @pair_divmod(functy.3) {
bbentry(%x: i32, %y: i32):
    %c7 = const i32 7
    %y7 = or i32 %y, %c7
    %q = sdiv i32 %x, %y7
    %r = srem i32 %x, %y7
    %rb = trunc i32 %r to u8
    ret %q, %rb
}

fn @pair_return(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %y = trunc i64 %b to i32
    %q, %rb = call @func.2(%x, %y)
    %qw = sext i32 %q to i64
    %rw = zext u8 %rb to i64
    %c32 = const i64 32
    %rs = shl i64 %rw, %c32
    %t = xor i64 %qw, %rs
    ret %t
}

fn @struct_by_value(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %y = trunc i64 %b to i32
    %p0 = const struct.0 { 0, 0 }
    %p1 = insertfield struct.0 %p0, 0, %x
    %p2 = insertfield struct.0 %p1, 1, %y
    %s = call @func.0(%p2)
    %r = sext i32 %s to i64
    ret %r
}

fn @struct_sret(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %y = trunc i64 %b to i32
    %p = call @func.1(%x, %y)
    %f0 = extractfield i32 %p, 0
    %f1 = extractfield i32 %p, 1
    %c7 = const i32 7
    %m = mul i32 %f1, %c7
    %d = sub i32 %f0, %m
    %r = sext i32 %d to i64
    ret %r
}

fn @struct_loop_swap(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %y = trunc i64 %b to i32
    %pa = make_aggregate struct.0 (%x, %y)
    %pb = make_aggregate struct.0 (%y, %x)
    %c7 = const i64 7
    %n = and i64 %b, %c7
    %zero = const i64 0
    br bbhead(%pa, %pb, %zero)
bbhead(%p: struct.0, %q: struct.0, %i: i64):
    %more = icmp ult i64 %i, %n
    condbr %more, bbbody, bbdone
bbbody:
    %one = const i64 1
    %i2 = add i64 %i, %one
    %qx = extractfield i32 %q, 0
    %c1 = const i32 1
    %qx1 = add i32 %qx, %c1
    %q2 = insertfield struct.0 %q, 0, %qx1
    br bbhead(%q2, %p, %i2)
bbdone:
    %p0 = extractfield i32 %p, 0
    %p1 = extractfield i32 %p, 1
    %q0 = extractfield i32 %q, 0
    %c5 = const i32 5
    %t = mul i32 %p1, %c5
    %u = add i32 %p0, %t
    %c11 = const i32 11
    %w = mul i32 %q0, %c11
    %z = xor i32 %u, %w
    %r = sext i32 %z to i64
    ret %r
}

fn @struct_memory(functy.0) {
bbentry(%a: i64, %b: i64):
    %slot = alloca struct.0
    %x = trunc i64 %a to i32
    %y = trunc i64 %b to i32
    %p = make_aggregate struct.0 (%x, %y)
    store struct.0 %p, ptr %slot
    %q = load struct.0, ptr %slot
    %qy = extractfield i32 %q, 1
    %q2 = insertfield struct.0 %q, 0, %qy
    store struct.0 %q2, ptr %slot
    %r0 = load i32, ptr %slot
    %r = sext i32 %r0 to i64
    ret %r
}

fn @tuple_nested(functy.0) {
bbentry(%a: i64, %b: i64):
    %y = trunc i64 %b to i32
    %c = trunc i64 %a to i8
    %inner = make_aggregate (i32, i8) (%y, %c)
    %outer = make_aggregate (i64, (i32, i8)) (%a, %inner)
    %got = extractfield (i32, i8) %outer, 1
    %gc = extractfield i8 %got, 1
    %gy = extractfield i32 %got, 0
    %ga = extractfield i64 %outer, 0
    %gcw = sext i8 %gc to i64
    %gyw = sext i32 %gy to i64
    %s = add i64 %gcw, %gyw
    %r = xor i64 %s, %ga
    ret %r
}

fn @array_dynamic(functy.0) {
bbentry(%a: i64, %b: i64):
    %arr = const [ty.0 x 8] array[ 3, 1, 4, 1, 5, 9, 2, 6 ]
    %c7 = const i64 7
    %ia = and i64 %a, %c7
    %i = trunc i64 %ia to usize
    %ib = and i64 %b, %c7
    %j = trunc i64 %ib to usize
    %v = trunc i64 %b to i32
    %arr2 = insertelement [ty.0 x 8] %arr, %j, %v
    %e0 = extractelement i32 %arr2, %i
    %e1 = extractelement i32 %arr, %i
    %s = add i32 %e0, %e1
    %r = sext i32 %s to i64
    ret %r
}

fn @enum_option(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %zero = const i64 0
    %some = icmp sgt i64 %b, %zero
    condbr %some, bbmksome, bbmknone
bbmksome:
    %e1 = make_aggregate enum.0 variant 1 (%x)
    br bbjoin(%e1)
bbmknone:
    %e0 = const enum.0 { 0 }
    br bbjoin(%e0)
bbjoin(%e: enum.0):
    %tag = extractfield u32 %e, 0
    switch %tag [ 1: bbisSome default: bbisNone ]
bbisSome:
    %p = extractfield i32 %e, 1
    %c2 = const i32 2
    %p2 = mul i32 %p, %c2
    %r1 = sext i32 %p2 to i64
    ret %r1
bbisNone:
    %m = const i64 -77
    ret %m
}

fn @enum_multi(functy.0) {
bbentry(%a: i64, %b: i64):
    %c3 = const i64 3
    %sel = and i64 %b, %c3
    %x8 = trunc i64 %a to u8
    %x32 = trunc i64 %a to u32
    %sw = trunc i64 %sel to u32
    switch %sw [ 0: bbmka 1: bbmkb default: bbmkc ]
bbmka:
    %ea = make_aggregate enum.1 variant 0 (%x8, %x32)
    br bbjoin(%ea)
bbmkb:
    %eb = make_aggregate enum.1 variant 1 (%a)
    br bbjoin(%eb)
bbmkc:
    %ec = make_aggregate enum.1 variant 2 ()
    br bbjoin(%ec)
bbjoin(%e: enum.1):
    %slot = alloca enum.1
    store enum.1 %e, ptr %slot
    %f = load enum.1, ptr %slot
    %tag = extractfield i8 %f, 0
    %tw = sext i8 %tag to i64
    switch %tag [ -3: bbisa 17: bbisb default: bbisc ]
bbisa:
    %a1 = extractfield u8 %f, 1
    %a2 = extractfield u32 %f, 2
    %a1w = zext u8 %a1 to i64
    %a2w = zext u32 %a2 to i64
    %sa = add i64 %a1w, %a2w
    %ra = add i64 %sa, %tw
    ret %ra
bbisb:
    %b1 = extractfield i64 %f, 1
    %rb = sub i64 %b1, %tw
    ret %rb
bbisc:
    ret %tw
}

fn @enum_niche(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to u32
    %one = const u32 1
    %nz = or u32 %x, %one
    %zero = const i64 0
    %some = icmp slt i64 %b, %zero
    condbr %some, bbmksome, bbmknone
bbmksome:
    %e1 = make_aggregate enum.2 variant 1 (%nz)
    br bbjoin(%e1)
bbmknone:
    %e0 = make_aggregate enum.2 variant 0 ()
    br bbjoin(%e0)
bbjoin(%e: enum.2):
    %slot = alloca enum.2
    store enum.2 %e, ptr %slot
    %raw = load u32, ptr %slot
    %f = load enum.2, ptr %slot
    %tag = extractfield u32 %f, 0
    %tw = zext u32 %tag to i64
    %rw = zext u32 %raw to i64
    %c40 = const i64 40
    %tt = shl i64 %tw, %c40
    %r = xor i64 %tt, %rw
    ret %r
}

fn @fat_slice(functy.0) {
bbentry(%a: i64, %b: i64):
    %buf = alloca [ty.0 x 4]
    %c0 = const usize 0
    %e0p = gep i32, ptr %buf, %c0
    %x = trunc i64 %a to i32
    store i32 %x, ptr %e0p
    %c1 = const usize 1
    %e1p = gep i32, ptr %buf, %c1
    %y = trunc i64 %b to i32
    store i32 %y, ptr %e1p
    %c3 = const i64 3
    %lenw = and i64 %b, %c3
    %len = trunc i64 %lenw to u32
    %s = ptr_from_parts fatptr<slice ty.0> ptr %buf, u32 %len
    %d = ptr_data fatptr<slice ty.0> %s
    %m = ptr_metadata fatptr<slice ty.0> %s to u32
    %e1p2 = gep i32, ptr %d, %c1
    %v = load i32, ptr %e1p2
    %vw = sext i32 %v to i64
    %mw = zext u32 %m to i64
    %c32 = const i64 32
    %ms = shl i64 %mw, %c32
    %r = xor i64 %vw, %ms
    ret %r
}

fn @atomics(functy.0) {
bbentry(%a: i64, %b: i64):
    %slot = alloca u32
    %x = trunc i64 %a to u32
    %y = trunc i64 %b to u32
    atomic_store seq_cst u32 %x, ptr %slot
    %old = atomicrmw add seq_cst u32 ptr %slot, %y
    %mx = atomicrmw umax seq_cst u32 ptr %slot, %x
    %cur, %ok = cmpxchg u32 ptr %slot, %old, %y seq_cst seq_cst
    %fin = atomic_load seq_cst u32, ptr %slot
    %t1 = xor u32 %old, %mx
    %t2 = add u32 %t1, %cur
    %t3 = xor u32 %t2, %fin
    %okw = zext bool %ok to u32
    %c31 = const u32 31
    %okb = shl u32 %okw, %c31
    %t4 = or u32 %t3, %okb
    %r = zext u32 %t4 to i64
    ret %r
}

fn @bulk_memory(functy.0) {
bbentry(%a: i64, %b: i64):
    %buf = alloca [ty.1 x 32]
    %byte = trunc i64 %a to u8
    %c15 = const i64 15
    %nw = and i64 %b, %c15
    %n = trunc i64 %nw to usize
    %c32 = const usize 32
    %z = const u8 0
    memset ptr %buf, %z, %c32
    memset ptr %buf, %byte, %n
    %c3 = const usize 3
    %dst = gep u8, ptr %buf, %c3
    memcopy overlap ptr %dst, ptr %buf, %n
    %c0 = const usize 0
    %w0p = gep u64, ptr %buf, %c0
    %w0 = load u64, ptr %w0p
    %c1 = const usize 1
    %w1p = gep u64, ptr %buf, %c1
    %w1 = load u64, ptr %w1p
    %c7 = const u64 7
    %w1s = mul u64 %w1, %c7
    %s = xor u64 %w0, %w1s
    %r = bitcast u64 %s to i64
    ret %r
}

fn @wide_resize(functy.0) {
bbentry(%a: i64, %b: i64):
    %slot = alloca u128
    %w = sext i64 %a to i128
    %u = zext i64 %b to u128
    store i128 %w, ptr %slot
    %c8 = const usize 1
    %hi = gep u64, ptr %slot, %c8
    %h = load u64, ptr %hi
    %lo = trunc u128 %u to u64
    %x = xor u64 %h, %lo
    %r = bitcast u64 %x to i64
    ret %r
}
"#;

/// The test module text and the names of its `(i64, i64) -> i64` functions.
fn build_module() -> (Module, Vec<String>) {
    let mut text = String::from(
        "; TrustIr text format v1\nmodule \"wasm_value_domain\"\ntarget \
         \"wasm32-unknown-unknown\" 4 little\n\n",
    );
    text.push_str("struct @P { : i32 @0, : i32 @4 } size=8 align=4 id=0\n\n");
    text.push_str("enum @Opt repr(u32) { None = 0, Some(i32) = 1 } id=0\n\n");
    text.push_str("enum @Multi repr(i8) { A(u8, u32) = -3, B(i64) = 17, C = 40 } id=1\n\n");
    text.push_str(
        "enum @NzOpt repr(u32) { None = 0, Some(u32) = 1 } layout(niche untagged=1 \
         variants=0..=0 start=0 lane=u32@0 size=4 align=4 offsets=[[], [0]]) id=2\n\n",
    );
    text.push_str("type ty.0 = i32\ntype ty.1 = u8\n\n");
    text.push_str("functy.0 = (i64, i64) -> (i64)\n\n");
    text.push_str("functy.1 = (struct.0) -> (i32)\n\n");
    text.push_str("functy.2 = (i32, i32) -> (struct.0)\n\n");
    text.push_str("functy.3 = (i32, i32) -> (i32, u8)\n\n");
    let mut names = Vec::new();
    text.push_str(AGGREGATE_FUNCTIONS);
    for line in AGGREGATE_FUNCTIONS.lines() {
        if let Some(rest) = line.strip_prefix("fn @") {
            names.push(rest.split('(').next().unwrap().to_string());
        }
    }
    for (name, body) in scalar_functions()
        .into_iter()
        .chain(wide_functions())
        .chain(mul_overflow_edge_functions())
    {
        let _ = write!(
            text,
            "\nfn @{name}(functy.0) {{\nbbentry(%a: i64, %b: i64):\n{body}}}\n"
        );
        names.push(name);
    }
    let text = number_names(&text);
    let module = parser::parse_module(&text).unwrap_or_else(|e| {
        let numbered: String = text
            .lines()
            .enumerate()
            .map(|(i, l)| format!("{:4} {l}\n", i + 1))
            .collect();
        panic!("test module failed to parse: {e}\n{numbered}")
    });
    (module, names)
}

/// Deterministic inputs: edge values crossed, then an LCG.
fn inputs() -> Vec<(i64, i64)> {
    let edges: [i64; 14] = [
        0,
        1,
        -1,
        2,
        7,
        -8,
        127,
        -128,
        255,
        65535,
        i32::MAX as i64,
        i32::MIN as i64,
        i64::MAX,
        i64::MIN,
    ];
    let mut out = Vec::new();
    for &a in &edges {
        for &b in &edges {
            out.push((a, b));
        }
    }
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        s as i64
    };
    for _ in 0..300 {
        let (a, b) = (next(), next());
        // Mix in narrow-looking values so the narrow paths see carries.
        out.push((a, b));
        out.push((a >> 40, b >> 56));
    }
    out
}

fn node() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

fn i64_value(v: i64) -> InterpretValue {
    InterpretValue::int(Ty::I64, i128::from(v)).expect("i64 value")
}

/// The interpreter's answer, or `None` when the reference execution refuses
/// the input (undefined behaviour — e.g. `frem` of an unrepresentable
/// operand is not UB, but an assert failure would be).
fn interpret(module: &Module, name: &str, a: i64, b: i64) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let interp = Interpreter::with_module(module).with_options(InterpretOptions {
        fuel: 10_000_000,
        max_call_depth: 64,
        panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
    });
    let out = interp
        .execute_func(f.id, vec![i64_value(a), i64_value(b)])
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
        other => panic!("{name} returned {other:?}"),
    }
}

/// Float results compare modulo NaN payloads: two NaNs agree.
fn agree(name: &str, want: i64, got: i64) -> bool {
    if want == got {
        return true;
    }
    if name.ends_with("_f64") {
        return f64::from_bits(want as u64).is_nan() && f64::from_bits(got as u64).is_nan();
    }
    if name.ends_with("_f32") {
        return f32::from_bits(want as u32).is_nan() && f32::from_bits(got as u32).is_nan();
    }
    false
}

/// The object lane refuses a `CallingConv::Rust` aggregate at a link
/// boundary (rustc's own Rust ABI for it differs from this lane's), while the
/// lane lowers the two conventions identically: the linked object is
/// compiled from the module's C spelling, and the interpreter keeps the
/// original.
fn c_spelling(module: &Module) -> Module {
    let mut m = module.clone();
    for f in &mut m.functions {
        f.calling_conv = trust_ir::CallingConv::C;
        for node in f.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
            if let trust_ir::Inst::CallIndirect { calling_conv, .. } = &mut node.inst {
                *calling_conv = trust_ir::CallingConv::C;
            }
        }
    }
    m
}

#[test]
fn interpreter_and_compiled_wasm_agree_on_the_value_domain() {
    let (module, names) = build_module();
    let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile: {e}"));
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&bytes)
        .unwrap_or_else(|e| panic!("the compiled module does not validate: {e}"));
    // The in-tree structural checker (its own decoder, the spec's operand-stack
    // typing) must HOLD — not merely fail to refute — on every function.
    let verdict = trust_cg_verify::wasm_cfg_proofs::check_module_structure(&bytes);
    assert!(
        verdict.holds(),
        "CFG structural invariant on the closed module: {verdict}"
    );

    let inputs = inputs();
    let mut expected: Vec<(String, Vec<Option<i64>>)> = Vec::new();
    let mut unexercised = Vec::new();
    for name in &names {
        let col: Vec<Option<i64>> = inputs
            .iter()
            .map(|&(a, b)| interpret(&module, name, a, b))
            .collect();
        // A function the reference refuses on most inputs checks nothing.
        let ran = col.iter().filter(|v| v.is_some()).count();
        if ran * 2 < inputs.len() {
            let (a, b) = inputs[col.iter().position(Option::is_none).unwrap_or(0)];
            let f = module.function_by_name(name).expect("function");
            let why = Interpreter::with_module(&module)
                .execute_func(f.id, vec![i64_value(a), i64_value(b)])
                .err()
                .map(|e| e.to_string());
            unexercised.push(format!("{name}: {ran}/{} ran; e.g. {why:?}", inputs.len()));
        }
        expected.push((name.clone(), col));
    }
    assert!(
        unexercised.is_empty(),
        "the reference interpreter refused these functions:\n{}",
        unexercised.join("\n")
    );

    let Some(node) = node() else {
        eprintln!("SKIP interpreter_and_compiled_wasm_agree_on_the_value_domain: node not on PATH");
        return;
    };
    let checks = run_and_compare(&node, &bytes, &names, &inputs, &expected, "closed");
    eprintln!(
        "wasm value-domain differential: {checks} checks over {} functions agree",
        names.len()
    );
}

/// Run every function of the (closed or linked) module under node and compare
/// with the interpreter's column. Returns the number of checks.
fn run_and_compare(
    node: &std::path::Path,
    bytes: &[u8],
    names: &[String],
    inputs: &[(i64, i64)],
    expected: &[(String, Vec<Option<i64>>)],
    tag: &str,
) -> usize {
    let dir = std::env::temp_dir().join(format!("tcg_wasm_vd_{tag}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    let mut js = String::from(
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const env = { fmod: (a, b) => a % b, fmodf: (a, b) => Math.fround(Math.fround(a) % Math.fround(b)) };\n\
         const inst = new WebAssembly.Instance(m, { env });\n\
         const names = JSON.parse(fs.readFileSync(process.argv[3]));\n\
         const inputs = JSON.parse(fs.readFileSync(process.argv[4])).map(([a,b]) => [BigInt(a), BigInt(b)]);\n\
         const out = {};\n\
         for (const n of names) {\n\
           out[n] = inputs.map(([a,b]) => { try { return inst.exports[n](a, b).toString(); } catch (e) { return null; } });\n\
         }\n\
         process.stdout.write(JSON.stringify(out));\n",
    );
    js.push('\n');
    std::fs::write(dir.join("run.js"), js).unwrap();
    std::fs::write(
        dir.join("names.json"),
        serde_json::to_string(names).unwrap(),
    )
    .unwrap();
    let pairs: Vec<[String; 2]> = inputs
        .iter()
        .map(|(a, b)| [a.to_string(), b.to_string()])
        .collect();
    std::fs::write(
        dir.join("inputs.json"),
        serde_json::to_string(&pairs).unwrap(),
    )
    .unwrap();
    let run = Command::new(node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .arg(dir.join("names.json"))
        .arg(dir.join("inputs.json"))
        .output()
        .expect("run node");
    assert!(
        run.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let got: serde_json::Value = serde_json::from_slice(&run.stdout).expect("node JSON");
    let mut checks = 0usize;
    let mut failures = Vec::new();
    for (name, col) in expected {
        let wasm_col = got[name].as_array().expect("column");
        for (i, want) in col.iter().enumerate() {
            let Some(want) = want else {
                continue; // the reference execution refused this input
            };
            checks += 1;
            let wasm_v = wasm_col[i].as_str().map(|s| s.parse::<i64>().unwrap());
            match wasm_v {
                Some(v) if agree(name, *want, v) => {}
                other => failures.push(format!(
                    "{name}({}, {}): interpreter {want}, wasm {other:?}",
                    inputs[i].0, inputs[i].1
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "[{tag}] {} of {checks} checks diverged:\n{}",
        failures.len(),
        failures
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(checks > 10_000, "[{tag}] too few checks ran: {checks}");
    checks
}

/// The wasm linker for the object-lane test: `$WASM_LD`, else
/// `wasm-ld` on PATH.
fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD") {
        return Some(PathBuf::from(p));
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

/// The same module through the RELOCATABLE OBJECT lane: `compile_object`,
/// linked by `wasm-ld`, must compute exactly what the interpreter computes.
/// This is what checks the relocations — every call, stack-pointer access,
/// pooled constant and data address in the object is rewritten by the linker,
/// and one wrong relocation diverges here.
#[test]
fn linked_relocatable_object_agrees_with_the_interpreter() {
    let (module, names) = build_module();
    let object = wasm::compile_object_with_license(&c_spelling(&module), &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_object: {e}"));
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&object)
        .unwrap_or_else(|e| panic!("the object does not validate: {e}"));
    let verdict = trust_cg_verify::wasm_cfg_proofs::check_module_structure(&object);
    assert!(
        verdict.holds(),
        "CFG structural invariant on the object: {verdict}"
    );
    let (Some(node), Some(ld)) = (node(), wasm_ld()) else {
        eprintln!(
            "SKIP linked_relocatable_object_agrees_with_the_interpreter: needs node and wasm-ld \
             (set WASM_LD)"
        );
        return;
    };
    let dir = std::env::temp_dir().join(format!("tcg_wasm_obj_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("m.o"), &object).unwrap();
    let link = Command::new(&ld)
        .args(["--no-entry", "--export-dynamic", "--allow-undefined", "-o"])
        .arg(dir.join("m.wasm"))
        .arg(dir.join("m.o"))
        .output()
        .expect("run wasm-ld");
    assert!(
        link.status.success(),
        "wasm-ld refused the object: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    let linked = std::fs::read(dir.join("m.wasm")).unwrap();
    let _ = std::fs::remove_dir_all(&dir);

    let inputs = inputs();
    let expected: Vec<(String, Vec<Option<i64>>)> = names
        .iter()
        .map(|name| {
            let col = inputs
                .iter()
                .map(|&(a, b)| interpret(&module, name, a, b))
                .collect();
            (name.clone(), col)
        })
        .collect();
    let checks = run_and_compare(&node, &linked, &names, &inputs, &expected, "object");
    eprintln!(
        "wasm object-lane differential: {checks} checks over {} functions agree ({} object bytes)",
        names.len(),
        object.len()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
