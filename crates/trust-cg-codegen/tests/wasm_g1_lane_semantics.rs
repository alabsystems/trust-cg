// trust-cg-codegen/tests/wasm_g1_lane_semantics.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Wasm-lane value semantics pinned against the trust-ir REFERENCE
//! INTERPRETER: every function below is interpreted and compiled (closed
//! module, and relocatable object linked by `wasm-ld`), and the two must agree
//! on every input the interpreter defines.
//!
//! Each function is the trust-ir shape that exposed a lane defect:
//!
//! * a signed `icmp` on `bool` (a 1-bit integer: `true` reads signed as `-1`);
//! * float to 8/16-bit integer casts, raw and saturating (clamped to the OP's
//!   range, then the destination's carrier);
//! * conversions between `f32`/`f64` and 128-bit integers in both directions
//!   (round-to-nearest-even once; saturation by the op's signedness);
//! * a multi-value return containing a memory-carried value (`(i128, bool)`,
//!   `(struct, i32)`), and a single memory-carried result beside zero-sized
//!   ones (`((), S)`, `(S, ())`, `((), i128)`), direct and indirect;
//! * the discriminant of a zero-sized untagged enum;
//! * 128-bit dynamic element and GEP indices, and bulk-memory byte counts
//!   explicitly narrowed from a 128-bit intermediate to the required `usize`
//!   (the index is the VALUE, never the operand's memory address);
//! * undeclared tuples and structs laid out by the interpreter's C rule
//!   wherever they occur (alloca, GEP pointee, enum payload, array of arrays,
//!   module globals);
//! * a niche enum whose discriminants exceed `i64::MAX`;
//! * typed-reference and pointer `symaddr` constants in function bodies.
//!
//! The pointer-typed `symaddr` constant has no interpreter semantics (its
//! constant evaluation covers typed references only), so those functions are
//! checked against exact expected values instead. Invalid IR the lane must
//! refuse by name (a bool-lane reinterpretation, a float cast to `bool`, an
//! array too large for wasm32, a closed module naming an undefined symbol) is
//! pinned at the end.
//!
//! Node executes the wasm; its absence is a loud SKIP, never a silent pass.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::wasm;
use trust_ir::{
    InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty, parser,
};

/// Rename `%name` values and `bbname` blocks to the text format's numeric
/// spellings, per function, in order of first appearance.
fn number_names(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.starts_with("fn ") || line.starts_with("rustcc fn ") {
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

/// The module header: types, globals, signatures, and the helper functions
/// (`func.0` .. `func.5`, in this order) the functions under test call.
const HEADER: &str = r#"; TrustIr text format v1
module "wasm_g1_lane_semantics"
target "wasm32-unknown-unknown" 4 little

type ty.0 = i32
type ty.1 = (u8, u32)
type ty.2 = [ty.1 x 2]
type ty.3 = u8

struct @P { : i64 @0, : i64 @8 } size=16 align=8 id=0
struct @W { : i32 @0 } size=4 align=4 id=1
struct @Q { : i32, : i64 } id=2

enum @One repr(u32) { A = 7 } layout(untagged size=0 align=1 offsets=[[]]) id=0
enum @OneI8 repr(i8) { A = -5 } layout(untagged size=0 align=1 offsets=[[]]) id=1
enum @E repr(u8) { A((u8, u32)) = 0, B = 1 } id=2
enum @Big repr(u64) { None = 18446744073709551615, Some(u32) = 7 } layout(niche untagged=1 variants=0..=0 start=0 lane=u32@0 size=4 align=4 offsets=[[], [0]]) id=3

global @tab [ty.0 x 4] = array[ 11, 22, 33, 44 ]
global mut @tup (u8, i32) = { 7, 1000 }

functy.0 = (i64, i64) -> (i64)
functy.1 = (i64, i64) -> ((), struct.0)
functy.2 = (i64, i64) -> (struct.0, ())
functy.3 = (i64) -> ((), i128)
functy.4 = (i128, i128) -> (i128, bool)
functy.5 = (i64, i64) -> (struct.1, i32)
functy.6 = (i64) -> (i64)

rustcc fn @mk(functy.1) {
bbentry(%a: i64, %b: i64):
    %u = const () phantomdata
    %p = make_aggregate struct.0 (%a, %b)
    ret %u, %p
}

rustcc fn @mk2(functy.2) {
bbentry(%a: i64, %b: i64):
    %u = const () phantomdata
    %p = make_aggregate struct.0 (%b, %a)
    ret %p, %u
}

rustcc fn @wide(functy.3) {
bbentry(%a: i64):
    %u = const () phantomdata
    %w = sext i64 %a to i128
    ret %u, %w
}

rustcc fn @ovf(functy.4) {
bbentry(%x: i128, %y: i128):
    %s, %o = add.overflow i128 %x, %y
    ret %s, %o
}

rustcc fn @ws(functy.5) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %w = make_aggregate struct.1 (%x)
    %y = trunc i64 %b to i32
    ret %w, %y
}

fn @dbl(functy.6) {
bbentry(%a: i64):
    %r = add i64 %a, %a
    ret %r
}

"#;

/// Hand-written functions (each `(i64, i64) -> i64`) compared with the
/// interpreter.
const FUNCTIONS: &str = r#"
fn @use_mk(functy.0) {
bbentry(%a: i64, %b: i64):
    %u, %p = call @func.0(%a, %b)
    %x = extractfield i64 %p, 0
    %y = extractfield i64 %p, 1
    %c3 = const i64 3
    %y3 = mul i64 %y, %c3
    %r = add i64 %x, %y3
    ret %r
}

fn @use_mk_ind(functy.0) {
bbentry(%a: i64, %b: i64):
    %fp = const functy.1 fndef<func.0>
    %u, %p = call_indirect %fp(functy.1)(%a, %b) cc=rustcc
    %x = extractfield i64 %p, 0
    %y = extractfield i64 %p, 1
    %c3 = const i64 3
    %y3 = mul i64 %y, %c3
    %r = add i64 %x, %y3
    ret %r
}

fn @use_mk2(functy.0) {
bbentry(%a: i64, %b: i64):
    %p, %u = call @func.1(%a, %b)
    %x = extractfield i64 %p, 0
    %y = extractfield i64 %p, 1
    %c3 = const i64 3
    %y3 = mul i64 %y, %c3
    %r = add i64 %x, %y3
    ret %r
}

fn @use_wide(functy.0) {
bbentry(%a: i64, %b: i64):
    %u, %w = call @func.2(%a)
    %c64 = const i128 64
    %h = ashr i128 %w, %c64
    %hi = trunc i128 %h to i64
    %lo = trunc i128 %w to i64
    %c5 = const i64 5
    %h5 = mul i64 %hi, %c5
    %r = xor i64 %lo, %h5
    ret %r
}

fn @use_wide_ind(functy.0) {
bbentry(%a: i64, %b: i64):
    %fp = const functy.3 fndef<func.2>
    %u, %w = call_indirect %fp(functy.3)(%a) cc=rustcc
    %c64 = const i128 64
    %h = ashr i128 %w, %c64
    %hi = trunc i128 %h to i64
    %lo = trunc i128 %w to i64
    %c5 = const i64 5
    %h5 = mul i64 %hi, %c5
    %r = xor i64 %lo, %h5
    ret %r
}

fn @use_ovf(functy.0) {
bbentry(%a: i64, %b: i64):
    %lo = zext i64 %a to i128
    %hw = zext i64 %b to i128
    %c64 = const i128 64
    %hi = shl i128 %hw, %c64
    %x = or i128 %hi, %lo
    %y = shl i128 %lo, %c64
    %s, %o = call @func.3(%x, %y)
    %sh = lshr i128 %s, %c64
    %shi = trunc i128 %sh to i64
    %slo = trunc i128 %s to i64
    %f = zext bool %o to i64
    %c7 = const i64 7
    %h7 = mul i64 %shi, %c7
    %m = xor i64 %slo, %h7
    %c40 = const i64 40
    %fs = shl i64 %f, %c40
    %r = xor i64 %m, %fs
    ret %r
}

fn @use_ovf_ind(functy.0) {
bbentry(%a: i64, %b: i64):
    %lo = zext i64 %a to i128
    %hw = zext i64 %b to i128
    %c64 = const i128 64
    %hi = shl i128 %hw, %c64
    %x = or i128 %hi, %lo
    %fp = const functy.4 fndef<func.3>
    %s, %o = call_indirect %fp(functy.4)(%x, %x) cc=rustcc
    %sh = lshr i128 %s, %c64
    %shi = trunc i128 %sh to i64
    %slo = trunc i128 %s to i64
    %f = zext bool %o to i64
    %c7 = const i64 7
    %h7 = mul i64 %shi, %c7
    %m = xor i64 %slo, %h7
    %c40 = const i64 40
    %fs = shl i64 %f, %c40
    %r = xor i64 %m, %fs
    ret %r
}

fn @use_ws(functy.0) {
bbentry(%a: i64, %b: i64):
    %w, %y = call @func.4(%a, %b)
    %x = extractfield i32 %w, 0
    %s = sub i32 %x, %y
    %r = sext i32 %s to i64
    ret %r
}

fn @zst_tag_make(functy.0) {
bbentry(%a: i64, %b: i64):
    %e = make_aggregate enum.0 variant 0 ()
    %t = extractfield u32 %e, 0
    %w = zext u32 %t to i64
    %r = add i64 %w, %a
    ret %r
}

fn @zst_tag_const(functy.0) {
bbentry(%a: i64, %b: i64):
    %e = const enum.0 { 7 }
    %t = extractfield u32 %e, 0
    %w = zext u32 %t to i64
    %r = add i64 %w, %b
    ret %r
}

fn @zst_tag_i8(functy.0) {
bbentry(%a: i64, %b: i64):
    %e = make_aggregate enum.1 variant 0 ()
    %t = extractfield i8 %e, 0
    %w = sext i8 %t to i64
    %r = add i64 %w, %a
    ret %r
}

fn @xelem_u128(functy.0) {
bbentry(%a: i64, %b: i64):
    %arr = const [ty.0 x 8] array[ 3, 1, 4, 1, 5, 9, 2, 6 ]
    %c7 = const i64 7
    %m = and i64 %a, %c7
    %i = zext i64 %m to u128
    %e = extractelement i32 %arr, %i
    %r = sext i32 %e to i64
    ret %r
}

fn @xelem_i128(functy.0) {
bbentry(%a: i64, %b: i64):
    %arr = const [ty.0 x 8] array[ 3, 1, 4, 1, 5, 9, 2, 6 ]
    %c7 = const i64 7
    %m = and i64 %a, %c7
    %i = zext i64 %m to i128
    %e = extractelement i32 %arr, %i
    %r = sext i32 %e to i64
    ret %r
}

fn @ielem_u128(functy.0) {
bbentry(%a: i64, %b: i64):
    %arr = const [ty.0 x 8] array[ 3, 1, 4, 1, 5, 9, 2, 6 ]
    %c7 = const i64 7
    %m = and i64 %a, %c7
    %i = zext i64 %m to u128
    %v = trunc i64 %b to i32
    %arr2 = insertelement [ty.0 x 8] %arr, %i, %v
    %c0 = const usize 0
    %e0 = extractelement i32 %arr2, %c0
    %c3 = const usize 3
    %e3 = extractelement i32 %arr2, %c3
    %c7u = const usize 7
    %e7 = extractelement i32 %arr2, %c7u
    %s = add i32 %e0, %e3
    %t = add i32 %s, %e7
    %r = sext i32 %t to i64
    ret %r
}

fn @splat_i32(functy.0) {
bbentry(%a: i64, %b: i64):
    %v = trunc i64 %a to i32
    %arr = array_splat [ty.0 x 7] %v
    %c3 = const i64 3
    %m = and i64 %b, %c3
    %i = zext i64 %m to u128
    %e = extractelement i32 %arr, %i
    %c6 = const usize 6
    %e6 = extractelement i32 %arr, %c6
    %s = add i32 %e, %e6
    %r = sext i32 %s to i64
    ret %r
}

fn @splat_tuple(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to u8
    %y = trunc i64 %b to u32
    %t = make_aggregate (u8, u32) (%x, %y)
    %arr = array_splat [ty.1 x 5] %t
    %slot = alloca [ty.1 x 5]
    store [ty.1 x 5] %arr, ptr %slot
    %c32 = const usize 32
    %q = gep u8, ptr %slot, %c32
    %lw = load u8, ptr %q
    %c36 = const usize 36
    %q4 = gep u8, ptr %slot, %c36
    %ly = load u32, ptr %q4
    %c2 = const usize 2
    %e = extractelement (u8, u32) %arr, %c2
    %ey = extractfield u32 %e, 1
    %s = add u32 %ly, %ey
    %sw = zext u32 %s to i64
    %lx = zext u8 %lw to i64
    %c32b = const i64 32
    %xs = shl i64 %lx, %c32b
    %r = or i64 %sw, %xs
    ret %r
}

fn @splat_nested(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to u8
    %y = trunc i64 %b to u32
    %t = make_aggregate (u8, u32) (%x, %y)
    %row = array_splat [ty.1 x 2] %t
    %m = array_splat [ty.2 x 3] %row
    %i2 = const usize 2
    %r2 = extractelement [ty.1 x 2] %m, %i2
    %i1 = const usize 1
    %e = extractelement (u8, u32) %r2, %i1
    %ex = extractfield u8 %e, 0
    %ey = extractfield u32 %e, 1
    %xw = zext u8 %ex to i64
    %yw = zext u32 %ey to i64
    %c40 = const i64 40
    %xs = shl i64 %xw, %c40
    %r = xor i64 %yw, %xs
    ret %r
}

fn @gep_u128(functy.0) {
bbentry(%a: i64, %b: i64):
    %buf = alloca [ty.0 x 4]
    %c0 = const usize 0
    %p0 = gep i32, ptr %buf, %c0
    %k0 = const i32 10
    store i32 %k0, ptr %p0
    %c1 = const usize 1
    %p1 = gep i32, ptr %buf, %c1
    %k1 = const i32 20
    store i32 %k1, ptr %p1
    %one = const i64 1
    %m = and i64 %a, %one
    %i = zext i64 %m to u128
    %pi = gep i32, ptr %buf, %i
    %v = load i32, ptr %pi
    %r = sext i32 %v to i64
    ret %r
}

fn @gep_u64(functy.0) {
bbentry(%a: i64, %b: i64):
    %buf = alloca [ty.0 x 4]
    %c0 = const usize 0
    %p0 = gep i32, ptr %buf, %c0
    %k0 = const i32 10
    store i32 %k0, ptr %p0
    %c1 = const usize 1
    %p1 = gep i32, ptr %buf, %c1
    %k1 = const i32 20
    store i32 %k1, ptr %p1
    %one = const i64 1
    %m = and i64 %a, %one
    %i = bitcast i64 %m to u64
    %pi = gep i32, ptr %buf, %i
    %v = load i32, ptr %pi
    %r = sext i32 %v to i64
    ret %r
}

fn @memset_u128(functy.0) {
bbentry(%a: i64, %b: i64):
    %buf = alloca [ty.3 x 16]
    %z = const u8 0
    %c16 = const usize 16
    memset ptr %buf, %z, %c16
    %c7 = const i64 7
    %m = and i64 %a, %c7
    %wide = zext i64 %m to u128
    %n = trunc u128 %wide to usize
    %k = const u8 171
    memset ptr %buf, %k, %n
    %c0 = const usize 0
    %p = gep u64, ptr %buf, %c0
    %v = load u64, ptr %p
    %r = bitcast u64 %v to i64
    ret %r
}

fn @memcopy_u128(functy.0) {
bbentry(%a: i64, %b: i64):
    %src = alloca [ty.3 x 16]
    %dst = alloca [ty.3 x 16]
    %z = const u8 0
    %c16 = const usize 16
    memset ptr %dst, %z, %c16
    %k = const u8 90
    memset ptr %src, %k, %c16
    %c7 = const i64 7
    %m = and i64 %a, %c7
    %wide = zext i64 %m to u128
    %n = trunc u128 %wide to usize
    memcopy overlap ptr %dst, ptr %src, %n
    %c0 = const usize 0
    %p = gep u64, ptr %dst, %c0
    %v = load u64, ptr %p
    %r = bitcast u64 %v to i64
    ret %r
}

fn @tuple_alloca(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to u8
    %y = bitcast i64 %b to u64
    %t = make_aggregate (u8, u64) (%x, %y)
    %slot = alloca (u8, u64)
    store (u8, u64) %t, ptr %slot
    %c8 = const usize 8
    %q = gep u8, ptr %slot, %c8
    %e = load u64, ptr %q
    %l = load (u8, u64), ptr %slot
    %f = extractfield u8 %l, 0
    %fw = zext u8 %f to u64
    %s = add u64 %e, %fw
    %r = bitcast u64 %s to i64
    ret %r
}

fn @tuple_gep(functy.0) {
bbentry(%a: i64, %b: i64):
    %buf = alloca [ty.3 x 64]
    %x = trunc i64 %a to u8
    %y = bitcast i64 %b to u64
    %t = make_aggregate (u8, u64) (%x, %y)
    %c1 = const usize 1
    %p1 = gep (u8, u64), ptr %buf, %c1
    store (u8, u64) %t, ptr %p1
    %c24 = const usize 24
    %q = gep u8, ptr %buf, %c24
    %e = load u64, ptr %q
    %r = bitcast u64 %e to i64
    ret %r
}

fn @tuple_in_enum(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to u8
    %y = trunc i64 %b to u32
    %t = make_aggregate (u8, u32) (%x, %y)
    %e = make_aggregate enum.2 variant 0 (%t)
    %slot = alloca enum.2
    store enum.2 %e, ptr %slot
    %l = load enum.2, ptr %slot
    %g = extractfield (u8, u32) %l, 1
    %gb = extractfield u32 %g, 1
    %ga = extractfield u8 %g, 0
    %d = extractfield u8 %l, 0
    %bw = zext u32 %gb to i64
    %aw = zext u8 %ga to i64
    %dw = zext u8 %d to i64
    %c32 = const i64 32
    %as = shl i64 %aw, %c32
    %c48 = const i64 48
    %ds = shl i64 %dw, %c48
    %s = or i64 %bw, %as
    %r = or i64 %s, %ds
    ret %r
}

fn @tuple_arr2(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to u8
    %y = trunc i64 %b to u32
    %t = make_aggregate (u8, u32) (%x, %y)
    %c1 = const u32 1
    %y1 = add u32 %y, %c1
    %t1 = make_aggregate (u8, u32) (%x, %y1)
    %row = make_aggregate [ty.1 x 2] (%t, %t1)
    %m = array_splat [ty.2 x 2] %row
    %i1 = const usize 1
    %r1 = extractelement [ty.1 x 2] %m, %i1
    %e = extractelement (u8, u32) %r1, %i1
    %eb = extractfield u32 %e, 1
    %slot = alloca [ty.2 x 2]
    store [ty.2 x 2] %m, ptr %slot
    %c28 = const usize 28
    %q = gep u8, ptr %slot, %c28
    %v = load u32, ptr %q
    %ew = zext u32 %eb to i64
    %vw = zext u32 %v to i64
    %c32 = const i64 32
    %vs = shl i64 %vw, %c32
    %r = or i64 %ew, %vs
    ret %r
}

fn @undeclared_struct(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %a to i32
    %q = make_aggregate struct.2 (%x, %b)
    %slot = alloca struct.2
    store struct.2 %q, ptr %slot
    %c8 = const usize 8
    %p = gep u8, ptr %slot, %c8
    %v = load i64, ptr %p
    %l = load struct.2, ptr %slot
    %f = extractfield i32 %l, 0
    %fw = sext i32 %f to i64
    %r = add i64 %v, %fw
    ret %r
}

fn @niche_big_disc(functy.0) {
bbentry(%a: i64, %b: i64):
    %x = trunc i64 %b to u32
    %one = const u32 1
    %nz = or u32 %x, %one
    %c1 = const i64 1
    %bit = and i64 %a, %c1
    %isz = icmp eq i64 %bit, %c1
    condbr %isz, bbnone, bbsome
bbnone:
    %n = make_aggregate enum.3 variant 0 ()
    br bbj(%n)
bbsome:
    %s = make_aggregate enum.3 variant 1 (%nz)
    br bbj(%s)
bbj(%e: enum.3):
    %t = extractfield u64 %e, 0
    %r = bitcast u64 %t to i64
    ret %r
}

fn @tuple_global(functy.0) {
bbentry(%a: i64, %b: i64):
    %g = global_addr @global.1
    %l = load (u8, i32), ptr %g
    %f = extractfield u8 %l, 0
    %s = extractfield i32 %l, 1
    %fw = zext u8 %f to i64
    %sw = sext i32 %s to i64
    %t = add i64 %fw, %sw
    %r = add i64 %t, %a
    ret %r
}

fn @symaddr_ref(functy.0) {
bbentry(%a: i64, %b: i64):
    %base = const &[ty.0 x 4] symaddr<tab>
    %c2 = const usize 2
    %p = gep i32, ptr %base, %c2
    %v = load i32, ptr %p
    %w = sext i32 %v to i64
    %r = add i64 %w, %b
    ret %r
}
"#;

/// Functions checked against exact values (no interpreter semantics: the
/// interpreter evaluates only typed-reference `symaddr` constants).
const EXACT_FUNCTIONS: &str = r#"
fn @symaddr_ptr(functy.0) {
bbentry(%a: i64, %b: i64):
    %p = const ptr symaddr<tab>
    %c3 = const i64 3
    %m = and i64 %a, %c3
    %i = trunc i64 %m to usize
    %q = gep i32, ptr %p, %i
    %v = load i32, ptr %q
    %r = sext i32 %v to i64
    ret %r
}

fn @symaddr_ptr_addend(functy.0) {
bbentry(%a: i64, %b: i64):
    %p = const ptr symaddr<tab + 12>
    %v = load i32, ptr %p
    %r = sext i32 %v to i64
    ret %r
}

fn @symaddr_fn(functy.0) {
bbentry(%a: i64, %b: i64):
    %fp = const ptr symaddr<dbl>
    %r = call_indirect %fp(functy.6)(%a)
    ret %r
}
"#;

/// The exact value of each [`EXACT_FUNCTIONS`] function.
fn exact(name: &str, a: i64, _b: i64) -> i64 {
    const TAB: [i64; 4] = [11, 22, 33, 44];
    match name {
        "symaddr_ptr" => TAB[(a & 3) as usize],
        "symaddr_ptr_addend" => 44,
        "symaddr_fn" => a.wrapping_add(a),
        other => panic!("no exact value for {other}"),
    }
}

/// Generated functions: `(name, body)`.
fn generated_functions() -> Vec<(String, String)> {
    let mut out = Vec::new();
    // `bool` to an ordered predicate is a 1-bit integer: `true` reads SIGNED
    // as `-1`, so every signed order is the reversed unsigned one.
    for cmp in [
        "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
    ] {
        out.push((
            format!("icmp_{cmp}_bool"),
            format!(
                "    %c0 = const i64 0\n    %x = icmp ne i64 %a, %c0\n    \
                 %y = icmp ne i64 %b, %c0\n    %v = icmp {cmp} bool %x, %y\n    \
                 %r = zext bool %v to i64\n    ret %r\n"
            ),
        ));
    }
    // `a` is an f64 bit pattern; an f32 source is its rounding.
    let float_src = |src: &str| {
        let mut s = String::from("    %f = bitcast i64 %a to f64\n");
        if src == "f32" {
            s.push_str("    %g = fptrunc f64 %f to f32\n");
        }
        s
    };
    let src_val = |src: &str| if src == "f32" { "%g" } else { "%f" };
    // Float to 8/16-bit integers, raw and saturating.
    for op in ["fptosi", "fptoui", "fptosi.sat", "fptoui.sat"] {
        for src in ["f64", "f32"] {
            for (dst, ext) in [
                ("i8", "sext"),
                ("u8", "zext"),
                ("i16", "sext"),
                ("u16", "zext"),
            ] {
                let mut body = float_src(src);
                let _ = write!(
                    body,
                    "    %n = {op} {src} {} to {dst}\n    %r = {ext} {dst} %n to i64\n    ret %r\n",
                    src_val(src)
                );
                out.push((format!("{}_{src}_{dst}", op.replace('.', "_")), body));
            }
        }
    }
    // Float to 128-bit integers: each half of the result.
    for op in ["fptosi", "fptoui", "fptosi.sat", "fptoui.sat"] {
        for src in ["f64", "f32"] {
            for it in ["i128", "u128"] {
                for half in ["lo", "hi"] {
                    let mut body = float_src(src);
                    let _ = writeln!(body, "    %x = {op} {src} {} to {it}", src_val(src));
                    if half == "lo" {
                        body.push_str(&format!("    %r = trunc {it} %x to i64\n"));
                    } else {
                        body.push_str(&format!(
                            "    %c64 = const {it} 64\n    %s = lshr {it} %x, %c64\n    \
                             %r = trunc {it} %s to i64\n"
                        ));
                    }
                    body.push_str("    ret %r\n");
                    out.push((format!("{}_{src}_{it}_{half}", op.replace('.', "_")), body));
                }
            }
        }
    }
    // 128-bit integers (`b` the high half, `a` the low) to floats, by the
    // op's signedness whatever the integer type's.
    for op in ["sitofp", "uitofp"] {
        for it in ["i128", "u128"] {
            for dst in ["f64", "f32"] {
                let mut body = String::from(
                    "    %lo = zext i64 %a to u128\n    %hw = zext i64 %b to u128\n    \
                     %c64 = const u128 64\n    %hi = shl u128 %hw, %c64\n    \
                     %u = or u128 %hi, %lo\n",
                );
                let x = if it == "i128" {
                    body.push_str("    %x = bitcast u128 %u to i128\n");
                    "%x"
                } else {
                    "%u"
                };
                let _ = writeln!(body, "    %v = {op} {it} {x} to {dst}");
                if dst == "f64" {
                    body.push_str("    %r = bitcast f64 %v to i64\n");
                } else {
                    body.push_str("    %w = bitcast f32 %v to u32\n    %r = zext u32 %w to i64\n");
                }
                body.push_str("    ret %r\n");
                out.push((format!("{op}_{it}_{dst}_bits"), body));
            }
        }
    }
    out
}

fn fn_names(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|l| l.strip_prefix("fn @"))
        .map(|rest| rest.split('(').next().unwrap().to_string())
        .collect()
}

/// The test module, the names compared with the interpreter, and the names
/// compared with [`exact`].
fn build_module() -> (Module, Vec<String>, Vec<String>) {
    let mut text = String::from(HEADER);
    text.push_str(FUNCTIONS);
    text.push_str(EXACT_FUNCTIONS);
    let mut names = fn_names(FUNCTIONS);
    for (name, body) in generated_functions() {
        let _ = write!(
            text,
            "\nfn @{name}(functy.0) {{\nbbentry(%a: i64, %b: i64):\n{body}}}\n"
        );
        names.push(name);
    }
    let module = parser::parse_module(&number_names(&text))
        .unwrap_or_else(|e| panic!("parse the test module: {e}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "the positive fixture must validate: {errors:?}"
    );
    (module, names, fn_names(EXACT_FUNCTIONS))
}

/// Inputs: f64 bit patterns at every conversion boundary crossed with
/// 128-bit high halves at rounding boundaries, then an LCG.
fn inputs() -> Vec<(i64, i64)> {
    let p = |e: i32| 2f64.powi(e);
    let mut floats = vec![
        0.0,
        -0.0,
        0.5,
        -0.5,
        0.99,
        -0.99,
        1.0,
        -1.0,
        1.5,
        -1.5,
        7.0,
        100.25,
        -100.75,
        127.0,
        127.5,
        128.0,
        -128.0,
        -128.5,
        -129.0,
        200.0,
        -200.0,
        255.0,
        255.9,
        256.0,
        300.0,
        -300.0,
        32767.0,
        32767.5,
        32768.0,
        -32768.0,
        -32768.9,
        -32769.0,
        65535.0,
        65535.5,
        65536.0,
        -65536.0,
        1e9,
        -1e9,
        p(31),
        p(32),
        p(53) + 2.0,
        p(63),
        -p(63),
        p(64),
        -p(64),
        p(64) * 1.5,
        p(100) + p(60),
        -p(100),
        p(126) * 1.75,
        p(127),
        -p(127),
        p(127) * (1.0 - p(-53)),
        -p(127) * (1.0 - p(-53)),
        p(128),
        p(128) * (1.0 - p(-53)),
        -p(128),
        f64::from(f32::MAX),
        1e300,
        -1e300,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        -f64::NAN,
        f64::from_bits(1),
    ];
    let mut s: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = || {
        s = s
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        s
    };
    for _ in 0..48 {
        let r = next();
        let e = (r % 135) as i32 - 4;
        let m = 1.0 + ((r >> 12) as f64) / p(52);
        let v = m * p(e);
        floats.push(if r & 1 == 0 { v } else { -v });
    }
    let highs: [i64; 9] = [0, 1, -1, 7, i64::MIN, 12345, 1 << 11, i64::MAX, -2];
    let mut out = Vec::new();
    for f in &floats {
        for &h in &highs {
            out.push((f.to_bits() as i64, h));
        }
    }
    // (low, high) at f64 / f32 rounding boundaries of a 128-bit value:
    // `2^64 + 2^11` and `2^64 + 2^40` are exact ties for f64 / f32.
    let lows: [i64; 11] = [
        0,
        1,
        1 << 11,
        (1 << 11) + 1,
        3 << 11,
        1 << 40,
        (1 << 40) + 1,
        3 << 40,
        i64::MIN,
        -1,
        i64::MAX,
    ];
    let wide_highs: [i64; 11] = [
        0,
        1,
        2,
        -1,
        -2,
        i64::MIN,
        i64::MAX,
        1 << 52,
        (1 << 53) - 1,
        1 << 40,
        (1 << 24) - 1,
    ];
    for &l in &lows {
        for &h in &wide_highs {
            out.push((l, h));
        }
    }
    for _ in 0..400 {
        let a = next() as i64;
        let b = next() as i64;
        out.push((a, b >> (next() % 64)));
    }
    out
}

fn node() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("node"))
        .find(|p| p.is_file())
}

/// The wasm linker for the object lane: `$WASM_LD`, else `wasm-ld` on PATH.
fn wasm_ld() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("WASM_LD") {
        return Some(PathBuf::from(p));
    }
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|d| d.join("wasm-ld"))
        .find(|p| p.is_file())
}

fn i64_value(v: i64) -> InterpretValue {
    InterpretValue::int(Ty::I64, i128::from(v)).expect("i64 value")
}

/// The interpreter's answer, or `None` when it refuses the input (undefined
/// behaviour, e.g. a raw `fptosi` of an out-of-range value).
fn interpret(module: &Module, name: &str, a: i64, b: i64) -> Option<i64> {
    let f = module.function_by_name(name).expect("function");
    let interp = Interpreter::with_module(module).with_options(InterpretOptions {
        fuel: 1_000_000,
        max_call_depth: 16,
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

/// Every function's column of wasm results under node (`None`: a trap).
fn run_node(
    node: &std::path::Path,
    bytes: &[u8],
    names: &[String],
    inputs: &[(i64, i64)],
    tag: &str,
) -> HashMap<String, Vec<Option<i64>>> {
    let dir = std::env::temp_dir().join(format!("tcg_wasm_g1_{tag}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("m.wasm"), bytes).unwrap();
    std::fs::write(
        dir.join("run.js"),
        "const fs = require('fs');\n\
         const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
         const inst = new WebAssembly.Instance(m, {});\n\
         const names = JSON.parse(fs.readFileSync(process.argv[3]));\n\
         const inputs = JSON.parse(fs.readFileSync(process.argv[4])).map(([a,b]) => [BigInt(a), BigInt(b)]);\n\
         const out = {};\n\
         for (const n of names) {\n\
           out[n] = inputs.map(([a,b]) => { try { return inst.exports[n](a, b).toString(); } catch (e) { return null; } });\n\
         }\n\
         process.stdout.write(JSON.stringify(out));\n",
    )
    .unwrap();
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
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "node failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let got: serde_json::Value = serde_json::from_slice(&run.stdout).expect("node JSON");
    names
        .iter()
        .map(|n| {
            let col = got[n]
                .as_array()
                .expect("column")
                .iter()
                .map(|v| v.as_str().map(|s| s.parse::<i64>().unwrap()))
                .collect();
            (n.clone(), col)
        })
        .collect()
}

/// Compare the compiled module (closed or linked) against the interpreter and
/// the exact values.
fn check_against_reference(bytes: &[u8], tag: &str) {
    let (module, names, exact_names) = build_module();
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(bytes)
        .unwrap_or_else(|e| panic!("[{tag}] the module does not validate: {e}"));
    let Some(node) = node() else {
        eprintln!("SKIP [{tag}] wasm_g1_lane_semantics: node not on PATH");
        return;
    };
    let inputs = inputs();
    let mut all = names.clone();
    all.extend(exact_names.iter().cloned());
    let got = run_node(&node, bytes, &all, &inputs, tag);
    let mut failures = Vec::new();
    let mut unexercised = Vec::new();
    let mut checks = 0usize;
    for name in &names {
        let mut ran = 0usize;
        for (i, &(a, b)) in inputs.iter().enumerate() {
            let Some(want) = interpret(&module, name, a, b) else {
                continue;
            };
            ran += 1;
            checks += 1;
            if got[name][i] != Some(want) {
                failures.push(format!(
                    "{name}({a}, {b}): interpreter {want}, wasm {:?}",
                    got[name][i]
                ));
            }
        }
        // A function the reference refuses on (nearly) every input pins
        // nothing.
        if ran < 8 {
            unexercised.push(format!("{name}: {ran} inputs ran"));
        }
    }
    for name in &exact_names {
        for (i, &(a, b)) in inputs.iter().enumerate() {
            checks += 1;
            let want = exact(name, a, b);
            if got[name][i] != Some(want) {
                failures.push(format!(
                    "{name}({a}, {b}): expected {want}, wasm {:?}",
                    got[name][i]
                ));
            }
        }
    }
    assert!(
        unexercised.is_empty(),
        "[{tag}] the interpreter refused these functions:\n{}",
        unexercised.join("\n")
    );
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
    eprintln!(
        "[{tag}] wasm g1 lane semantics: {checks} checks over {} functions agree",
        all.len()
    );
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
fn closed_module_agrees_with_the_interpreter() {
    let (module, _, _) = build_module();
    let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile: {e}"));
    let verdict = trust_cg_verify::wasm_cfg_proofs::check_module_structure(&bytes);
    assert!(verdict.holds(), "CFG structural invariant: {verdict}");
    check_against_reference(&bytes, "closed");
}

#[test]
fn linked_relocatable_object_agrees_with_the_interpreter() {
    let (module, _, _) = build_module();
    let object = wasm::compile_object_with_license(&c_spelling(&module), &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_object: {e}"));
    let Some(ld) = wasm_ld() else {
        eprintln!("SKIP linked_relocatable_object_agrees_with_the_interpreter: set WASM_LD");
        return;
    };
    let dir = std::env::temp_dir().join(format!("tcg_wasm_g1_obj_{}", std::process::id()));
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
    check_against_reference(&linked, "object");
}

/// A one-function module `(i64, i64) -> i64` with `body`.
fn one_function(prelude: &str, body: &str) -> Module {
    let text = format!(
        "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n{prelude}\
         functy.0 = (i64, i64) -> (i64)\n\nfn @f(functy.0) {{\nbbentry(%a: i64, %b: i64):\n{body}}}\n"
    );
    parser::parse_module(&number_names(&text)).unwrap_or_else(|e| panic!("parse: {e}"))
}

fn refusal(module: &Module) -> String {
    wasm::compile_module_with_license(module, &permit_unlicensed())
        .err()
        .unwrap_or_else(|| panic!("the lane compiled invalid IR"))
        .to_string()
}

/// An array of tuples too large for wasm32 is refused, not a panic.
#[test]
fn an_array_larger_than_wasm32_is_refused() {
    let m = one_function(
        "type ty.0 = (u8, u32)\n\n",
        "    %x = undef [ty.0 x 4611686018427387904]\n    ret %a\n",
    );
    let err = refusal(&m);
    assert!(err.contains("larger than the wasm32 space"), "{err}");
}

/// trust-ir never reinterprets a bool lane (the validator's
/// `CastLayoutUnsupported`; the interpreter has no bool `Bitcast` source), so
/// the i32 carriers must not make `bitcast bool -> u8` look like an identity.
#[test]
fn a_bool_lane_reinterpretation_is_refused_by_name() {
    for (pre, cast) in [
        (
            "    %c0 = const i64 0\n    %x = icmp ne i64 %a, %c0\n",
            "    %y = bitcast bool %x to u8\n    %r = zext u8 %y to i64\n",
        ),
        (
            "    %x = trunc i64 %a to u8\n",
            "    %y = bitcast u8 %x to bool\n    %r = zext bool %y to i64\n",
        ),
        (
            "    %c0 = const i64 0\n    %x = icmp ne i64 %a, %c0\n",
            "    %y = bitcast bool %x to ptr\n    %r = ptrtoint ptr %y to i64\n",
        ),
    ] {
        let m = one_function("", &format!("{pre}{cast}    ret %r\n"));
        let err = refusal(&m);
        assert!(
            err.contains("CastLayoutUnsupported")
                && err.contains("bitcast")
                && err.contains("bool"),
            "{cast}: {err}"
        );
    }
}

/// A float cast to `bool` has no integer shape in the interpreter
/// (`int_shape`), so it is refused rather than lowered on the i32 carrier.
#[test]
fn a_float_to_bool_cast_is_refused_by_name() {
    let m = one_function(
        "",
        "    %f = bitcast i64 %a to f64\n    %y = fptosi.sat f64 %f to bool\n    \
         %r = zext bool %y to i64\n    ret %r\n",
    );
    let err = refusal(&m);
    assert!(
        err.contains("CastIncompatible") && err.contains("fptosi.sat from f64 to bool"),
        "{err}"
    );
}

/// The old wide-count fixture was invalid under the module's pointer-sized
/// bulk-memory contract. Keep both rejected forms as controls, while the
/// positive fixture above still computes the count in a 128-bit value.
#[test]
fn bulk_memory_counts_require_the_target_usize_type() {
    for operation in [
        "memset ptr %buf, %byte, %n",
        "memcopy overlap ptr %buf, ptr %buf, %n",
    ] {
        let body = format!(
            "    %buf = alloca [ty.0 x 16]\n    %byte = const u8 0\n\
             %n = const u128 1\n    {operation}\n    ret %a\n"
        );
        let m = one_function("type ty.0 = u8\n\n", &body);
        let err = refusal(&m);
        assert!(
            err.contains("OperandTypeMismatch")
                && err.contains("bytes type mismatch: expected usize, got u128"),
            "{operation}: {err}"
        );
        let err = wasm::compile_object_with_license(&m, &permit_unlicensed())
            .expect_err("the object lane must preserve the same byte-count contract")
            .to_string();
        assert!(
            err.contains("OperandTypeMismatch")
                && err.contains("bytes type mismatch: expected usize, got u128"),
            "{operation}: {err}"
        );
    }
}

/// A typed reference denotes the whole global with its exact type. Taking an
/// interior element requires a GEP from that reference, as in the positive
/// fixture; neither an addend nor a different pointee type is admitted.
#[test]
fn typed_reference_constants_keep_the_global_type_and_zero_addend() {
    for (constant, reason) in [
        ("&i32 symaddr<tab + 8>", "addend 8 is not 0"),
        ("&i32 symaddr<tab>", "not the pointee type"),
    ] {
        let body = format!("    %p = const {constant}\n    ret %a\n");
        let m = one_function(
            "type ty.0 = i32\nglobal @tab [ty.0 x 4] = array[ 11, 22, 33, 44 ]\n\n",
            &body,
        );
        let err = refusal(&m);
        assert!(
            err.contains("PointerConstantRefused") && err.contains(reason),
            "{err}"
        );
        let err = wasm::compile_object_with_license(&m, &permit_unlicensed())
            .expect_err("the object lane must preserve the same reference contract")
            .to_string();
        assert!(
            err.contains("PointerConstantRefused") && err.contains(reason),
            "{err}"
        );
    }
}

/// A body `symaddr` naming a symbol the module does not define needs a
/// linker: the closed module refuses it by name, the object imports it.
#[test]
fn an_undefined_symaddr_is_refused_by_a_closed_module_and_imported_by_an_object() {
    let m = one_function(
        "",
        "    %p = const ptr symaddr<elsewhere + 4>\n    %v = load i64, ptr %p\n    ret %v\n",
    );
    let err = refusal(&m);
    assert!(err.contains("does not define"), "{err}");
    let object = wasm::compile_object_with_license(&m, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("compile_object: {e}"));
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&object)
        .unwrap_or_else(|e| panic!("the object does not validate: {e}"));
    assert!(
        object.windows(9).any(|w| w == b"elsewhere"),
        "the object names the undefined data symbol"
    );
}

/// A wasm function address is a `funcref` table index, not a byte address, so
/// `symaddr<function + k>` with `k != 0` names nothing. Both lanes refuse it
/// by name, in a function body and in a global's static data alike; the
/// object lane must not turn it into an undefined DATA import that merely
/// shares the function's name.
#[test]
fn a_function_symaddr_with_an_addend_is_refused_by_both_lanes() {
    let body = one_function(
        "",
        "    %p = const ptr symaddr<f + 4>\n    %v = load i64, ptr %p\n    ret %v\n",
    );
    let global = one_function("global @p ptr = symaddr<f + 4>\n\n", "    ret %a\n");
    for (what, m) in [("body", &body), ("global", &global)] {
        let closed = refusal(m);
        assert!(
            closed.contains("which a byte offset does not address"),
            "{what}: {closed}"
        );
        let object = wasm::compile_object_with_license(m, &permit_unlicensed())
            .err()
            .unwrap_or_else(|| panic!("{what}: the object lane accepted symaddr<f + 4>"))
            .to_string();
        assert!(
            object.contains("which a byte offset does not address"),
            "{what}: {object}"
        );
    }
    // Without an addend the same constant is the function's table index.
    let plain = one_function("global @p ptr = symaddr<f>\n\n", "    ret %a\n");
    wasm::compile_module_with_license(&plain, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("symaddr<f>: {e}"));
    wasm::compile_object_with_license(&plain, &permit_unlicensed())
        .unwrap_or_else(|e| panic!("symaddr<f>: {e}"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
