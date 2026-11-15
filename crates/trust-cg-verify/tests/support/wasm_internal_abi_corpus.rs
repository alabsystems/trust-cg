// trust-cg-verify/tests/support/wasm_internal_abi_corpus.rs - the internal
// multi-value ABI corpus, compiled by the live wasm object lane
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The trust-ir modules and hand-built objects the internal-ABI gate
//! (`trust_cg_verify::wasm_internal_abi`) is exercised on: a callee object
//! defining every kind of callee (strong hidden crate-private functions with
//! scalar, pair, quad, mixed and 128-bit results; a five-lane one; a
//! link-once one; an exported one; an address-taken one), a caller object
//! declaring them, a static holding function pointers, the whole program as
//! one closed module, and hand-built objects that cross the boundary.
//!
//! Shared by `#[path]` with `trust-cg-codegen/tests/wasm_p6_multivalue.rs`,
//! which links and executes the same objects, so the gate's negative
//! controls and the link differential exercise one corpus.
//!
//! It compiles through `trust_cg_codegen::wasm::compile_object_optimized`
//! (round 8) and feeds `trust_cg_verify::wasm_internal_abi` (round 11), both
//! provisional surfaces pending the owner's sign-off: the corpus and its
//! targets follow them if they change, and are not a contract for their
//! shape.

#![allow(dead_code)]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm;
use trust_cg_verify::wasm_internal_abi as gate;
use trust_ir::Module;

pub const TAG: &str = "0123456789abcdef";

pub const TYPES: &str = "functy.0 = (i64, i64) -> (i64)\n\
functy.1 = (i128, i64) -> (u128)\n\
functy.2 = (i32, i32) -> (i32, i8)\n\
functy.3 = (i64) -> (i128, bool)\n\
functy.4 = (i128, i128) -> (i128, i128)\n\
functy.5 = (i64) -> (i128, i128, i32)\n\
functy.6 = (i64, i64) -> (i128)\n\
functy.7 = (i64) -> (f64, i32, i16)\n";

/// A crate-private name.
pub fn cp(name: &str) -> String {
    format!("{name}.tcg.crate.{TAG}")
}

/// How one function is spelled in a module.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Sym {
    /// Strong and hidden under a crate-private name: the internal ABI.
    Internal,
    /// `linkonce_odr`, hidden, crate-private: replaceable, so the C form.
    LinkOnce,
    /// Strong with default visibility: exported, so the C form.
    Exported,
}

/// `(symbol, kind, functy, body)`. A body names a function as `{name}`
/// (its id in the module being built) and folds a 128-bit `%r` with
/// `{fold:%r}`.
pub fn callees() -> Vec<(String, Sym, u32, String)> {
    vec![
        (
            cp("wide"),
            Sym::Internal,
            1,
            "bb0(%x: i128, %b: i64):\n    %w = sext i64 %b to i128\n    \
             %m = mul i128 %x, %w\n    %c3 = const i128 3\n    %s = add i128 %m, %c3\n    \
             %u = bitcast i128 %s to u128\n    ret %u\n"
                .to_string(),
        ),
        (
            cp("pair"),
            Sym::Internal,
            2,
            "bb0(%a: i32, %b: i32):\n    %s = add i32 %a, %b\n    \
             %t = trunc i32 %b to i8\n    ret %s, %t\n"
                .to_string(),
        ),
        (
            cp("trio"),
            Sym::Internal,
            3,
            "bb0(%x: i64):\n    %w = sext i64 %x to i128\n    %k = mul i128 %w, %w\n    \
             %z = const i64 0\n    %n = icmp slt i64 %x, %z\n    ret %k, %n\n"
                .to_string(),
        ),
        (
            cp("quad"),
            Sym::Internal,
            4,
            "bb0(%p: i128, %q: i128):\n    %s = add i128 %p, %q\n    \
             %m = mul i128 %p, %q\n    ret %s, %m\n"
                .to_string(),
        ),
        (
            cp("five"),
            Sym::Internal,
            5,
            "bb0(%x: i64):\n    %w = sext i64 %x to i128\n    %k = mul i128 %w, %w\n    \
             %t = trunc i64 %x to i32\n    ret %w, %k, %t\n"
                .to_string(),
        ),
        (
            cp("once"),
            Sym::LinkOnce,
            6,
            "bb0(%a: i64, %b: i64):\n    %x = sext i64 %a to i128\n    \
             %y = zext i64 %b to i128\n    %m = mul i128 %x, %y\n    ret %m\n"
                .to_string(),
        ),
        (
            "pub_wide".to_string(),
            Sym::Exported,
            6,
            "bb0(%a: i64, %b: i64):\n    %x = sext i64 %a to i128\n    \
             %c64 = const i128 64\n    %h = shl i128 %x, %c64\n    \
             %y = zext i64 %b to i128\n    %r = or i128 %h, %y\n    ret %r\n"
                .to_string(),
        ),
        (
            cp("mixed"),
            Sym::Internal,
            7,
            "bb0(%x: i64):\n    %f = sitofp i64 %x to f64\n    %t = trunc i64 %x to i32\n    \
             %h = trunc i64 %x to i16\n    ret %f, %t, %h\n"
                .to_string(),
        ),
        (
            cp("taken"),
            Sym::Internal,
            6,
            "bb0(%a: i64, %b: i64):\n    %x = zext i64 %a to i128\n    \
             %y = sext i64 %b to i128\n    %s = sub i128 %x, %y\n    ret %s\n"
                .to_string(),
        ),
    ]
}

/// `%r` (128-bit) folded into `%{p}f`, an `i64`, as `lo ^ hi * 31`.
pub fn fold(p: &str, r: &str) -> String {
    format!(
        "    %{p}lo = trunc i128 {r} to i64\n    %{p}c64 = const i128 64\n    \
         %{p}sh = lshr i128 {r}, %{p}c64\n    %{p}hi = trunc i128 %{p}sh to i64\n    \
         %{p}c31 = const i64 31\n    %{p}hm = mul i64 %{p}hi, %{p}c31\n    \
         %{p}f = xor i64 %{p}lo, %{p}hm\n"
    )
}

/// An entry `(i64, i64) -> i64` calling every callee directly, and `taken`
/// through a function pointer too.
pub fn caller_body() -> String {
    let mut b = String::from(
        "bb0(%a: i64, %b: i64):\n    %x = sext i64 %a to i128\n    %y = zext i64 %b to i128\n",
    );
    b.push_str(&format!("    %r1 = call @{{{}}}(%x, %b)\n", cp("wide")));
    b.push_str("    %r1s = bitcast u128 %r1 to i128\n");
    b.push_str(&fold("v1", "%r1s"));
    b.push_str("    %a32 = trunc i64 %a to i32\n    %b32 = trunc i64 %b to i32\n");
    b.push_str(&format!(
        "    %ps, %pt = call @{{{}}}(%a32, %b32)\n",
        cp("pair")
    ));
    b.push_str(
        "    %ps64 = sext i32 %ps to i64\n    %pt64 = sext i8 %pt to i64\n    \
         %v2 = xor i64 %ps64, %pt64\n",
    );
    b.push_str(&format!("    %tk, %tn = call @{{{}}}(%a)\n", cp("trio")));
    b.push_str(&fold("v3", "%tk"));
    b.push_str("    %tn64 = zext bool %tn to i64\n    %v3 = add i64 %v3f, %tn64\n");
    b.push_str(&format!(
        "    %qs, %qm = call @{{{}}}(%x, %y)\n",
        cp("quad")
    ));
    b.push_str(&fold("v4", "%qs"));
    b.push_str(&fold("v5", "%qm"));
    b.push_str(&format!(
        "    %fw, %fk, %ft = call @{{{}}}(%b)\n",
        cp("five")
    ));
    b.push_str(&fold("v6", "%fk"));
    b.push_str(&fold("v7", "%fw"));
    b.push_str("    %ft64 = sext i32 %ft to i64\n");
    b.push_str(&format!("    %o = call @{{{}}}(%a, %b)\n", cp("once")));
    b.push_str(&fold("v8", "%o"));
    b.push_str("    %pw = call @{pub_wide}(%b, %a)\n");
    b.push_str(&fold("v9", "%pw"));
    b.push_str(&format!(
        "    %mf, %mt, %mh = call @{{{}}}(%a)\n",
        cp("mixed")
    ));
    b.push_str(
        "    %mfi = fptosi.sat f64 %mf to i64\n    %mt64 = sext i32 %mt to i64\n    \
         %mh64 = sext i16 %mh to i64\n",
    );
    b.push_str(&format!("    %d = call @{{{}}}(%a, %b)\n", cp("taken")));
    b.push_str(&fold("v10", "%d"));
    b.push_str(&format!(
        "    %fp = const functy.6 fndef<{{{}}}>\n    %e = call_indirect %fp(functy.6)(%b, %a)\n",
        cp("taken")
    ));
    b.push_str(&fold("v11", "%e"));
    let terms = [
        "%v1f", "%v2", "%v3", "%v4f", "%v5f", "%v6f", "%v7f", "%ft64", "%v8f", "%v9f", "%mfi",
        "%mt64", "%mh64", "%v10f", "%v11f",
    ];
    let mut acc = terms[0].to_string();
    for (k, t) in terms.iter().enumerate().skip(1) {
        b.push_str(&format!(
            "    %acc{k}m = mul i64 {acc}, %c7\n    %acc{k} = xor i64 %acc{k}m, {t}\n"
        ));
        acc = format!("%acc{k}");
    }
    b.push_str(&format!("    ret {acc}\n"));
    b.replacen(
        "bb0(%a: i64, %b: i64):\n",
        "bb0(%a: i64, %b: i64):\n    %c7 = const i64 7\n",
        1,
    )
}

/// An entry that calls `wide` and `taken` through the pointers a static
/// holds (`global.0`).
pub fn table_body() -> String {
    format!(
        "bb0(%a: i64, %b: i64):\n    %g = global_addr @global.0\n    \
         %p0 = load ptr, ptr %g\n    %x = sext i64 %a to i128\n    \
         %r = call_indirect %p0(functy.1)(%x, %b)\n    %rs = bitcast u128 %r to i128\n{}    \
         %c4 = const i32 4\n    %gi = ptrtoint ptr %g to i32\n    %g1i = add i32 %gi, %c4\n    \
         %g1 = inttoptr i32 %g1i to ptr\n    %p1 = load ptr, ptr %g1\n    \
         %t = call_indirect %p1(functy.6)(%a, %b)\n{}    %s = xor i64 %v1f, %v2f\n    ret %s\n",
        fold("v1", "%rs"),
        fold("v2", "%t")
    )
}

/// One function of a module being built: its symbol, its header keyword and
/// visibility, its type, and its body (`None`: a declaration).
pub struct Item {
    pub name: String,
    pub kind: Sym,
    pub functy: u32,
    pub body: Option<String>,
}

/// Assemble a module: `globals` lines, then the items in order, with every
/// `{name}` replaced by that function's id and value names numbered. A
/// closed module states no linkage or visibility (it has no linker).
pub fn assemble(tag: &str, globals: &str, items: &[Item]) -> Module {
    assemble_as(tag, globals, items, false)
}

pub fn assemble_as(tag: &str, globals: &str, items: &[Item], closed: bool) -> Module {
    let ids: HashMap<&str, usize> = items
        .iter()
        .enumerate()
        .map(|(i, it)| (it.name.as_str(), i))
        .collect();
    let mut text = format!(
        "module \"{tag}\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n{TYPES}\n{globals}\n"
    );
    for it in items {
        let linkage = if !closed && it.kind == Sym::LinkOnce && it.body.is_some() {
            "linkonce_odr "
        } else {
            ""
        };
        // A declaration of a strong crate-private symbol carries its
        // definition's hidden visibility (the bridge stamps it so); a
        // link-once one is declared at default visibility.
        let hidden = match (it.kind, it.body.is_some()) {
            _ if closed => "",
            (Sym::Internal, _) | (Sym::LinkOnce, true) => "    ; #visibility: hidden\n",
            _ => "",
        };
        let mut body = it.body.clone().unwrap_or_default();
        for (name, id) in &ids {
            body = body.replace(&format!("{{{name}}}"), &format!("func.{id}"));
        }
        text.push_str(&format!(
            "{linkage}fn @{}(functy.{}) {{\n{hidden}{}}}\n\n",
            it.name, it.functy, body
        ));
    }
    let text = number_values(&text);
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| {
        let numbered: String = text
            .lines()
            .enumerate()
            .map(|(i, l)| format!("{:4} {l}\n", i + 1))
            .collect();
        panic!("module `{tag}` does not parse: {e}\n{numbered}")
    })
}

/// Rename `%name` values to the text format's numeric spelling, per
/// function, in order of first appearance.
pub fn number_values(text: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(text.len());
    let mut values: HashMap<String, usize> = HashMap::new();
    for line in text.lines() {
        if line.contains("fn @") {
            values.clear();
        }
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'%' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
                let mut end = i + 1;
                while end < bytes.len()
                    && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_')
                {
                    end += 1;
                }
                let n = values.len() + 1;
                let id = *values.entry(line[i + 1..end].to_string()).or_insert(n);
                let _ = write!(out, "%{id}");
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

pub fn define(name: &str, kind: Sym, functy: u32, body: &str) -> Item {
    Item {
        name: name.to_string(),
        kind,
        functy,
        body: Some(body.to_string()),
    }
}

pub fn declare(name: &str, kind: Sym, functy: u32) -> Item {
    Item {
        name: name.to_string(),
        kind,
        functy,
        body: None,
    }
}

/// The callee object: every callee defined, plus an entry calling them
/// within the object.
pub fn callee_module() -> Module {
    let mut items: Vec<Item> = callees()
        .iter()
        .map(|(n, k, t, b)| define(n, *k, *t, b))
        .collect();
    items.push(define("a_entry", Sym::Exported, 0, &caller_body()));
    assemble("callee", "", &items)
}

/// A caller object: every callee declared, one entry named `entry`.
pub fn caller_module(entry: &str) -> Module {
    let mut items: Vec<Item> = callees()
        .iter()
        .map(|(n, k, t, _)| declare(n, *k, *t))
        .collect();
    items.push(define(entry, Sym::Exported, 0, &caller_body()));
    assemble(entry, "", &items)
}

/// A static holding pointers to `wide` and `taken`, and an entry calling
/// through them.
pub fn table_module() -> Module {
    let items = vec![
        declare(&cp("wide"), Sym::Internal, 1),
        declare(&cp("taken"), Sym::Internal, 6),
        define("c_entry", Sym::Exported, 0, &table_body()),
    ];
    // The slots are `ptr`s, so each names its function by symbol (`symaddr`,
    // the function's table index on wasm32): trust-ir types `fndef` at a
    // function type only.
    assemble(
        "table",
        &format!(
            "type ty.0 = ptr\n\nglobal @fptrs [ty.0 x 2] = array[ symaddr<{}>, symaddr<{}> ]\n",
            cp("wide"),
            cp("taken")
        ),
        &items,
    )
}

/// The whole program as one module: the reference.
pub fn whole_module() -> Module {
    let mut items: Vec<Item> = callees()
        .iter()
        .map(|(n, k, t, b)| define(n, *k, *t, b))
        .collect();
    for entry in ["a_entry", "b_entry", "b0_entry"] {
        items.push(define(entry, Sym::Exported, 0, &caller_body()));
    }
    items.push(define("c_entry", Sym::Exported, 0, &table_body()));
    assemble_as(
        "whole",
        &format!(
            "type ty.0 = ptr\n\nglobal @fptrs [ty.0 x 2] = array[ symaddr<{}>, symaddr<{}> ]\n",
            cp("wide"),
            cp("taken")
        ),
        &items,
        true,
    )
}

/// The relocatable object the live lane emits for `module` at `level`.
pub fn compile(module: &Module, level: OptLevel) -> Vec<u8> {
    wasm::compile_object_with_license_optimized(module, &permit_unlicensed(), level)
        .unwrap_or_else(|e| panic!("compile `{}` at {level:?}: {e}", module.name))
}

/// The symbols of `bytes` by name: `(flags, defined)`.
pub fn symbols(bytes: &[u8]) -> HashMap<String, (u32, bool)> {
    let o = gate::decode_object(bytes).expect("decode the object");
    o.symbols
        .iter()
        .filter(|s| s.kind == 0)
        .filter_map(|s| {
            o.symbol_name(s)
                .map(|n| (n, (s.flags, s.flags & 0x10 == 0)))
        })
        .collect()
}

pub fn mv(name: &str) -> String {
    format!("{name}{}", gate::INTERNAL_ENTRY_SUFFIX)
}

/// Patch one byte of `bytes`.
pub fn patched(bytes: &[u8], at: usize, value: u8) -> Vec<u8> {
    let mut out = bytes.to_vec();
    out[at] = value;
    out
}

/// A hand-built object around one multi-value function `name` of type
/// `() -> (i64, i64)`, with `flags`, called by a second function, which
/// also takes its address when `address_taken`.
pub fn hand_object(name: &str, flags: wasm::encode::SymbolFlags, address_taken: bool) -> Vec<u8> {
    use wasm::encode::{
        FuncBody, FuncType, Reloc, RelocKind, RelocTarget, ValType, WasmModule,
        write_padded_sleb128, write_padded_uleb128,
    };
    let mut m = WasmModule::new_object();
    let mv_ty = m.add_type(FuncType {
        params: vec![],
        results: vec![ValType::I64, ValType::I64],
    });
    let caller_ty = m.add_type(FuncType {
        params: vec![],
        results: vec![ValType::I64],
    });
    // `i64.const 1; i64.const 2`.
    let f = m.add_function(
        mv_ty,
        FuncBody {
            locals: vec![],
            code: vec![0x42, 0x01, 0x42, 0x02],
            relocs: vec![],
        },
    );
    m.set_function_symbol(f, name, flags);
    let mut code = vec![0x10];
    let mut relocs = vec![Reloc {
        kind: RelocKind::FunctionIndexLeb,
        offset: 1,
        target: RelocTarget::Func(f),
        addend: 0,
    }];
    write_padded_uleb128(&mut code, f);
    code.push(0x85); // i64.xor
    if address_taken {
        code.push(0x41); // i32.const <table index>
        relocs.push(Reloc {
            kind: RelocKind::TableIndexSleb,
            offset: code.len() as u32,
            target: RelocTarget::Func(f),
            addend: 0,
        });
        write_padded_sleb128(&mut code, f as i32);
        code.push(0x1a); // drop
    }
    let g = m.add_function(
        caller_ty,
        FuncBody {
            locals: vec![],
            code,
            relocs,
        },
    );
    m.set_function_symbol(g, "caller", wasm::encode::SymbolFlags::default());
    m.require_feature("multivalue");
    m.finish()
}

/// A closed module (no symbol table) whose multi-value function is exported
/// and in the function table.
pub fn closed_exporting_module() -> Vec<u8> {
    use wasm::encode::{FuncBody, FuncType, ValType, WasmModule};
    let mut m = WasmModule::new();
    let ty = m.add_type(FuncType {
        params: vec![],
        results: vec![ValType::I64, ValType::I64],
    });
    let f = m.add_function(
        ty,
        FuncBody {
            locals: vec![],
            code: vec![0x42, 0x01, 0x42, 0x02],
            relocs: vec![],
        },
    );
    m.export_func("f", f);
    m.enable_func_table();
    m.finish()
}

/// This module's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
