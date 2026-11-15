// trust-cg-verify/wasm_internal_abi.rs - the wasm32 internal-ABI boundary gate
// and the multi-value call/return binding (P6, a sibling of the call/table
// ABI family in `wasm_abi_proofs.rs`; its live gate is the soundness-gate
// target `tests/wasm_internal_abi_gate.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — "Binary Format";
//            WebAssembly tool-conventions `Linking.md` (the `linking` symbol
//            table, `reloc.*` sections, `target_features`) and `BasicCABI.md`.
//
// WHAT THIS MODULE IS
//
// The wasm32 object lane returns the results of a crate-internal function as
// wasm multi-value results instead of through the BasicCABI's `sret` buffer
// (crates/trust-cg-codegen/src/wasm/lower/abi.rs, "the internal ABI"). That
// convention is sound only where every caller and callee agrees on it, so it
// must never meet code this crate does not compile: an exported function, a
// function in the indirect-call table, a function whose address is taken, a
// symbol the linker may replace. This module decides that over the OBJECT
// BYTES, by decoding the symbol table, the relocations, the export and
// element sections and the function types itself (its own reader: nothing
// here reads `encode.rs` or `lower.rs`):
//
//   * the GATE ([`check_object`]): every function whose wasm type has more
//     than one result — the only signatures the BasicCABI never produces — is
//     an internal entry: one function symbol names it, that symbol is local,
//     or strong and hidden under the reserved crate-private internal-entry
//     name ([`is_internal_entry_name`]); it is not exported (flag or export
//     section), is in no element segment, and every relocation naming it is a
//     `R_WASM_FUNCTION_INDEX_LEB` at the immediate of a `call` (never
//     `ref.func`, a table index, or a data word); no relocated
//     `call_indirect` type has several results; the object declares
//     `+multivalue`; and every symbol under the reserved name has a
//     multi-value type. `wasm-ld`'s signature check is only a second line of
//     defence behind this.
//   * the RETURN BINDING ([`check_object`], per defined internal entry): the
//     C-form entry under the plain crate-private name forwards to the
//     internal entry and stores every result it returns exactly once, in
//     result order, with a store of the result's own value type, into
//     pairwise-disjoint bytes of the `sret` buffer its first parameter
//     addresses; its parameters are the internal entry's after that pointer.
//   * the SOURCE BINDING ([`check_object_against_module`]): against the
//     trust-ir module the object was lowered from, every internal entry's
//     results are those the trust-ir signature intends (a scalar's value
//     type, a 128-bit integer's low and high `i64` halves), and the C-form
//     entry's stores land at the BasicCABI layout of the trust-ir results
//     (each valued result at the running offset rounded up to its trust-ir
//     alignment, as wide as its trust-ir size), computed here from trust-ir's
//     own layout table.
//   * the LINK BINDING ([`check_link`]): across the objects of one crate,
//     each internal entry any object imports or defines is defined by
//     exactly one of them, and every import of it has the definition's type.
//
// WHAT THIS MODULE IS NOT
//
// The checks are structural and decidable, reported as `AbiStructuralCheck`s
// like the rest of the call/table family: no solver is involved. They do not
// prove that the internal entry computes what the trust-ir function computes
// (the lowering's value-domain and differential evidence does), nor that the
// objects handed to `check_link` are all of a crate's objects. A crate-private
// name is a naming contract the rustc bridge keeps (a CGU-private symbol of
// one crate, renamed with that crate's `StableCrateId`); this module checks
// the name's form, not who chose it.

//! The wasm32 internal-ABI boundary gate and the multi-value call/return
//! binding: structural checks over a relocatable object's symbol table,
//! relocations, exports, element segments and the C-form forwarding entries.
//!
//! This module's public items are a new surface pending owner sign-off: the
//! wasm lane and the rustc bridge call [`check_object_against_module`] and
//! [`check_link`]; the decoder and evidence types are exposed for tests and
//! are not a settled contract.

use std::collections::BTreeMap;

use trust_ir::{Module, Ty};

use crate::wasm_abi_proofs::{AbiStructuralCheck, DecodedFuncType, DecodedInst, Imm, decode_insts};

/// The suffix of an internal entry's symbol: `<crate-private name>.tcg.mv`.
pub const INTERNAL_ENTRY_SUFFIX: &str = ".tcg.mv";

/// The mark a crate-private name carries before its 16 lowercase hex digits
/// (`<symbol>.tcg.crate.<StableCrateId>`).
pub const CRATE_PRIVATE_MARK: &str = ".tcg.crate.";

/// `WASM_SYM_BINDING_WEAK`.
const SYM_WEAK: u32 = 0x1;
/// `WASM_SYM_BINDING_LOCAL`.
const SYM_LOCAL: u32 = 0x2;
/// `WASM_SYM_VISIBILITY_HIDDEN`.
const SYM_HIDDEN: u32 = 0x4;
/// `WASM_SYM_UNDEFINED`.
const SYM_UNDEFINED: u32 = 0x10;
/// `WASM_SYM_EXPORTED`.
const SYM_EXPORTED: u32 = 0x20;
/// `WASM_SYM_EXPLICIT_NAME`.
const SYM_EXPLICIT_NAME: u32 = 0x40;

/// `WASM_SYMBOL_TYPE_FUNCTION`.
const SYMTAB_FUNCTION: u8 = 0;
/// `WASM_SYMBOL_TYPE_DATA`.
const SYMTAB_DATA: u8 = 1;
/// `WASM_SYMBOL_TYPE_SECTION`.
const SYMTAB_SECTION: u8 = 3;

/// `R_WASM_FUNCTION_INDEX_LEB`: a `call`'s (or `ref.func`'s) function index.
pub const R_FUNCTION_INDEX_LEB: u8 = 0;
/// `R_WASM_TABLE_INDEX_SLEB`: a function pointer in code.
pub const R_TABLE_INDEX_SLEB: u8 = 1;
/// `R_WASM_TYPE_INDEX_LEB`: a `call_indirect`'s type index.
pub const R_TYPE_INDEX_LEB: u8 = 6;

/// Relocation types whose symbol index names a SYMBOL (every type but
/// `R_WASM_TYPE_INDEX_LEB`, whose index is a type index).
fn reloc_names_symbol(ty: u8) -> bool {
    ty != R_TYPE_INDEX_LEB
}

/// Relocation types that carry an addend (tool-conventions `Linking.md`).
fn reloc_has_addend(ty: u8) -> Result<bool, String> {
    match ty {
        0 | 1 | 2 | 6 | 7 | 10 | 12 | 13 | 18 | 19 | 20 | 24 | 26 => Ok(false),
        3 | 4 | 5 | 8 | 9 | 11 | 14 | 15 | 16 | 17 | 21 | 22 | 23 | 25 => Ok(true),
        other => Err(format!("unknown relocation type {other}")),
    }
}

const OP_CALL: u8 = 0x10;
const OP_END: u8 = 0x0b;
const OP_LOCAL_GET: u8 = 0x20;
const OP_LOCAL_SET: u8 = 0x21;
const VT_I32: u8 = 0x7f;
const VT_I64: u8 = 0x7e;
const VT_F32: u8 = 0x7d;
const VT_F64: u8 = 0x7c;

/// Whether `name` is an internal entry's name: a crate-private name — a
/// non-empty symbol, [`CRATE_PRIVATE_MARK`], exactly 16 lowercase hex digits
/// — followed by [`INTERNAL_ENTRY_SUFFIX`].
pub fn is_internal_entry_name(name: &str) -> bool {
    let Some(base) = name.strip_suffix(INTERNAL_ENTRY_SUFFIX) else {
        return false;
    };
    let Some(at) = base.rfind(CRATE_PRIVATE_MARK) else {
        return false;
    };
    let tag = &base[at + CRATE_PRIVATE_MARK.len()..];
    at > 0
        && tag.len() == 16
        && tag
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

// ===========================================================================
// The object reader
// ===========================================================================

/// A byte cursor.
struct Cur<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Cur<'a> {
    fn new(b: &'a [u8]) -> Self {
        Cur { b, p: 0 }
    }

    fn done(&self) -> bool {
        self.p >= self.b.len()
    }

    fn byte(&mut self, what: &str) -> Result<u8, String> {
        let v = *self
            .b
            .get(self.p)
            .ok_or_else(|| format!("truncated reading {what}"))?;
        self.p += 1;
        Ok(v)
    }

    fn take(&mut self, n: usize, what: &str) -> Result<&'a [u8], String> {
        let end = self
            .p
            .checked_add(n)
            .filter(|&e| e <= self.b.len())
            .ok_or_else(|| format!("truncated reading {what}"))?;
        let s = &self.b[self.p..end];
        self.p = end;
        Ok(s)
    }

    fn uleb(&mut self, what: &str) -> Result<u64, String> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = self.byte(what)?;
            if shift >= 64 || (shift == 63 && byte & 0x7e != 0) {
                return Err(format!("LEB128 overflow reading {what}"));
            }
            result |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    fn u32(&mut self, what: &str) -> Result<u32, String> {
        u32::try_from(self.uleb(what)?).map_err(|_| format!("LEB128 overflow reading {what}"))
    }

    fn sleb(&mut self, what: &str) -> Result<i64, String> {
        let mut result: i64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = self.byte(what)?;
            if shift >= 64 {
                return Err(format!("LEB128 overflow reading {what}"));
            }
            result |= i64::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                if shift < 64 && byte & 0x40 != 0 {
                    result |= -1i64 << shift;
                }
                return Ok(result);
            }
        }
    }

    fn name(&mut self, what: &str) -> Result<String, String> {
        let n = self.u32(what)? as usize;
        let bytes = self.take(n, what)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| format!("{what} is not UTF-8"))
    }

    /// A constant offset expression: `i32.const k` or `global.get g`, then
    /// `end`.
    fn const_expr(&mut self) -> Result<(), String> {
        match self.byte("constant expression")? {
            0x41 => {
                self.sleb("i32.const")?;
            }
            0x23 => {
                self.u32("global.get")?;
            }
            other => {
                return Err(format!(
                    "unmodeled constant expression opcode 0x{other:02x}"
                ));
            }
        }
        match self.byte("constant expression end")? {
            OP_END => Ok(()),
            other => Err(format!("constant expression continues with 0x{other:02x}")),
        }
    }

    fn limits(&mut self) -> Result<(), String> {
        let flags = self.byte("limits flags")?;
        if flags & !0x07 != 0 {
            return Err(format!("unknown limits flags 0x{flags:02x}"));
        }
        self.uleb("limits minimum")?;
        if flags & 1 != 0 {
            self.uleb("limits maximum")?;
        }
        Ok(())
    }
}

/// One function import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectFuncImport {
    /// The import module name.
    pub module: String,
    /// The import field name.
    pub field: String,
    /// Its type index.
    pub type_idx: u32,
}

/// One `linking` symbol-table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectSymbol {
    /// `WASM_SYMBOL_TYPE_*`.
    pub kind: u8,
    /// `WASM_SYM_*` flags.
    pub flags: u32,
    /// The function / global / table / tag index, or the section index.
    pub index: Option<u32>,
    /// The symbol's own name, when the entry carries one.
    pub name: Option<String>,
    /// File offset of the flags' first byte.
    pub flags_at: usize,
}

/// One relocation entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectReloc {
    /// The index, in file order, of the section the relocation patches.
    pub section: u32,
    /// `R_WASM_*` type.
    pub ty: u8,
    /// Offset of the patched field within that section's payload.
    pub offset: u32,
    /// Symbol index (a type index for `R_WASM_TYPE_INDEX_LEB`).
    pub index: u32,
    /// File offset of the type byte.
    pub ty_at: usize,
}

/// One code-section entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectBody {
    /// Offset of the body's first byte (after its size) in the code
    /// section's payload.
    pub start: usize,
    /// Offset one past its last byte.
    pub end: usize,
    /// Declared locals, expanded one per local.
    pub locals: Vec<u8>,
    /// Offset of the first instruction in the code section's payload.
    pub code_start: usize,
}

/// The parts of a relocatable wasm object the gate reads.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DecodedObject {
    /// Type section.
    pub types: Vec<DecodedFuncType>,
    /// Function imports, in index order (the low function index space).
    pub func_imports: Vec<ObjectFuncImport>,
    /// Type index of each defined function.
    pub defined_types: Vec<u32>,
    /// Function exports: `(name, function index)`.
    pub func_exports: Vec<(String, u32)>,
    /// Every function index any element segment holds.
    pub elem_funcs: Vec<u32>,
    /// The code section's payload.
    pub code: Vec<u8>,
    /// File offset of the code section's payload.
    pub code_at: usize,
    /// The code section's index in file order.
    pub code_section: Option<u32>,
    /// Code-section entries.
    pub bodies: Vec<ObjectBody>,
    /// The `linking` symbol table.
    pub symbols: Vec<ObjectSymbol>,
    /// Every relocation of every `reloc.*` section.
    pub relocs: Vec<ObjectReloc>,
    /// `target_features` entries: `(prefix, name)`.
    pub features: Vec<(u8, String)>,
    /// Whether a `linking` section was present.
    pub linking: bool,
}

impl DecodedObject {
    /// The type of function index `f`.
    pub fn type_of_func(&self, f: u32) -> Option<&DecodedFuncType> {
        let n = self.func_imports.len() as u32;
        let t = if f < n {
            self.func_imports[f as usize].type_idx
        } else {
            *self.defined_types.get((f - n) as usize)?
        };
        self.types.get(t as usize)
    }

    /// The function index space's size.
    pub fn func_count(&self) -> u32 {
        (self.func_imports.len() + self.defined_types.len()) as u32
    }

    /// Whether `f` is imported.
    pub fn is_import(&self, f: u32) -> bool {
        (f as usize) < self.func_imports.len()
    }

    /// The name a function symbol binds: its own name, or for an undefined
    /// symbol without an explicit name, its import's field name.
    pub fn symbol_name(&self, s: &ObjectSymbol) -> Option<String> {
        if let Some(n) = &s.name {
            return Some(n.clone());
        }
        let i = s.index? as usize;
        (s.kind == SYMTAB_FUNCTION && s.flags & SYM_UNDEFINED != 0)
            .then(|| self.func_imports.get(i).map(|imp| imp.field.clone()))
            .flatten()
    }

    /// The function symbols naming function index `f`, with their positions.
    pub fn func_symbols(&self, f: u32) -> Vec<(usize, &ObjectSymbol)> {
        self.symbols
            .iter()
            .enumerate()
            .filter(|(_, s)| s.kind == SYMTAB_FUNCTION && s.index == Some(f))
            .collect()
    }
}

/// Decode a relocatable wasm object. Fails closed on any section, symbol,
/// relocation or element form it does not model.
pub fn decode_object(bytes: &[u8]) -> Result<DecodedObject, String> {
    let mut c = Cur::new(bytes);
    if c.take(4, "magic")? != b"\0asm" || c.take(4, "version")? != [1, 0, 0, 0] {
        return Err("not a wasm binary (bad magic or version)".to_string());
    }
    let mut o = DecodedObject::default();
    let mut section_index: u32 = 0;
    let mut reloc_sections: Vec<(usize, &[u8])> = Vec::new();
    while !c.done() {
        let id = c.byte("section id")?;
        let size = c.u32("section size")? as usize;
        let at = c.p;
        let body = c.take(size, "section payload")?;
        let mut s = Cur::new(body);
        match id {
            0 => {
                let name = s.name("custom section name")?;
                if name == "linking" {
                    o.linking = true;
                    read_linking(&mut s, at, &mut o)?;
                } else if name.starts_with("reloc.") {
                    reloc_sections.push((at + s.p, &body[s.p..]));
                } else if name == "target_features" {
                    let n = s.u32("feature count")?;
                    for _ in 0..n {
                        let prefix = s.byte("feature prefix")?;
                        o.features.push((prefix, s.name("feature name")?));
                    }
                }
            }
            1 => {
                let n = s.u32("type count")?;
                for _ in 0..n {
                    if s.byte("type form")? != 0x60 {
                        return Err("a type that is not a function type".to_string());
                    }
                    let np = s.u32("param count")? as usize;
                    let params = s.take(np, "param types")?.to_vec();
                    let nr = s.u32("result count")? as usize;
                    let results = s.take(nr, "result types")?.to_vec();
                    o.types.push(DecodedFuncType { params, results });
                }
            }
            2 => {
                let n = s.u32("import count")?;
                for _ in 0..n {
                    let module = s.name("import module")?;
                    let field = s.name("import field")?;
                    match s.byte("import kind")? {
                        0 => {
                            let type_idx = s.u32("import type")?;
                            o.func_imports.push(ObjectFuncImport {
                                module,
                                field,
                                type_idx,
                            });
                        }
                        1 => {
                            s.byte("table element type")?;
                            s.limits()?;
                        }
                        2 => s.limits()?,
                        3 => {
                            s.byte("global type")?;
                            s.byte("global mutability")?;
                        }
                        4 => {
                            s.byte("tag attribute")?;
                            s.u32("tag type")?;
                        }
                        other => return Err(format!("unknown import kind {other}")),
                    }
                }
            }
            3 => {
                let n = s.u32("function count")?;
                for _ in 0..n {
                    o.defined_types.push(s.u32("function type")?);
                }
            }
            7 => {
                let n = s.u32("export count")?;
                for _ in 0..n {
                    let name = s.name("export name")?;
                    let kind = s.byte("export kind")?;
                    let index = s.u32("export index")?;
                    if kind == 0 {
                        o.func_exports.push((name, index));
                    }
                }
            }
            9 => {
                let n = s.u32("element segment count")?;
                for _ in 0..n {
                    let flags = s.u32("element segment flags")?;
                    match flags {
                        0 => s.const_expr()?,
                        1 | 3 => {
                            if s.byte("element kind")? != 0 {
                                return Err("an element kind other than funcref".to_string());
                            }
                        }
                        2 => {
                            s.u32("element table")?;
                            s.const_expr()?;
                            if s.byte("element kind")? != 0 {
                                return Err("an element kind other than funcref".to_string());
                            }
                        }
                        other => {
                            return Err(format!(
                                "element segment form {other} (expressions) is not modeled"
                            ));
                        }
                    }
                    let k = s.u32("element count")?;
                    for _ in 0..k {
                        o.elem_funcs.push(s.u32("element function")?);
                    }
                }
            }
            10 => {
                o.code = body.to_vec();
                o.code_at = at;
                o.code_section = Some(section_index);
                let n = s.u32("body count")?;
                for _ in 0..n {
                    let len = s.u32("body size")? as usize;
                    let start = s.p;
                    let end = start
                        .checked_add(len)
                        .filter(|&e| e <= body.len())
                        .ok_or("truncated function body")?;
                    let mut b = Cur::new(&body[start..end]);
                    let runs = b.u32("local run count")?;
                    let mut locals = Vec::new();
                    for _ in 0..runs {
                        let k = b.u32("local run length")? as usize;
                        let ty = b.byte("local type")?;
                        if locals.len().saturating_add(k) > 50_000 {
                            return Err("more than 50000 declared locals".to_string());
                        }
                        locals.extend(std::iter::repeat_n(ty, k));
                    }
                    o.bodies.push(ObjectBody {
                        start,
                        end,
                        locals,
                        code_start: start + b.p,
                    });
                    s.p = end;
                }
            }
            4 | 5 | 6 | 8 | 11 | 12 | 13 => {}
            other => return Err(format!("unknown section id {other}")),
        }
        section_index += 1;
    }
    for (at, payload) in reloc_sections {
        let mut s = Cur::new(payload);
        let section = s.u32("relocated section")?;
        let n = s.u32("relocation count")?;
        for _ in 0..n {
            let ty_at = at + s.p;
            let ty = s.byte("relocation type")?;
            let offset = s.u32("relocation offset")?;
            let index = s.u32("relocation index")?;
            if reloc_has_addend(ty)? {
                s.sleb("relocation addend")?;
            }
            o.relocs.push(ObjectReloc {
                section,
                ty,
                offset,
                index,
                ty_at,
            });
        }
    }
    if o.defined_types.len() != o.bodies.len() {
        return Err(format!(
            "{} defined functions but {} bodies",
            o.defined_types.len(),
            o.bodies.len()
        ));
    }
    Ok(o)
}

/// Read the `linking` section's symbol table (other subsections skipped).
fn read_linking(s: &mut Cur<'_>, at: usize, o: &mut DecodedObject) -> Result<(), String> {
    let version = s.u32("linking version")?;
    if version != 2 {
        return Err(format!("linking section version {version}"));
    }
    while !s.done() {
        let sub = s.byte("linking subsection")?;
        let len = s.u32("linking subsection size")? as usize;
        let start = s.p;
        let payload = s.take(len, "linking subsection")?;
        if sub != 8 {
            continue;
        }
        let mut t = Cur::new(payload);
        let n = t.u32("symbol count")?;
        for _ in 0..n {
            let kind = t.byte("symbol kind")?;
            let flags_at = at + start + t.p;
            let flags = t.u32("symbol flags")?;
            let undefined = flags & SYM_UNDEFINED != 0;
            let (index, name) = match kind {
                SYMTAB_DATA => {
                    let name = t.name("data symbol name")?;
                    if !undefined {
                        t.uleb("data segment")?;
                        t.uleb("data offset")?;
                        t.uleb("data size")?;
                    }
                    (None, Some(name))
                }
                SYMTAB_SECTION => (Some(t.u32("section symbol index")?), None),
                0 | 2 | 4 | 5 => {
                    let index = t.u32("symbol index")?;
                    let name = if !undefined || flags & SYM_EXPLICIT_NAME != 0 {
                        Some(t.name("symbol name")?)
                    } else {
                        None
                    };
                    (Some(index), name)
                }
                other => return Err(format!("unknown symbol kind {other}")),
            };
            o.symbols.push(ObjectSymbol {
                kind,
                flags,
                index,
                name,
                flags_at,
            });
        }
    }
    Ok(())
}

// ===========================================================================
// The gate and the return binding
// ===========================================================================

/// What [`check_object`] established about one object.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InternalAbiEvidence {
    /// Internal entries the object defines.
    pub defined_entries: usize,
    /// Internal entries the object imports.
    pub imported_entries: usize,
    /// Relocated direct calls to an internal entry.
    pub direct_calls: usize,
    /// C-form entries whose forwarding body was checked.
    pub forwarding_entries: usize,
    /// Every check, passed or not.
    pub checks: Vec<AbiStructuralCheck>,
}

impl InternalAbiEvidence {
    /// Whether every check passed.
    pub fn holds(&self) -> bool {
        self.checks.iter().all(|c| c.ok)
    }

    /// The first failed check, rendered.
    pub fn first_failure(&self) -> Option<String> {
        self.checks
            .iter()
            .find(|c| !c.ok)
            .map(|c| format!("{}: {}", c.name, c.detail))
    }
}

fn push(out: &mut Vec<AbiStructuralCheck>, name: String, ok: bool, detail: String) {
    out.push(AbiStructuralCheck { name, ok, detail });
}

/// Width in bytes and value type of a store opcode.
fn store_shape(op: u8) -> Option<(u32, u8)> {
    Some(match op {
        0x36 => (4, VT_I32),
        0x37 => (8, VT_I64),
        0x38 => (4, VT_F32),
        0x39 => (8, VT_F64),
        0x3a => (1, VT_I32),
        0x3b => (2, VT_I32),
        0x3c => (1, VT_I64),
        0x3d => (2, VT_I64),
        0x3e => (4, VT_I64),
        _ => return None,
    })
}

/// One store of a C-form entry: the result it writes, its offset and width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ForwardedStore {
    /// Byte offset in the `sret` buffer.
    pub offset: u32,
    /// Bytes written.
    pub width: u32,
}

/// The internal entries of a decoded object and what the gate found, plus
/// the store layout of every C-form entry, by its plain name.
fn gate(o: &DecodedObject) -> (InternalAbiEvidence, BTreeMap<String, Vec<ForwardedStore>>) {
    let mut ev = InternalAbiEvidence::default();
    let mut layouts = BTreeMap::new();
    let mut checks = Vec::new();
    let checks = &mut checks;
    push(
        checks,
        "the object carries a linking section".to_string(),
        o.linking,
        format!("{} symbols", o.symbols.len()),
    );
    let multi = |f: u32| o.type_of_func(f).is_some_and(|t| t.results.len() > 1);
    // Symbol index -> function index, for the multi-value functions.
    let mut internal_symbols: BTreeMap<u32, u32> = BTreeMap::new();
    for f in (0..o.func_count()).filter(|&f| multi(f)) {
        let syms = o.func_symbols(f);
        let what = format!("multi-value function {f}");
        let name = match syms.as_slice() {
            [(si, sym)] => {
                internal_symbols.insert(*si as u32, f);
                let name = o.symbol_name(sym).unwrap_or_default();
                let local = sym.flags & SYM_LOCAL != 0;
                let entry = !local
                    && sym.flags & SYM_HIDDEN != 0
                    && sym.flags & SYM_WEAK == 0
                    && is_internal_entry_name(&name);
                let ok = (local || entry)
                    && sym.flags & SYM_EXPORTED == 0
                    && sym.flags & SYM_EXPLICIT_NAME == 0
                    && (!o.is_import(f) || o.func_imports[f as usize].module == "env");
                push(
                    checks,
                    format!("{what} `{name}` is local, or a strong hidden internal entry"),
                    ok,
                    format!("symbol flags 0x{:x}", sym.flags),
                );
                name
            }
            _ => {
                push(
                    checks,
                    format!("{what} has exactly one function symbol"),
                    false,
                    format!("{} symbols name it", syms.len()),
                );
                String::new()
            }
        };
        let exported: Vec<&str> = o
            .func_exports
            .iter()
            .filter(|(_, i)| *i == f)
            .map(|(n, _)| n.as_str())
            .collect();
        push(
            checks,
            format!("{what} `{name}` is not exported"),
            exported.is_empty(),
            format!("exported as {exported:?}"),
        );
        let in_table = o.elem_funcs.contains(&f);
        push(
            checks,
            format!("{what} `{name}` is in no element segment"),
            !in_table,
            format!("element segments hold it: {in_table}"),
        );
        if o.is_import(f) {
            ev.imported_entries += 1;
        } else {
            ev.defined_entries += 1;
        }
    }
    // Every reserved-name symbol is a multi-value function.
    for s in &o.symbols {
        let Some(name) = o.symbol_name(s) else {
            continue;
        };
        if name.ends_with(INTERNAL_ENTRY_SUFFIX) {
            let ok = s.kind == SYMTAB_FUNCTION && s.index.is_some_and(multi);
            push(
                checks,
                format!("reserved internal-entry name `{name}` is a multi-value function"),
                ok,
                format!("symbol kind {}, index {:?}", s.kind, s.index),
            );
        }
    }
    // Every relocation naming an internal entry is a direct call.
    for r in &o.relocs {
        if !reloc_names_symbol(r.ty) {
            let t = o.types.get(r.index as usize);
            push(
                checks,
                format!("relocated type index {} is not a multi-value type", r.index),
                t.is_some_and(|t| t.results.len() <= 1),
                format!("type {t:?}"),
            );
            continue;
        }
        let Some(&f) = internal_symbols.get(&r.index) else {
            continue;
        };
        let in_code = Some(r.section) == o.code_section;
        let opcode = (r.offset as usize)
            .checked_sub(1)
            .and_then(|p| o.code.get(p))
            .copied();
        let ok = r.ty == R_FUNCTION_INDEX_LEB && in_code && opcode == Some(OP_CALL);
        if ok {
            ev.direct_calls += 1;
        }
        push(
            checks,
            format!("relocation of internal entry {f} is a direct call"),
            ok,
            format!(
                "type {}, section {} (code {:?}), opcode before offset {}: {opcode:?}",
                r.ty, r.section, o.code_section, r.offset
            ),
        );
    }
    if !internal_symbols.is_empty() {
        let declared = o
            .features
            .iter()
            .any(|(p, n)| *p == b'+' && n == "multivalue");
        push(
            checks,
            "the object declares +multivalue".to_string(),
            declared,
            format!("{:?}", o.features),
        );
    }
    // The return binding of every defined internal entry.
    for (&si, &f) in &internal_symbols {
        if o.is_import(f) {
            continue;
        }
        let sym = &o.symbols[si as usize];
        let Some(entry) = o.symbol_name(sym) else {
            continue;
        };
        let Some(plain) = entry.strip_suffix(INTERNAL_ENTRY_SUFFIX) else {
            continue;
        };
        match forwarding_entry(o, si, f, plain) {
            Ok(stores) => {
                ev.forwarding_entries += 1;
                push(
                    checks,
                    format!("C-form entry `{plain}` forwards to `{entry}`"),
                    true,
                    format!("stores {stores:?}"),
                );
                layouts.insert(plain.to_string(), stores);
            }
            Err(why) => push(
                checks,
                format!("C-form entry `{plain}` forwards to `{entry}`"),
                false,
                why,
            ),
        }
    }
    ev.checks = std::mem::take(checks);
    (ev, layouts)
}

/// Check the C-form entry named `plain` of internal entry `f` (symbol
/// `entry_sym`): one defined, strong, hidden, unexported function symbol of
/// that name, of type `(i32, P...) -> ()` for internal type `(P...) ->
/// (R...)`, whose body is exactly
///
/// ```text
/// local.get 1 .. local.get n          ;; the parameters after `sret`
/// call <f>                            ;; relocated to `entry_sym`
/// local.set n+k .. local.set n+1      ;; one declared local per result
/// (local.get 0  local.get n+1+j  <store of R[j]'s value type>)  j = 0..k
/// end
/// ```
///
/// with the stored byte ranges pairwise disjoint. Returns the stores.
fn forwarding_entry(
    o: &DecodedObject,
    entry_sym: u32,
    f: u32,
    plain: &str,
) -> Result<Vec<ForwardedStore>, String> {
    let defs: Vec<&ObjectSymbol> = o
        .symbols
        .iter()
        .filter(|s| {
            s.kind == SYMTAB_FUNCTION
                && s.flags & SYM_UNDEFINED == 0
                && s.name.as_deref() == Some(plain)
        })
        .collect();
    let [sym] = defs.as_slice() else {
        return Err(format!(
            "{} defined function symbols are named so",
            defs.len()
        ));
    };
    if sym.flags & (SYM_WEAK | SYM_LOCAL | SYM_EXPORTED) != 0 || sym.flags & SYM_HIDDEN == 0 {
        return Err(format!("its symbol flags are 0x{:x}", sym.flags));
    }
    let c = sym.index.ok_or("no function index")?;
    if o.is_import(c) {
        return Err("it is imported".to_string());
    }
    let inner = o.type_of_func(f).ok_or("the internal entry has no type")?;
    let outer = o.type_of_func(c).ok_or("it has no type")?;
    if outer.params.first() != Some(&VT_I32)
        || outer.params[1..] != inner.params[..]
        || !outer.results.is_empty()
    {
        return Err(format!(
            "type {outer:?} is not (i32, P...) -> () of {inner:?}"
        ));
    }
    let body = &o.bodies[(c as usize) - o.func_imports.len()];
    if body.locals != inner.results {
        return Err(format!(
            "declared locals {:?}, results {:?}",
            body.locals, inner.results
        ));
    }
    let insts = decode_insts(&o.code[body.code_start..body.end]).map_err(|e| e.to_string())?;
    let n = inner.params.len() as u32;
    let k = inner.results.len() as u32;
    let mut it = insts.iter();
    let mut next = |what: &str| it.next().ok_or_else(|| format!("ends before {what}"));
    let local = |i: &DecodedInst, op: u8, idx: u32| i.op == op && i.imm == Imm::Idx(idx);
    for p in 1..=n {
        let i = next("a parameter")?;
        if !local(i, OP_LOCAL_GET, p) {
            return Err(format!("parameter {p} is not forwarded in order: {i:?}"));
        }
    }
    let call = next("the call")?;
    if !local(call, OP_CALL, f) {
        return Err(format!("does not call the internal entry: {call:?}"));
    }
    let imm = body.code_start + call.at + 1;
    let relocated = o.relocs.iter().any(|r| {
        Some(r.section) == o.code_section
            && r.offset as usize == imm
            && r.ty == R_FUNCTION_INDEX_LEB
            && r.index == entry_sym
    });
    if !relocated {
        return Err("its call is not relocated to the internal entry's symbol".to_string());
    }
    for j in (0..k).rev() {
        let i = next("a result")?;
        if !local(i, OP_LOCAL_SET, n + 1 + j) {
            return Err(format!("result {j} is not taken in order: {i:?}"));
        }
    }
    let mut stores: Vec<ForwardedStore> = Vec::new();
    for j in 0..k {
        let a = next("the sret address")?;
        let v = next("a stored result")?;
        let st = next("a store")?;
        if !local(a, OP_LOCAL_GET, 0) || !local(v, OP_LOCAL_GET, n + 1 + j) {
            return Err(format!("store {j} does not write result {j} through sret"));
        }
        let (width, vt) =
            store_shape(st.op).ok_or_else(|| format!("store {j} is not a store: {st:?}"))?;
        let Imm::Memarg { align, offset } = st.imm else {
            return Err(format!("store {j} has no memarg"));
        };
        if vt != inner.results[j as usize] || (1u32 << align.min(31)) > width {
            return Err(format!(
                "store {j} ({st:?}) does not store result {j} of type 0x{:02x}",
                inner.results[j as usize]
            ));
        }
        let end = offset.checked_add(width).ok_or("store offset overflows")?;
        if let Some(prev) = stores
            .iter()
            .find(|s| offset < s.offset + s.width && s.offset < end)
        {
            return Err(format!(
                "store {j} at {offset} overlaps the store at {}",
                prev.offset
            ));
        }
        stores.push(ForwardedStore { offset, width });
    }
    let last = next("the end")?;
    if last.op != OP_END || it.next().is_some() {
        return Err("the body does not end after the stores".to_string());
    }
    Ok(stores)
}

/// The gate and the return binding over one object ([`gate`]).
pub fn object_evidence(bytes: &[u8]) -> Result<InternalAbiEvidence, String> {
    let o = decode_object(bytes)?;
    Ok(gate(&o).0)
}

/// Refuse an object whose ABI boundary or return binding does not hold
/// (module docs); the evidence when it does.
pub fn check_object(bytes: &[u8]) -> Result<InternalAbiEvidence, String> {
    let ev = object_evidence(bytes)?;
    match ev.first_failure() {
        None => Ok(ev),
        Some(why) => Err(why),
    }
}

// ===========================================================================
// The source binding
// ===========================================================================

/// The value-type byte of a scalar trust-ir type.
fn scalar_byte(ty: &Ty) -> Option<u8> {
    crate::wasm_abi_proofs::valtype_byte(ty).ok()
}

/// Size and alignment in bytes of `ty` under trust-ir's own layout table.
fn layout(module: &Module, ty: &Ty) -> Result<(u32, u32), String> {
    let shape = module
        .ty_layout_shape(ty)
        .map_err(|e| format!("{ty:?} has no layout: {e:?}"))?;
    let size = shape
        .size_bytes()
        .and_then(|s| u32::try_from(s).ok())
        .ok_or_else(|| format!("{ty:?} has no byte size"))?;
    let align = shape
        .align_bits
        .and_then(|a| u32::try_from(a / 8).ok())
        .filter(|a| a.is_power_of_two())
        .ok_or_else(|| format!("{ty:?} has no byte alignment"))?;
    Ok((size, align))
}

/// The internal results and the C-form stores trust-ir intends for
/// `returns`: a zero-sized result is nothing, a 128-bit integer is two
/// `i64`s stored 8 bytes apart, a scalar is its value type stored as wide as
/// its size; each valued result sits at the running offset rounded up to its
/// alignment.
fn intended(module: &Module, returns: &[Ty]) -> Result<(Vec<u8>, Vec<ForwardedStore>), String> {
    let mut results = Vec::new();
    let mut stores = Vec::new();
    let mut cursor = 0u32;
    for ty in returns {
        let (size, align) = layout(module, ty)?;
        if size == 0 {
            continue;
        }
        cursor = cursor
            .checked_next_multiple_of(align)
            .ok_or("sret offset overflows")?;
        if matches!(ty, Ty::I128 | Ty::U128) {
            results.extend([VT_I64, VT_I64]);
            stores.push(ForwardedStore {
                offset: cursor,
                width: 8,
            });
            stores.push(ForwardedStore {
                offset: cursor + 8,
                width: 8,
            });
        } else {
            let b = scalar_byte(ty)
                .ok_or_else(|| format!("result type {ty:?} has no internal-ABI lane"))?;
            results.push(b);
            stores.push(ForwardedStore {
                offset: cursor,
                width: size,
            });
        }
        cursor = cursor.checked_add(size).ok_or("sret offset overflows")?;
    }
    Ok((results, stores))
}

/// The gate, the return binding, and the source binding against `module`,
/// the trust-ir module the object was lowered from: every function of
/// `module` whose internal entry the object names returns the results its
/// signature intends, and its C-form entry, when defined here, stores them
/// at their BasicCABI offsets and widths; and every internal entry the
/// object names belongs to a function of `module`.
pub fn check_object_against_module(
    bytes: &[u8],
    module: &Module,
) -> Result<InternalAbiEvidence, String> {
    let o = decode_object(bytes)?;
    let (mut ev, layouts) = gate(&o);
    let mut named: BTreeMap<String, u32> = BTreeMap::new();
    for f in (0..o.func_count()).filter(|&f| o.type_of_func(f).is_some_and(|t| t.results.len() > 1))
    {
        for (_, s) in o.func_symbols(f) {
            if let Some(n) = o.symbol_name(s) {
                named.insert(n, f);
            }
        }
    }
    for (name, f) in &named {
        let plain = name.strip_suffix(INTERNAL_ENTRY_SUFFIX);
        let func = plain.and_then(|p| module.function_by_name(p));
        let Some(func) = func else {
            push(
                &mut ev.checks,
                format!("internal entry `{name}` belongs to a function of the module"),
                false,
                "no trust-ir function of that name".to_string(),
            );
            continue;
        };
        let check = (|| -> Result<String, String> {
            let ft = module
                .func_type(func.ty)
                .ok_or("the function has no signature")?;
            let (results, stores) = intended(module, &ft.returns)?;
            let got = o.type_of_func(*f).ok_or("no type")?;
            if got.results != results {
                return Err(format!(
                    "results {:?}, the signature intends {results:?}",
                    got.results
                ));
            }
            match plain.and_then(|p| layouts.get(p)) {
                Some(have) if *have != stores => Err(format!(
                    "the C-form entry stores {have:?}, the BasicCABI layout is {stores:?}"
                )),
                Some(_) => Ok(format!("results {results:?}, stores {stores:?}")),
                None if o.is_import(*f) => Ok(format!("imported; results {results:?}")),
                None => Err("no checked C-form entry".to_string()),
            }
        })();
        let ok = check.is_ok();
        push(
            &mut ev.checks,
            format!("internal entry `{name}` matches the trust-ir signature"),
            ok,
            check.unwrap_or_else(|e| e),
        );
    }
    match ev.first_failure() {
        None => Ok(ev),
        Some(why) => Err(why),
    }
}

// ===========================================================================
// The link binding
// ===========================================================================

/// What [`check_link`] established.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InternalAbiLinkEvidence {
    /// Internal entries defined across the objects.
    pub entries: usize,
    /// Imports of them across the objects.
    pub imports: usize,
}

/// Check every object ([`check_object`]) and their agreement: each internal
/// entry any of them names is defined by exactly one of them, and every
/// object that imports it imports it at the definition's type.
pub fn check_link(objects: &[&[u8]]) -> Result<InternalAbiLinkEvidence, String> {
    /// The defining objects of one internal entry, and the (object, defines,
    /// type) of every symbol naming it.
    type EntrySites = (Vec<usize>, Vec<(usize, bool, DecodedFuncType)>);
    let mut seen: BTreeMap<String, EntrySites> = BTreeMap::new();
    for (k, bytes) in objects.iter().enumerate() {
        check_object(bytes).map_err(|e| format!("object {k}: {e}"))?;
        let o = decode_object(bytes)?;
        for s in &o.symbols {
            let (Some(name), Some(f)) = (o.symbol_name(s), s.index) else {
                continue;
            };
            if s.kind != SYMTAB_FUNCTION || !is_internal_entry_name(&name) {
                continue;
            }
            let ty = o.type_of_func(f).cloned().unwrap_or_default();
            let entry = seen.entry(name).or_default();
            let defined = s.flags & SYM_UNDEFINED == 0;
            if defined {
                entry.0.push(k);
            }
            entry.1.push((k, defined, ty));
        }
    }
    let mut ev = InternalAbiLinkEvidence::default();
    for (name, (defs, namings)) in &seen {
        let [def] = defs.as_slice() else {
            return Err(format!(
                "internal entry `{name}` is defined by {} objects ({defs:?})",
                defs.len()
            ));
        };
        let def_ty = namings
            .iter()
            .find(|(k, d, _)| k == def && *d)
            .map(|(_, _, t)| t.clone())
            .unwrap_or_default();
        for (k, defined, ty) in namings {
            if !defined {
                if *ty != def_ty {
                    return Err(format!(
                        "object {k} imports `{name}` as {ty:?}; object {def} defines it as \
                         {def_ty:?}"
                    ));
                }
                ev.imports += 1;
            }
        }
        ev.entries += 1;
    }
    Ok(ev)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn internal_entry_names_carry_a_crate_tag_and_the_suffix() {
        assert!(is_internal_entry_name(
            "f.tcg.crate.0123456789abcdef.tcg.mv"
        ));
        for bad in [
            "f.tcg.crate.0123456789abcdef",
            ".tcg.crate.0123456789abcdef.tcg.mv",
            "f.tcg.crate.0123456789ABCDEF.tcg.mv",
            "f.tcg.crate.0123456789abcde.tcg.mv",
            "f.tcg.mv",
        ] {
            assert!(!is_internal_entry_name(bad), "{bad}");
        }
    }

    #[test]
    fn unknown_relocation_types_fail_closed() {
        assert!(reloc_has_addend(27).is_err());
        assert_eq!(reloc_has_addend(R_FUNCTION_INDEX_LEB), Ok(false));
        assert_eq!(reloc_has_addend(5), Ok(true));
    }
}
