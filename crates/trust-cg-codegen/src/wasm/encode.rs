// trust-cg-codegen/wasm/encode.rs - WebAssembly binary module encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Hand-rolled WebAssembly binary (`.wasm`) module encoder.
//!
//! trust-cg owns its emission — it hand-writes ELF/Mach-O/COFF, and it
//! hand-writes wasm too (no `wasm-encoder` dependency), so the bytes that
//! execute are inside the verification scope. This module is the wasm analogue
//! of the `elf` / `macho` / `coff` writers: it turns a structured module
//! description into the binary module format. It is intentionally
//! IR-agnostic — the trust-ir → wasm lowering (relooper, linear memory) builds
//! the [`WasmModule`] and calls [`WasmModule::finish`].
//!
//! Slice 0 surface: function types, functions, function exports, and code
//! bodies for straight-line integer functions. Control flow, memory, calls,
//! and imports are added in later slices.
//!
//! Reference: WebAssembly Core Specification, "Binary Format".

/// Append an unsigned LEB128 encoding of `value` to `buf`.
pub fn write_uleb128(buf: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Append a signed LEB128 encoding of `value` to `buf`.
pub fn write_sleb128(buf: &mut Vec<u8>, mut value: i64) {
    loop {
        let byte = (value & 0x7f) as u8;
        // Arithmetic shift keeps the sign bit replicated.
        value >>= 7;
        let sign_bit_set = byte & 0x40 != 0;
        let done = (value == 0 && !sign_bit_set) || (value == -1 && sign_bit_set);
        if done {
            buf.push(byte);
            break;
        }
        buf.push(byte | 0x80);
    }
}

/// WebAssembly value types (the numeric types Slice 0 needs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

impl ValType {
    /// The single-byte encoding of this value type.
    pub fn code(self) -> u8 {
        match self {
            ValType::I32 => 0x7f,
            ValType::I64 => 0x7e,
            ValType::F32 => 0x7d,
            ValType::F64 => 0x7c,
        }
    }
}

/// A function type: parameters and results.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// A function body: local declarations (run-length encoded) plus the encoded
/// instruction stream. The trailing `end` opcode is appended by the encoder, so
/// callers provide instructions without it.
#[derive(Debug, Clone, Default)]
pub struct FuncBody {
    /// Run-length local declarations: `(count, type)`.
    pub locals: Vec<(u32, ValType)>,
    /// Encoded instruction bytes (no trailing `end`).
    pub code: Vec<u8>,
}

/// Export descriptor kind. Slice 0 only exports functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportKind {
    Func,
}

impl ExportKind {
    fn code(self) -> u8 {
        match self {
            ExportKind::Func => 0x00,
        }
    }
}

#[derive(Debug, Clone)]
struct Export {
    name: String,
    kind: ExportKind,
    index: u32,
}

/// A WebAssembly module under construction.
/// A module-level global: value type, mutability, and an `i*.const` initializer.
#[derive(Debug, Clone)]
struct GlobalDef {
    ty: ValType,
    mutable: bool,
    init: i64,
}

#[derive(Debug, Clone, Default)]
pub struct WasmModule {
    types: Vec<FuncType>,
    /// Type index for each defined function (parallel to `bodies`).
    func_types: Vec<u32>,
    bodies: Vec<FuncBody>,
    exports: Vec<Export>,
    /// Linear memory minimum size in 64KiB pages, if the module uses memory.
    memory_min_pages: Option<u32>,
    globals: Vec<GlobalDef>,
    /// If set, a `funcref` table is emitted holding functions `0..table_size`
    /// at element index `i = funcidx i` (for `call_indirect` / function ptrs).
    table_size: Option<u32>,
}

impl WasmModule {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a function type, returning its type index.
    pub fn add_type(&mut self, ty: FuncType) -> u32 {
        if let Some(idx) = self.types.iter().position(|t| *t == ty) {
            return idx as u32;
        }
        let idx = self.types.len() as u32;
        self.types.push(ty);
        idx
    }

    /// Define a function of the given type with the given body. Returns the new
    /// function index.
    pub fn add_function(&mut self, type_idx: u32, body: FuncBody) -> u32 {
        let idx = self.func_types.len() as u32;
        self.func_types.push(type_idx);
        self.bodies.push(body);
        idx
    }

    /// Declare a linear memory of at least `min_pages` 64KiB pages. Idempotent:
    /// the maximum requested page count wins.
    pub fn ensure_memory(&mut self, min_pages: u32) {
        self.memory_min_pages = Some(self.memory_min_pages.unwrap_or(0).max(min_pages));
    }

    /// Add a module global with an integer-constant initializer. Returns its
    /// global index.
    pub fn add_global(&mut self, ty: ValType, mutable: bool, init: i64) -> u32 {
        let idx = self.globals.len() as u32;
        self.globals.push(GlobalDef { ty, mutable, init });
        idx
    }

    /// Emit a `funcref` table holding functions `0..count` at element index
    /// equal to their function index (so a function pointer is its funcidx).
    pub fn set_func_table(&mut self, count: u32) {
        self.table_size = Some(count);
    }

    /// Export a defined function under `name`.
    pub fn export_func(&mut self, name: &str, func_idx: u32) {
        self.exports.push(Export {
            name: name.to_string(),
            kind: ExportKind::Func,
            index: func_idx,
        });
    }

    /// Serialize the module to its binary `.wasm` representation.
    pub fn finish(&self) -> Vec<u8> {
        let mut out = Vec::new();
        // Magic "\0asm" + version 1.
        out.extend_from_slice(&[0x00, 0x61, 0x73, 0x6d]);
        out.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);

        // Type section (id 1).
        if !self.types.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.types.len() as u64);
            for ty in &self.types {
                body.push(0x60); // func type tag
                write_uleb128(&mut body, ty.params.len() as u64);
                body.extend(ty.params.iter().map(|p| p.code()));
                write_uleb128(&mut body, ty.results.len() as u64);
                body.extend(ty.results.iter().map(|r| r.code()));
            }
            push_section(&mut out, 1, &body);
        }

        // Function section (id 3): declared functions and their type indices.
        if !self.func_types.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.func_types.len() as u64);
            for type_idx in &self.func_types {
                write_uleb128(&mut body, u64::from(*type_idx));
            }
            push_section(&mut out, 3, &body);
        }

        // Table section (id 4): one funcref table sized to hold all functions.
        if let Some(count) = self.table_size {
            let mut body = Vec::new();
            write_uleb128(&mut body, 1); // one table
            body.push(0x70); // funcref element type
            body.push(0x00); // limits flag: min only
            write_uleb128(&mut body, u64::from(count));
            push_section(&mut out, 4, &body);
        }

        // Memory section (id 5): a single linear memory with a min size.
        if let Some(min_pages) = self.memory_min_pages {
            let mut body = Vec::new();
            write_uleb128(&mut body, 1); // one memory
            body.push(0x00); // limits flag: min only
            write_uleb128(&mut body, u64::from(min_pages));
            push_section(&mut out, 5, &body);
        }

        // Global section (id 6).
        if !self.globals.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.globals.len() as u64);
            for g in &self.globals {
                body.push(g.ty.code());
                body.push(if g.mutable { 0x01 } else { 0x00 });
                // Constant init expression.
                match g.ty {
                    ValType::I64 => {
                        body.push(op::I64_CONST);
                        write_sleb128(&mut body, g.init);
                    }
                    _ => {
                        body.push(op::I32_CONST);
                        write_sleb128(&mut body, g.init);
                    }
                }
                body.push(op::END);
            }
            push_section(&mut out, 6, &body);
        }

        // Export section (id 7).
        if !self.exports.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.exports.len() as u64);
            for export in &self.exports {
                write_uleb128(&mut body, export.name.len() as u64);
                body.extend_from_slice(export.name.as_bytes());
                body.push(export.kind.code());
                write_uleb128(&mut body, u64::from(export.index));
            }
            push_section(&mut out, 7, &body);
        }

        // Element section (id 9): an active segment filling table 0 at offset 0
        // with functions 0..count, so funcidx == table element index.
        if let Some(count) = self.table_size {
            let mut body = Vec::new();
            write_uleb128(&mut body, 1); // one element segment
            write_uleb128(&mut body, 0); // segment flags: active, table 0
            // offset init expr: i32.const 0; end
            body.push(op::I32_CONST);
            write_sleb128(&mut body, 0);
            body.push(op::END);
            write_uleb128(&mut body, u64::from(count)); // number of func indices
            for i in 0..count {
                write_uleb128(&mut body, u64::from(i));
            }
            push_section(&mut out, 9, &body);
        }

        // Code section (id 10): one entry per defined function.
        if !self.bodies.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.bodies.len() as u64);
            for func in &self.bodies {
                let mut entry = Vec::new();
                write_uleb128(&mut entry, func.locals.len() as u64);
                for (count, ty) in &func.locals {
                    write_uleb128(&mut entry, u64::from(*count));
                    entry.push(ty.code());
                }
                entry.extend_from_slice(&func.code);
                entry.push(op::END);
                // Each code entry is length-prefixed.
                write_uleb128(&mut body, entry.len() as u64);
                body.extend_from_slice(&entry);
            }
            push_section(&mut out, 10, &body);
        }

        out
    }
}

/// Write a section: id byte, ULEB128 length prefix, then the body.
fn push_section(out: &mut Vec<u8>, id: u8, body: &[u8]) {
    out.push(id);
    write_uleb128(out, body.len() as u64);
    out.extend_from_slice(body);
}

/// WebAssembly instruction opcodes used by the Slice 0 emitter. Extended as
/// later slices add control flow, memory, and calls.
pub mod op {
    // Control flow.
    pub const UNREACHABLE: u8 = 0x00;
    pub const BLOCK: u8 = 0x02;
    pub const LOOP: u8 = 0x03;
    pub const IF: u8 = 0x04;
    pub const ELSE: u8 = 0x05;
    pub const END: u8 = 0x0b;
    pub const BR: u8 = 0x0c;
    pub const BR_IF: u8 = 0x0d;
    pub const BR_TABLE: u8 = 0x0e;
    pub const RETURN: u8 = 0x0f;
    pub const CALL: u8 = 0x10;
    pub const CALL_INDIRECT: u8 = 0x11;
    pub const DROP: u8 = 0x1a;
    /// `blocktype` byte for a block/loop/if with no parameters and no results.
    pub const BLOCKTYPE_VOID: u8 = 0x40;

    // Variables.
    pub const LOCAL_GET: u8 = 0x20;
    pub const LOCAL_SET: u8 = 0x21;
    pub const LOCAL_TEE: u8 = 0x22;
    pub const GLOBAL_GET: u8 = 0x23;
    pub const GLOBAL_SET: u8 = 0x24;

    // Linear memory load/store (each followed by a memarg: align_exp, offset).
    pub const I32_LOAD: u8 = 0x28;
    pub const I64_LOAD: u8 = 0x29;
    pub const I32_STORE: u8 = 0x36;
    pub const I64_STORE: u8 = 0x37;

    // Constants.
    pub const I32_CONST: u8 = 0x41;
    pub const I64_CONST: u8 = 0x42;

    // i32 comparisons (result i32).
    pub const I32_EQ: u8 = 0x46;
    pub const I32_NE: u8 = 0x47;
    pub const I32_LT_S: u8 = 0x48;
    pub const I32_LT_U: u8 = 0x49;
    pub const I32_GT_S: u8 = 0x4a;
    pub const I32_GT_U: u8 = 0x4b;
    pub const I32_LE_S: u8 = 0x4c;
    pub const I32_LE_U: u8 = 0x4d;
    pub const I32_GE_S: u8 = 0x4e;
    pub const I32_GE_U: u8 = 0x4f;

    // i64 comparisons (result i32).
    pub const I64_EQ: u8 = 0x51;
    pub const I64_NE: u8 = 0x52;
    pub const I64_LT_S: u8 = 0x53;
    pub const I64_LT_U: u8 = 0x54;
    pub const I64_GT_S: u8 = 0x55;
    pub const I64_GT_U: u8 = 0x56;
    pub const I64_LE_S: u8 = 0x57;
    pub const I64_LE_U: u8 = 0x58;
    pub const I64_GE_S: u8 = 0x59;
    pub const I64_GE_U: u8 = 0x5a;

    // i32/i64 arithmetic.
    pub const I32_ADD: u8 = 0x6a;
    pub const I32_SUB: u8 = 0x6b;
    pub const I32_MUL: u8 = 0x6c;
    pub const I32_DIV_S: u8 = 0x6d;
    pub const I32_DIV_U: u8 = 0x6e;
    pub const I32_REM_S: u8 = 0x6f;
    pub const I32_REM_U: u8 = 0x70;
    pub const I64_ADD: u8 = 0x7c;
    pub const I64_SUB: u8 = 0x7d;
    pub const I64_MUL: u8 = 0x7e;
    pub const I64_DIV_S: u8 = 0x7f;
    pub const I64_DIV_U: u8 = 0x80;
    pub const I64_REM_S: u8 = 0x81;
    pub const I64_REM_U: u8 = 0x82;

    // i32/i64 bitwise and shifts (wasm masks the shift amount mod width).
    pub const I32_AND: u8 = 0x71;
    pub const I32_OR: u8 = 0x72;
    pub const I32_XOR: u8 = 0x73;
    pub const I32_SHL: u8 = 0x74;
    pub const I32_SHR_S: u8 = 0x75;
    pub const I32_SHR_U: u8 = 0x76;
    pub const I64_AND: u8 = 0x83;
    pub const I64_OR: u8 = 0x84;
    pub const I64_XOR: u8 = 0x85;
    pub const I64_SHL: u8 = 0x86;
    pub const I64_SHR_S: u8 = 0x87;
    pub const I64_SHR_U: u8 = 0x88;

    // f32/f64 arithmetic (IEEE-754, round-to-nearest-ties-to-even).
    pub const F32_ADD: u8 = 0x92;
    pub const F32_SUB: u8 = 0x93;
    pub const F32_MUL: u8 = 0x94;
    pub const F32_DIV: u8 = 0x95;
    pub const F64_ADD: u8 = 0xa0;
    pub const F64_SUB: u8 = 0xa1;
    pub const F64_MUL: u8 = 0xa2;
    pub const F64_DIV: u8 = 0xa3;

    // Integer unary: popcount (i32/i64). (wasm has no integer neg/not — those
    // lower to `0 - x` / `x ^ -1` in the backend.)
    pub const I32_POPCNT: u8 = 0x69;
    pub const I64_POPCNT: u8 = 0x7b;

    // f32/f64 unary (IEEE-754).
    pub const F32_ABS: u8 = 0x8b;
    pub const F32_NEG: u8 = 0x8c;
    pub const F32_CEIL: u8 = 0x8d;
    pub const F32_FLOOR: u8 = 0x8e;
    pub const F32_TRUNC: u8 = 0x8f;
    pub const F32_SQRT: u8 = 0x91;
    pub const F64_ABS: u8 = 0x99;
    pub const F64_NEG: u8 = 0x9a;
    pub const F64_CEIL: u8 = 0x9b;
    pub const F64_FLOOR: u8 = 0x9c;
    pub const F64_TRUNC: u8 = 0x9d;
    pub const F64_SQRT: u8 = 0x9f;

    // f32/f64 comparisons → i32 (0/1). eq/lt/gt/le/ge are ORDERED (false on
    // NaN); ne is UNORDERED (true on NaN). Composite predicates are built from
    // these + i32.or / isnan(x)=f.ne(x,x).
    pub const F32_EQ: u8 = 0x5b;
    pub const F32_NE: u8 = 0x5c;
    pub const F32_LT: u8 = 0x5d;
    pub const F32_GT: u8 = 0x5e;
    pub const F32_LE: u8 = 0x5f;
    pub const F32_GE: u8 = 0x60;
    pub const F64_EQ: u8 = 0x61;
    pub const F64_NE: u8 = 0x62;
    pub const F64_LT: u8 = 0x63;
    pub const F64_GT: u8 = 0x64;
    pub const F64_LE: u8 = 0x65;
    pub const F64_GE: u8 = 0x66;

    // Conversions. Integer width:
    pub const I32_WRAP_I64: u8 = 0xa7;
    pub const I64_EXTEND_I32_S: u8 = 0xac;
    pub const I64_EXTEND_I32_U: u8 = 0xad;
    // Float width:
    pub const F32_DEMOTE_F64: u8 = 0xb6;
    pub const F64_PROMOTE_F32: u8 = 0xbb;
    // int → float:
    pub const F32_CONVERT_I32_S: u8 = 0xb2;
    pub const F32_CONVERT_I32_U: u8 = 0xb3;
    pub const F32_CONVERT_I64_S: u8 = 0xb4;
    pub const F32_CONVERT_I64_U: u8 = 0xb5;
    pub const F64_CONVERT_I32_S: u8 = 0xb7;
    pub const F64_CONVERT_I32_U: u8 = 0xb8;
    pub const F64_CONVERT_I64_S: u8 = 0xb9;
    pub const F64_CONVERT_I64_U: u8 = 0xba;
    // reinterpret (bitcast):
    pub const I32_REINTERPRET_F32: u8 = 0xbc;
    pub const I64_REINTERPRET_F64: u8 = 0xbd;
    pub const F32_REINTERPRET_I32: u8 = 0xbe;
    pub const F64_REINTERPRET_I64: u8 = 0xbf;
    // Saturating float → int (the 0xfc prefix + index; matches Rust `as`, which
    // saturates instead of trapping). Stored as the index after 0xfc.
    pub const FC_PREFIX: u8 = 0xfc;
    pub const I32_TRUNC_SAT_F32_S: u32 = 0;
    pub const I32_TRUNC_SAT_F32_U: u32 = 1;
    pub const I32_TRUNC_SAT_F64_S: u32 = 2;
    pub const I32_TRUNC_SAT_F64_U: u32 = 3;
    pub const I64_TRUNC_SAT_F32_S: u32 = 4;
    pub const I64_TRUNC_SAT_F32_U: u32 = 5;
    pub const I64_TRUNC_SAT_F64_S: u32 = 6;
    pub const I64_TRUNC_SAT_F64_U: u32 = 7;
}

/// Append a `local.get $idx` instruction to an instruction buffer.
pub fn emit_local_get(code: &mut Vec<u8>, idx: u32) {
    code.push(op::LOCAL_GET);
    write_uleb128(code, u64::from(idx));
}

/// Append an `i32.const $value` instruction to an instruction buffer.
pub fn emit_i32_const(code: &mut Vec<u8>, value: i32) {
    code.push(op::I32_CONST);
    write_sleb128(code, i64::from(value));
}

/// Append a load/store `memarg` immediate: alignment exponent (log2 of the
/// alignment in bytes) and a static byte offset, both ULEB128.
pub fn emit_memarg(code: &mut Vec<u8>, align_exponent: u32, offset: u32) {
    write_uleb128(code, u64::from(align_exponent));
    write_uleb128(code, u64::from(offset));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uleb128_examples() {
        let cases: &[(u64, &[u8])] = &[
            (0, &[0x00]),
            (1, &[0x01]),
            (127, &[0x7f]),
            (128, &[0x80, 0x01]),
            (300, &[0xac, 0x02]),
            (624485, &[0xe5, 0x8e, 0x26]),
        ];
        for (value, expected) in cases {
            let mut buf = Vec::new();
            write_uleb128(&mut buf, *value);
            assert_eq!(&buf, expected, "uleb128({value})");
        }
    }

    #[test]
    fn sleb128_examples() {
        let cases: &[(i64, &[u8])] = &[
            (0, &[0x00]),
            (1, &[0x01]),
            (-1, &[0x7f]),
            (63, &[0x3f]),
            (64, &[0xc0, 0x00]),
            (-64, &[0x40]),
            (-65, &[0xbf, 0x7f]),
        ];
        for (value, expected) in cases {
            let mut buf = Vec::new();
            write_sleb128(&mut buf, *value);
            assert_eq!(&buf, expected, "sleb128({value})");
        }
    }

    /// The canonical minimal module:
    /// `(module (func (export "add") (param i32 i32) (result i32)
    ///    local.get 0 local.get 1 i32.add))`
    /// — its 41-byte binary encoding is a fixed reference point. If the encoder
    /// drifts, this golden catches it.
    #[test]
    fn emits_canonical_add_module() {
        let mut module = WasmModule::new();
        let ty = module.add_type(FuncType {
            params: vec![ValType::I32, ValType::I32],
            results: vec![ValType::I32],
        });
        let mut code = Vec::new();
        emit_local_get(&mut code, 0);
        emit_local_get(&mut code, 1);
        code.push(op::I32_ADD);
        let func = module.add_function(
            ty,
            FuncBody {
                locals: vec![],
                code,
            },
        );
        module.export_func("add", func);

        let bytes = module.finish();

        #[rustfmt::skip]
        let golden: &[u8] = &[
            // magic + version
            0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
            // type section: 1 type, (i32,i32)->i32
            0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f,
            // function section: func 0 has type 0
            0x03, 0x02, 0x01, 0x00,
            // export section: "add" -> func 0
            0x07, 0x07, 0x01, 0x03, 0x61, 0x64, 0x64, 0x00, 0x00,
            // code section: body = local.get 0; local.get 1; i32.add; end
            0x0a, 0x09, 0x01, 0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0x6a, 0x0b,
        ];
        assert_eq!(bytes, golden, "canonical add module byte mismatch");
        assert_eq!(bytes.len(), 41);
    }
}
