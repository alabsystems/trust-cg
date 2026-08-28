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
//! bodies for straight-line integer functions. Control flow, memory and calls
//! followed.
//!
//! **P2 (the import/index-space slice)** adds the surface an *island* needs to
//! live beside a host module: function/memory/global **imports** (section id
//! 2), an explicit [`WasmMemoryPolicy`] (own the memory, import the host's, or
//! have none), and global initializers that read an imported global
//! ([`GlobalInit::ImportedGlobal`]). The load-bearing rule it enforces is the
//! wasm **index space**: imported functions occupy indices `0..N` and defined
//! functions follow, and likewise for globals — so every index the encoder
//! hands out ([`WasmModule::add_function`], [`WasmModule::add_global`]) is
//! import-shifted, the funcref element segment is derived from
//! [`WasmModule::func_count`] rather than from a caller's arithmetic, and
//! declaring an import *after* a definition of the same kind is refused
//! ([`WasmEncodeError::ImportAfterDefinition`]) instead of silently shifting
//! indices that were already issued.
//!
//! **P3 (the value-domain slice)** adds the rest of the memory instruction
//! table — sub-word integer loads/stores (`i32.load8_u` … `i64.store32`) and
//! `f32`/`f64` loads/stores — the **data section** (id 11) so constant tables
//! live in memory instead of in code, and `memory.size` / `memory.grow`. A data
//! segment is an *active* one: it is copied into memory 0 at instantiation, so
//! under [`WasmMemoryPolicy::Imported`] it writes into the HOST's memory at an
//! address the module chose. That is a contract term, not an encoding detail,
//! so the encoder refuses it ([`WasmEncodeError::DataIntoImportedMemory`])
//! unless the host grant is recorded
//! ([`WasmModule::grant_imported_memory_data`]).
//!
//! Reference: WebAssembly Core Specification, "Binary Format".

use std::fmt;

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

/// Export descriptor kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportKind {
    Func,
    Memory,
    Global,
}

impl ExportKind {
    fn code(self) -> u8 {
        match self {
            ExportKind::Func => 0x00,
            ExportKind::Memory => 0x02,
            ExportKind::Global => 0x03,
        }
    }
}

#[derive(Debug, Clone)]
struct Export {
    name: String,
    kind: ExportKind,
    index: u32,
}

/// Bytes in one WebAssembly linear-memory page.
pub const WASM_PAGE_BYTES: u32 = 65536;

/// Where a module's linear memory comes from — the memory half of the host
/// contract an island negotiates rather than assumes.
///
/// The closed-module default is [`WasmMemoryPolicy::Owned`] with one page and
/// no export, which is exactly the behavior the backend had before P2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmMemoryPolicy {
    /// The module has NO linear memory: it neither defines nor imports one.
    /// A module that turns out to need memory is refused
    /// ([`WasmEncodeError::NoMemory`]) rather than emitted with dangling
    /// loads/stores.
    Absent,
    /// The module DEFINES its own memory of `pages` 64KiB pages, optionally
    /// exporting it under `export` so a host can read the island's results.
    Owned { pages: u32, export: Option<String> },
    /// The module IMPORTS the host's memory as `(module, name)` and defines
    /// none — the island lives *inside* the host's address space, so it may
    /// touch only the region the host negotiated with it (see
    /// `super::lower::WasmStackPolicy::HostBase`).
    ///
    /// The declared limits are `min 0`, no maximum: the island makes no demand
    /// on the host memory's size (it is told where its region is), and those
    /// limits match every host memory.
    Imported { module: String, name: String },
}

/// The closed-module linear-memory size: one 64KiB page, with the shadow stack
/// growing down from its top. Plenty for the scalar frames the backend
/// produces today.
pub const DEFAULT_OWNED_PAGES: u32 = 1;

impl Default for WasmMemoryPolicy {
    fn default() -> Self {
        WasmMemoryPolicy::Owned {
            pages: DEFAULT_OWNED_PAGES,
            export: None,
        }
    }
}

/// The initializer (constant expression) of a defined global.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobalInit {
    I32(i32),
    I64(i64),
    /// `global.get $idx` — a *constant expression* only when `$idx` names an
    /// IMPORTED IMMUTABLE global (WebAssembly Core Specification, "Constant
    /// Expressions"). This is how a host publishes an address to an island:
    /// the host allocates the island's region, exports its top as an immutable
    /// `i32` global, and the island seeds its shadow stack pointer from it.
    ImportedGlobal(u32),
}

/// Errors from BUILDING a [`WasmModule`]: structural guards that fail closed
/// instead of emitting a module whose indices point at the wrong entity.
///
/// The index-space guards are the load-bearing ones. In wasm, imported
/// functions and globals occupy the LOW index space and definitions follow, so
/// an import declared *after* a definition of the same kind would silently
/// shift every index already handed out — call targets, element segments,
/// exports, `global.get`/`global.set`. That is a silent miscompile (calls land
/// on the wrong function), so the encoder refuses the ordering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmEncodeError {
    /// An import was declared after a definition of the same kind.
    ImportAfterDefinition {
        kind: &'static str,
        import: String,
        defined: u32,
    },
    /// The module needs a linear memory but its policy provides none.
    NoMemory(String),
    /// A global initializer does not match its declared type, or reads a
    /// global that is not an imported immutable global of the same type.
    InvalidGlobalInit(String),
    /// An ACTIVE data segment would be written into a linear memory this module
    /// does not own. The segment names an ABSOLUTE address in the HOST's
    /// address space, which the host never agreed to, so it is refused unless
    /// the grant is recorded ([`WasmModule::grant_imported_memory_data`]).
    DataIntoImportedMemory {
        module: String,
        name: String,
        offset: u32,
        len: usize,
    },
    /// A data segment does not fit the memory it targets: it runs past the
    /// wasm32 address space, or past the declared minimum of an OWNED memory
    /// (where instantiation would trap instead of initializing).
    DataOutOfRange(String),
}

impl fmt::Display for WasmEncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmEncodeError::ImportAfterDefinition {
                kind,
                import,
                defined,
            } => write!(
                f,
                "{kind} import `{import}` declared after {defined} {kind}(s) were defined: \
                 imported {kind}s occupy the LOW index space, so every index already issued \
                 would shift — declare all {kind} imports before the first definition"
            ),
            WasmEncodeError::NoMemory(m) => {
                write!(f, "module needs a linear memory but has none: {m}")
            }
            WasmEncodeError::InvalidGlobalInit(m) => write!(f, "invalid global initializer: {m}"),
            WasmEncodeError::DataIntoImportedMemory {
                module,
                name,
                offset,
                len,
            } => write!(
                f,
                "active data segment of {len} byte(s) at address {offset} would be written into \
                 the IMPORTED memory `{module}.{name}` at instantiation: that address is the \
                 HOST's, not this module's — place the data in an owned memory, or record the \
                 host's grant with `WasmModule::grant_imported_memory_data`"
            ),
            WasmEncodeError::DataOutOfRange(m) => {
                write!(f, "data segment does not fit its memory: {m}")
            }
        }
    }
}

impl std::error::Error for WasmEncodeError {}

/// An imported function: its two-level name and its type index.
#[derive(Debug, Clone)]
struct FuncImport {
    module: String,
    name: String,
    type_idx: u32,
}

/// An imported global: its two-level name, value type, and mutability.
#[derive(Debug, Clone)]
struct GlobalImport {
    module: String,
    name: String,
    ty: ValType,
    mutable: bool,
}

/// An imported linear memory: its two-level name.
#[derive(Debug, Clone)]
struct MemoryImport {
    module: String,
    name: String,
}

/// A module-level global: value type, mutability, and its initializer.
#[derive(Debug, Clone)]
struct GlobalDef {
    ty: ValType,
    mutable: bool,
    init: GlobalInit,
}

/// An ACTIVE data segment: `bytes` copied into memory 0 starting at `offset`
/// when the module is instantiated (WebAssembly Core Specification, "Data
/// Section" — section id 11, segment form `0x00 offset:expr init:vec(byte)`).
#[derive(Debug, Clone, PartialEq, Eq)]
struct DataSegment {
    offset: u32,
    bytes: Vec<u8>,
}

/// A WebAssembly module under construction.
#[derive(Debug, Clone, Default)]
pub struct WasmModule {
    types: Vec<FuncType>,
    /// Imported functions, occupying function indices `0..func_imports.len()`.
    func_imports: Vec<FuncImport>,
    /// Imported globals, occupying global indices `0..global_imports.len()`.
    global_imports: Vec<GlobalImport>,
    /// The imported linear memory, if the policy imports one.
    memory_import: Option<MemoryImport>,
    /// How this module's linear memory is provided when it is needed.
    memory_policy: WasmMemoryPolicy,
    /// Type index for each defined function (parallel to `bodies`).
    func_types: Vec<u32>,
    bodies: Vec<FuncBody>,
    exports: Vec<Export>,
    /// Linear memory minimum size in 64KiB pages, if the module DEFINES one.
    memory_min_pages: Option<u32>,
    globals: Vec<GlobalDef>,
    /// If set, a `funcref` table is emitted holding every function (imported
    /// and defined) at element index `i = funcidx i` (for `call_indirect` /
    /// function pointers). The size is derived from [`WasmModule::func_count`]
    /// at emission, never from caller arithmetic that could forget the import
    /// shift.
    func_table: bool,
    /// ACTIVE data segments, emitted as section 11 in declaration order.
    data_segments: Vec<DataSegment>,
    /// The host has explicitly granted this module the right to write ACTIVE
    /// data segments into the memory it IMPORTS. Without it,
    /// [`WasmModule::add_data_segment`] fails closed under an imported memory.
    imported_memory_data_granted: bool,
}

impl WasmModule {
    /// A closed module: it owns one page of linear memory (emitted only if it
    /// turns out to need memory) and exports it to nobody.
    pub fn new() -> Self {
        Self::default()
    }

    /// A module whose linear memory is provided by `policy`.
    pub fn with_memory_policy(policy: WasmMemoryPolicy) -> Self {
        Self {
            memory_policy: policy,
            ..Self::default()
        }
    }

    /// This module's memory policy.
    pub fn memory_policy(&self) -> &WasmMemoryPolicy {
        &self.memory_policy
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

    /// Import a function from `module`.`name` with the given type index,
    /// returning its **function index**. Imported functions occupy the low
    /// index space `0..N`, so this must be called before the first
    /// [`WasmModule::add_function`] — otherwise the already-issued index of a
    /// defined function would shift, and the call refuses
    /// ([`WasmEncodeError::ImportAfterDefinition`]).
    pub fn add_func_import(
        &mut self,
        module: &str,
        name: &str,
        type_idx: u32,
    ) -> Result<u32, WasmEncodeError> {
        if !self.func_types.is_empty() {
            return Err(WasmEncodeError::ImportAfterDefinition {
                kind: "function",
                import: format!("{module}.{name}"),
                defined: self.func_types.len() as u32,
            });
        }
        let idx = self.func_imports.len() as u32;
        self.func_imports.push(FuncImport {
            module: module.to_string(),
            name: name.to_string(),
            type_idx,
        });
        Ok(idx)
    }

    /// Import a global from `module`.`name`, returning its **global index**.
    /// Imported globals occupy the low index space `0..M`, so this must be
    /// called before the first [`WasmModule::add_global`].
    pub fn add_global_import(
        &mut self,
        module: &str,
        name: &str,
        ty: ValType,
        mutable: bool,
    ) -> Result<u32, WasmEncodeError> {
        if !self.globals.is_empty() {
            return Err(WasmEncodeError::ImportAfterDefinition {
                kind: "global",
                import: format!("{module}.{name}"),
                defined: self.globals.len() as u32,
            });
        }
        let idx = self.global_imports.len() as u32;
        self.global_imports.push(GlobalImport {
            module: module.to_string(),
            name: name.to_string(),
            ty,
            mutable,
        });
        Ok(idx)
    }

    /// The number of imported functions — the base of the *defined*-function
    /// index space.
    pub fn func_import_count(&self) -> u32 {
        self.func_imports.len() as u32
    }

    /// The number of imported globals — the base of the *defined*-global index
    /// space.
    pub fn global_import_count(&self) -> u32 {
        self.global_imports.len() as u32
    }

    /// Every function in the module's index space: imports plus definitions.
    pub fn func_count(&self) -> u32 {
        self.func_import_count() + self.func_types.len() as u32
    }

    /// Define a function of the given type with the given body. Returns the new
    /// function index — **import-shifted**: `func_import_count() + ordinal`.
    pub fn add_function(&mut self, type_idx: u32, body: FuncBody) -> u32 {
        let idx = self.func_import_count() + self.func_types.len() as u32;
        self.func_types.push(type_idx);
        self.bodies.push(body);
        idx
    }

    /// True once the module has a linear memory (defined or imported).
    pub fn has_memory(&self) -> bool {
        self.memory_min_pages.is_some() || self.memory_import.is_some()
    }

    /// Provide the module's linear memory per its [`WasmMemoryPolicy`].
    /// Idempotent. Fails closed when the policy is
    /// [`WasmMemoryPolicy::Absent`] — a module that needs memory under a
    /// no-memory policy is refused, not emitted with dangling accesses.
    pub fn require_memory(&mut self) -> Result<(), WasmEncodeError> {
        if self.has_memory() {
            return Ok(());
        }
        match self.memory_policy.clone() {
            WasmMemoryPolicy::Absent => Err(WasmEncodeError::NoMemory(
                "memory policy is Absent (the module neither defines nor imports one)".to_string(),
            )),
            WasmMemoryPolicy::Owned { pages, export } => {
                self.memory_min_pages = Some(pages);
                if let Some(name) = export {
                    self.export_memory(&name);
                }
                Ok(())
            }
            WasmMemoryPolicy::Imported { module, name } => {
                self.memory_import = Some(MemoryImport { module, name });
                Ok(())
            }
        }
    }

    /// Add a module global. Returns its **global index** — import-shifted:
    /// `global_import_count() + ordinal`.
    ///
    /// Fails closed when the initializer does not match the declared type, or
    /// when it reads a global that is not an imported immutable global of the
    /// same type (the only `global.get` the spec admits in a constant
    /// expression).
    pub fn add_global(
        &mut self,
        ty: ValType,
        mutable: bool,
        init: GlobalInit,
    ) -> Result<u32, WasmEncodeError> {
        match (ty, init) {
            (ValType::I32, GlobalInit::I32(_)) | (ValType::I64, GlobalInit::I64(_)) => {}
            (_, GlobalInit::ImportedGlobal(g)) => {
                let src = self.global_imports.get(g as usize).ok_or_else(|| {
                    WasmEncodeError::InvalidGlobalInit(format!(
                        "global.get {g} names no imported global (the module imports {})",
                        self.global_imports.len()
                    ))
                })?;
                if src.mutable {
                    return Err(WasmEncodeError::InvalidGlobalInit(format!(
                        "global.get {g} reads imported `{}.{}`, which is MUTABLE; a constant \
                         expression may read only an imported IMMUTABLE global",
                        src.module, src.name
                    )));
                }
                if src.ty != ty {
                    return Err(WasmEncodeError::InvalidGlobalInit(format!(
                        "global.get {g} reads imported `{}.{}` of type {:?}, but the global being \
                         defined is {ty:?}",
                        src.module, src.name, src.ty
                    )));
                }
            }
            _ => {
                return Err(WasmEncodeError::InvalidGlobalInit(format!(
                    "{init:?} does not initialize a {ty:?} global"
                )));
            }
        }
        let idx = self.global_import_count() + self.globals.len() as u32;
        self.globals.push(GlobalDef { ty, mutable, init });
        Ok(idx)
    }

    /// Record the host's grant to write ACTIVE data segments into the memory
    /// this module IMPORTS.
    ///
    /// An active segment is copied into memory 0 at an ABSOLUTE address when
    /// the module is instantiated. In an owned memory that address is the
    /// module's own business; in a host's memory it is the host's data, so the
    /// host must have reserved the region and said so. This records that it
    /// did — it verifies nothing, exactly like every other half of the host
    /// contract (see `super::lower::WasmCompileEvidence`).
    pub fn grant_imported_memory_data(&mut self) {
        self.imported_memory_data_granted = true;
    }

    /// Declare an ACTIVE data segment: `bytes` written into memory 0 at
    /// `offset` when the module is instantiated. An empty `bytes` is a no-op
    /// (wasm memory is already zero-initialized), so it declares nothing.
    ///
    /// Fails closed when the module has no memory, when the segment runs past
    /// the wasm32 address space or past an OWNED memory's declared minimum
    /// (where instantiation would TRAP rather than initialize), or when it
    /// would write into an IMPORTED memory without the host's recorded grant.
    pub fn add_data_segment(&mut self, offset: u32, bytes: Vec<u8>) -> Result<(), WasmEncodeError> {
        if bytes.is_empty() {
            return Ok(());
        }
        if !self.has_memory() {
            return Err(WasmEncodeError::NoMemory(format!(
                "an active data segment of {} byte(s) at address {offset} needs a linear memory \
                 to be written into",
                bytes.len(),
            )));
        }
        let end = u64::from(offset) + bytes.len() as u64;
        if end > u64::from(u32::MAX) + 1 {
            return Err(WasmEncodeError::DataOutOfRange(format!(
                "{} byte(s) at address {offset} run past the end of the wasm32 address space",
                bytes.len(),
            )));
        }
        if let Some(pages) = self.memory_min_pages {
            let limit = u64::from(pages) * u64::from(WASM_PAGE_BYTES);
            if end > limit {
                return Err(WasmEncodeError::DataOutOfRange(format!(
                    "{} byte(s) at address {offset} end at {end}, past the {pages}-page \
                     ({limit}-byte) minimum of this module's own memory — instantiation would \
                     trap instead of initializing",
                    bytes.len(),
                )));
            }
        }
        if let Some(m) = &self.memory_import
            && !self.imported_memory_data_granted
        {
            return Err(WasmEncodeError::DataIntoImportedMemory {
                module: m.module.clone(),
                name: m.name.clone(),
                offset,
                len: bytes.len(),
            });
        }
        self.data_segments.push(DataSegment { offset, bytes });
        Ok(())
    }

    /// The number of ACTIVE data segments declared.
    pub fn data_segment_count(&self) -> usize {
        self.data_segments.len()
    }

    /// Emit a `funcref` table holding EVERY function — imported and defined —
    /// at element index equal to its function index, so a function pointer is
    /// its funcidx. The size and contents are derived from
    /// [`WasmModule::func_count`] when the module is serialized, so the import
    /// shift cannot be forgotten at a call site.
    pub fn enable_func_table(&mut self) {
        self.func_table = true;
    }

    /// Export a defined function under `name`. `func_idx` is the value
    /// [`WasmModule::add_function`] returned (already import-shifted).
    pub fn export_func(&mut self, name: &str, func_idx: u32) {
        self.exports.push(Export {
            name: name.to_string(),
            kind: ExportKind::Func,
            index: func_idx,
        });
    }

    /// Export the module's single linear memory under `name`.
    pub fn export_memory(&mut self, name: &str) {
        self.exports.push(Export {
            name: name.to_string(),
            kind: ExportKind::Memory,
            index: 0,
        });
    }

    /// Export a global under `name`. `global_idx` is the value
    /// [`WasmModule::add_global`] returned (already import-shifted).
    pub fn export_global(&mut self, name: &str, global_idx: u32) {
        self.exports.push(Export {
            name: name.to_string(),
            kind: ExportKind::Global,
            index: global_idx,
        });
    }

    /// The host contract this module binds: every import it requires, as
    /// `"<kind> <module>.<name>"` lines in emission order. Empty for a closed
    /// module — which is exactly the claim "the boundary is the module".
    pub fn host_contract(&self) -> Vec<String> {
        let mut out = Vec::new();
        for f in &self.func_imports {
            out.push(format!("func {}.{}", f.module, f.name));
        }
        if let Some(m) = &self.memory_import {
            out.push(format!("memory {}.{}", m.module, m.name));
        }
        for g in &self.global_imports {
            out.push(format!("global {}.{}", g.module, g.name));
        }
        out
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

        // Import section (id 2). Within each kind, appearance order IS the
        // index order, so functions and globals are emitted in the order they
        // were declared; the kinds themselves may be interleaved freely.
        let import_count = self.func_imports.len()
            + usize::from(self.memory_import.is_some())
            + self.global_imports.len();
        if import_count > 0 {
            let mut body = Vec::new();
            write_uleb128(&mut body, import_count as u64);
            for f in &self.func_imports {
                push_name(&mut body, &f.module);
                push_name(&mut body, &f.name);
                body.push(0x00); // importdesc: func
                write_uleb128(&mut body, u64::from(f.type_idx));
            }
            if let Some(m) = &self.memory_import {
                push_name(&mut body, &m.module);
                push_name(&mut body, &m.name);
                body.push(0x02); // importdesc: mem
                body.push(0x00); // limits flag: min only
                // min 0: the island makes no demand on the host memory's size
                // (the host tells it where its region is), and `min 0` matches
                // every host memory.
                write_uleb128(&mut body, 0);
            }
            for g in &self.global_imports {
                push_name(&mut body, &g.module);
                push_name(&mut body, &g.name);
                body.push(0x03); // importdesc: global
                body.push(g.ty.code());
                body.push(if g.mutable { 0x01 } else { 0x00 });
            }
            push_section(&mut out, 2, &body);
        }

        // Function section (id 3): defined functions and their type indices.
        if !self.func_types.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.func_types.len() as u64);
            for type_idx in &self.func_types {
                write_uleb128(&mut body, u64::from(*type_idx));
            }
            push_section(&mut out, 3, &body);
        }

        // Table section (id 4): one funcref table sized to hold all functions
        // (imported ones included — they share the function index space).
        if self.func_table {
            let mut body = Vec::new();
            write_uleb128(&mut body, 1); // one table
            body.push(0x70); // funcref element type
            body.push(0x00); // limits flag: min only
            write_uleb128(&mut body, u64::from(self.func_count()));
            push_section(&mut out, 4, &body);
        }

        // Memory section (id 5): a single linear memory with a min size. Only
        // a DEFINED memory lands here; an imported one is in section 2.
        if let Some(min_pages) = self.memory_min_pages {
            let mut body = Vec::new();
            write_uleb128(&mut body, 1); // one memory
            body.push(0x00); // limits flag: min only
            write_uleb128(&mut body, u64::from(min_pages));
            push_section(&mut out, 5, &body);
        }

        // Global section (id 6): DEFINED globals only.
        if !self.globals.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.globals.len() as u64);
            for g in &self.globals {
                body.push(g.ty.code());
                body.push(if g.mutable { 0x01 } else { 0x00 });
                // Constant init expression.
                match g.init {
                    GlobalInit::I32(v) => {
                        body.push(op::I32_CONST);
                        write_sleb128(&mut body, i64::from(v));
                    }
                    GlobalInit::I64(v) => {
                        body.push(op::I64_CONST);
                        write_sleb128(&mut body, v);
                    }
                    GlobalInit::ImportedGlobal(idx) => {
                        body.push(op::GLOBAL_GET);
                        write_uleb128(&mut body, u64::from(idx));
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
                push_name(&mut body, &export.name);
                body.push(export.kind.code());
                write_uleb128(&mut body, u64::from(export.index));
            }
            push_section(&mut out, 7, &body);
        }

        // Element section (id 9): an active segment filling table 0 at offset 0
        // with every function index, so funcidx == table element index.
        if self.func_table {
            let count = self.func_count();
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

        // Data section (id 11): ACTIVE segments, each `0x00 offset:expr
        // init:vec(byte)`. It follows the code section: the binary section
        // order is by increasing id, and the only exception (datacount, id 12,
        // which sits before code) exists solely for the bulk-memory
        // instructions this encoder does not emit.
        if !self.data_segments.is_empty() {
            let mut body = Vec::new();
            write_uleb128(&mut body, self.data_segments.len() as u64);
            for seg in &self.data_segments {
                write_uleb128(&mut body, 0); // segment kind 0: active, memory 0
                // offset init expr: i32.const <addr>; end. The address is an
                // UNSIGNED wasm32 address carried in an i32 bit pattern.
                body.push(op::I32_CONST);
                write_sleb128(&mut body, i64::from(seg.offset as i32));
                body.push(op::END);
                write_uleb128(&mut body, seg.bytes.len() as u64);
                body.extend_from_slice(&seg.bytes);
            }
            push_section(&mut out, 11, &body);
        }

        out
    }
}

/// Write a wasm `name`: a ULEB128 byte length followed by its UTF-8 bytes.
fn push_name(out: &mut Vec<u8>, name: &str) {
    write_uleb128(out, name.len() as u64);
    out.extend_from_slice(name.as_bytes());
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
    // The complete memory-instruction table, WebAssembly Core Specification
    // "Memory Instructions" (binary opcodes 0x28..=0x40). Every sub-word load
    // names its extension explicitly — `_s` sign-extends the loaded bits into
    // the value type, `_u` zero-extends them — and every sub-word store writes
    // the low bits of the operand.
    pub const I32_LOAD: u8 = 0x28;
    pub const I64_LOAD: u8 = 0x29;
    pub const F32_LOAD: u8 = 0x2a;
    pub const F64_LOAD: u8 = 0x2b;
    pub const I32_LOAD8_S: u8 = 0x2c;
    pub const I32_LOAD8_U: u8 = 0x2d;
    pub const I32_LOAD16_S: u8 = 0x2e;
    pub const I32_LOAD16_U: u8 = 0x2f;
    pub const I64_LOAD8_S: u8 = 0x30;
    pub const I64_LOAD8_U: u8 = 0x31;
    pub const I64_LOAD16_S: u8 = 0x32;
    pub const I64_LOAD16_U: u8 = 0x33;
    pub const I64_LOAD32_S: u8 = 0x34;
    pub const I64_LOAD32_U: u8 = 0x35;
    pub const I32_STORE: u8 = 0x36;
    pub const I64_STORE: u8 = 0x37;
    pub const F32_STORE: u8 = 0x38;
    pub const F64_STORE: u8 = 0x39;
    pub const I32_STORE8: u8 = 0x3a;
    pub const I32_STORE16: u8 = 0x3b;
    pub const I64_STORE8: u8 = 0x3c;
    pub const I64_STORE16: u8 = 0x3d;
    pub const I64_STORE32: u8 = 0x3e;
    /// `memory.size` — the current size of memory 0 in 64KiB pages. Followed by
    /// a single-byte memory index (always 0: the MVP has one memory).
    pub const MEMORY_SIZE: u8 = 0x3f;
    /// `memory.grow` — grow memory 0 by the popped page delta, pushing the
    /// PREVIOUS size in pages, or -1 if the request could not be met. Followed
    /// by a single-byte memory index (always 0).
    pub const MEMORY_GROW: u8 = 0x40;

    // Constants. The integer forms carry a signed LEB128 payload; the float
    // forms carry a RAW little-endian IEEE-754 payload (4 / 8 bytes).
    pub const I32_CONST: u8 = 0x41;
    pub const I64_CONST: u8 = 0x42;
    pub const F32_CONST: u8 = 0x43;
    pub const F64_CONST: u8 = 0x44;

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

    // Sign-extension operators (WebAssembly Core Specification 2.0, "Numeric
    // Instructions"): `extendN_s` sign-extends the low N bits of the operand
    // into the full value type. These are how a narrow trust-ir value is
    // re-canonicalized into its i32 carrier after an operation that could have
    // carried out of the narrow width (see `super::lower`'s narrow-carrier
    // invariant).
    pub const I32_EXTEND8_S: u8 = 0xc0;
    pub const I32_EXTEND16_S: u8 = 0xc1;

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

/// Append `memory.size` (opcode + the memory index, always 0). Pushes the
/// current size of memory 0 in 64KiB pages.
pub fn emit_memory_size(code: &mut Vec<u8>) {
    code.push(op::MEMORY_SIZE);
    code.push(0x00);
}

/// Append `memory.grow` (opcode + the memory index, always 0). Pops a page
/// delta and pushes the PREVIOUS size in pages, or `-1` when the request could
/// not be satisfied.
pub fn emit_memory_grow(code: &mut Vec<u8>) {
    code.push(op::MEMORY_GROW);
    code.push(0x00);
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

    // -----------------------------------------------------------------------
    // P2: imports and the index space.
    // -----------------------------------------------------------------------

    /// Read a ULEB128 out of `buf`, returning `(value, bytes_consumed)`.
    fn read_uleb128(buf: &[u8]) -> (u64, usize) {
        let mut value = 0u64;
        let mut shift = 0;
        let mut i = 0;
        loop {
            let byte = buf[i];
            value |= u64::from(byte & 0x7f) << shift;
            i += 1;
            if byte & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        (value, i)
    }

    /// Split a finished module into `(section id, body)` in emission order.
    fn sections(bytes: &[u8]) -> Vec<(u8, Vec<u8>)> {
        let mut out = Vec::new();
        let mut i = 8; // magic + version
        while i < bytes.len() {
            let id = bytes[i];
            i += 1;
            let (len, used) = read_uleb128(&bytes[i..]);
            i += used;
            let len = len as usize;
            out.push((id, bytes[i..i + len].to_vec()));
            i += len;
        }
        out
    }

    fn section(bytes: &[u8], id: u8) -> Option<Vec<u8>> {
        sections(bytes)
            .into_iter()
            .find(|(i, _)| *i == id)
            .map(|(_, b)| b)
    }

    fn void_type(m: &mut WasmModule) -> u32 {
        m.add_type(FuncType::default())
    }

    fn nop_body() -> FuncBody {
        FuncBody::default()
    }

    /// The finding-class this slice exists to eliminate: imported functions
    /// occupy the LOW index space, so a defined function's index is
    /// `N + ordinal`, never `ordinal`.
    #[test]
    fn func_imports_shift_the_defined_function_index_space() {
        let mut m = WasmModule::new();
        let t = void_type(&mut m);
        assert_eq!(m.add_func_import("host", "a", t).unwrap(), 0);
        assert_eq!(m.add_func_import("host", "b", t).unwrap(), 1);
        assert_eq!(m.add_func_import("host", "c", t).unwrap(), 2);
        assert_eq!(m.func_import_count(), 3);
        // Defined functions follow the imports.
        assert_eq!(m.add_function(t, nop_body()), 3);
        assert_eq!(m.add_function(t, nop_body()), 4);
        assert_eq!(m.func_count(), 5);
    }

    /// Same rule for globals — the shadow stack pointer's index is what the
    /// prologue's `global.get`/`global.set` immediates encode.
    #[test]
    fn global_imports_shift_the_defined_global_index_space() {
        let mut m = WasmModule::new();
        assert_eq!(
            m.add_global_import("host", "base", ValType::I32, false)
                .unwrap(),
            0
        );
        assert_eq!(
            m.add_global_import("host", "limit", ValType::I32, false)
                .unwrap(),
            1
        );
        assert_eq!(m.global_import_count(), 2);
        assert_eq!(
            m.add_global(ValType::I32, true, GlobalInit::I32(0))
                .unwrap(),
            2
        );
    }

    /// An import declared after a definition would shift an index already
    /// handed out — refused, both kinds.
    #[test]
    fn an_import_after_a_definition_is_refused() {
        let mut m = WasmModule::new();
        let t = void_type(&mut m);
        m.add_function(t, nop_body());
        let err = m.add_func_import("host", "late", t).unwrap_err();
        assert!(
            matches!(
                err,
                WasmEncodeError::ImportAfterDefinition {
                    kind: "function",
                    ..
                }
            ),
            "{err}"
        );
        assert!(err.to_string().contains("host.late"), "{err}");

        let mut m = WasmModule::new();
        m.add_global(ValType::I32, true, GlobalInit::I32(1))
            .unwrap();
        let err = m
            .add_global_import("host", "late", ValType::I32, false)
            .unwrap_err();
        assert!(
            matches!(
                err,
                WasmEncodeError::ImportAfterDefinition { kind: "global", .. }
            ),
            "{err}"
        );
    }

    /// The funcref table covers the WHOLE function index space (imports
    /// included), so element index == funcidx still holds with imports.
    #[test]
    fn the_element_segment_covers_imports_and_definitions() {
        let mut m = WasmModule::new();
        let t = void_type(&mut m);
        m.add_func_import("host", "a", t).unwrap();
        m.add_func_import("host", "b", t).unwrap();
        m.add_function(t, nop_body());
        m.enable_func_table();
        let bytes = m.finish();

        // Table section: 1 table, funcref, min-only limits, min == 3.
        assert_eq!(section(&bytes, 4).unwrap(), vec![0x01, 0x70, 0x00, 0x03]);
        // Element section: 1 active segment @ table 0, offset i32.const 0,
        // then funcidx 0,1,2 — the imports are elements too.
        assert_eq!(
            section(&bytes, 9).unwrap(),
            vec![
                0x01,
                0x00,
                op::I32_CONST,
                0x00,
                op::END,
                0x03,
                0x00,
                0x01,
                0x02
            ]
        );
    }

    /// The import section (id 2) sits between types (1) and functions (3), and
    /// carries the two-level names plus descriptors.
    #[test]
    fn emits_an_import_section_in_the_right_place() {
        let mut m = WasmModule::with_memory_policy(WasmMemoryPolicy::Imported {
            module: "env".to_string(),
            name: "memory".to_string(),
        });
        let t = m.add_type(FuncType {
            params: vec![ValType::I32],
            results: vec![],
        });
        m.add_func_import("env", "log", t).unwrap();
        m.add_global_import("env", "base", ValType::I32, false)
            .unwrap();
        m.require_memory().unwrap();
        m.add_function(t, nop_body());

        let bytes = m.finish();
        let ids: Vec<u8> = sections(&bytes).into_iter().map(|(id, _)| id).collect();
        assert_eq!(ids, vec![1, 2, 3, 10], "section order/presence: {ids:?}");

        #[rustfmt::skip]
        let expected_imports: Vec<u8> = vec![
            0x03,                                     // 3 imports
            0x03, b'e', b'n', b'v', 0x03, b'l', b'o', b'g', 0x00, 0x00, // func env.log : type 0
            0x03, b'e', b'n', b'v', 0x06, b'm', b'e', b'm', b'o', b'r', b'y',
            0x02, 0x00, 0x00,                         // mem env.memory : min 0
            0x03, b'e', b'n', b'v', 0x04, b'b', b'a', b's', b'e',
            0x03, 0x7f, 0x00,                         // global env.base : i32 immutable
        ];
        assert_eq!(section(&bytes, 2).unwrap(), expected_imports);
        // An IMPORTED memory means no memory section at all.
        assert!(
            section(&bytes, 5).is_none(),
            "imported memory must not be defined too"
        );
        assert_eq!(
            m.host_contract(),
            vec!["func env.log", "memory env.memory", "global env.base"]
        );
    }

    /// A defined global may be seeded from an imported IMMUTABLE global of the
    /// same type — the host-negotiated stack base. Everything else fails
    /// closed.
    #[test]
    fn global_init_from_an_imported_global_is_checked() {
        let mut m = WasmModule::new();
        let imm = m
            .add_global_import("env", "base", ValType::I32, false)
            .unwrap();
        let mutable = m
            .add_global_import("env", "cursor", ValType::I32, true)
            .unwrap();
        let wide = m
            .add_global_import("env", "wide", ValType::I64, false)
            .unwrap();

        // The good case: i32 defined global seeded from the immutable import.
        let sp = m
            .add_global(ValType::I32, true, GlobalInit::ImportedGlobal(imm))
            .unwrap();
        assert_eq!(sp, 3, "defined globals follow the three imports");

        let err = m
            .add_global(ValType::I32, true, GlobalInit::ImportedGlobal(mutable))
            .unwrap_err();
        assert!(err.to_string().contains("MUTABLE"), "{err}");
        let err = m
            .add_global(ValType::I32, true, GlobalInit::ImportedGlobal(wide))
            .unwrap_err();
        assert!(err.to_string().contains("I64"), "{err}");
        let err = m
            .add_global(ValType::I32, true, GlobalInit::ImportedGlobal(99))
            .unwrap_err();
        assert!(
            err.to_string().contains("names no imported global"),
            "{err}"
        );
        // Type/initializer mismatches are refused rather than silently
        // re-encoded as an i32 constant (the pre-P2 fallthrough).
        let err = m
            .add_global(ValType::F64, true, GlobalInit::I32(0))
            .unwrap_err();
        assert!(
            matches!(err, WasmEncodeError::InvalidGlobalInit(_)),
            "{err}"
        );

        // The seeded global emits `global.get 0; end` as its init expr.
        let globals = section(&m.finish(), 6).unwrap();
        assert_eq!(
            globals,
            vec![0x01, 0x7f, 0x01, op::GLOBAL_GET, 0x00, op::END]
        );
    }

    /// Fail-closed: a module that needs memory under `Absent` is refused.
    #[test]
    fn require_memory_fails_closed_under_the_absent_policy() {
        let mut m = WasmModule::with_memory_policy(WasmMemoryPolicy::Absent);
        let err = m.require_memory().unwrap_err();
        assert!(matches!(err, WasmEncodeError::NoMemory(_)), "{err}");
        assert!(!m.has_memory());
    }

    // -----------------------------------------------------------------------
    // P3: data segments, memory.size/grow, and the memory opcode table.
    // -----------------------------------------------------------------------

    /// The data section (id 11) sits AFTER the code section (id 10) and encodes
    /// each active segment as `0x00 i32.const <addr> end <len> <bytes>`.
    #[test]
    fn emits_an_active_data_section_after_the_code_section() {
        let mut m = WasmModule::new();
        let t = void_type(&mut m);
        m.add_function(t, nop_body());
        m.require_memory().unwrap();
        m.add_data_segment(8, vec![0xde, 0xad, 0xbe, 0xef]).unwrap();
        m.add_data_segment(200, vec![0x01]).unwrap();
        assert_eq!(m.data_segment_count(), 2);

        let bytes = m.finish();
        let ids: Vec<u8> = sections(&bytes).into_iter().map(|(id, _)| id).collect();
        assert_eq!(ids, vec![1, 3, 5, 10, 11], "section order: {ids:?}");

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            0x02,                                            // 2 segments
            0x00, op::I32_CONST, 0x08, op::END, 0x04, 0xde, 0xad, 0xbe, 0xef,
            0x00, op::I32_CONST, 0xc8, 0x01, op::END, 0x01, 0x01,
        ];
        assert_eq!(section(&bytes, 11).unwrap(), expected);
    }

    /// An empty segment declares nothing: wasm memory is already zeroed, so a
    /// zero-length write is not an encoding the module needs to carry.
    #[test]
    fn an_empty_data_segment_is_not_emitted() {
        let mut m = WasmModule::new();
        m.require_memory().unwrap();
        m.add_data_segment(0, vec![]).unwrap();
        assert_eq!(m.data_segment_count(), 0);
        assert!(section(&m.finish(), 11).is_none());
    }

    /// Fail-closed: no memory, no data segment.
    #[test]
    fn a_data_segment_without_a_memory_is_refused() {
        let mut m = WasmModule::with_memory_policy(WasmMemoryPolicy::Absent);
        let err = m.add_data_segment(0, vec![1, 2, 3]).unwrap_err();
        assert!(matches!(err, WasmEncodeError::NoMemory(_)), "{err}");
    }

    /// Fail-closed: a segment past the OWNED memory's declared minimum would
    /// TRAP at instantiation, so it is refused at encode time instead.
    #[test]
    fn a_data_segment_past_the_owned_minimum_is_refused() {
        let mut m = WasmModule::with_memory_policy(WasmMemoryPolicy::Owned {
            pages: 1,
            export: None,
        });
        m.require_memory().unwrap();
        // The last four bytes of the page are fine …
        m.add_data_segment(WASM_PAGE_BYTES - 4, vec![0; 4]).unwrap();
        // … one past it is not.
        let err = m
            .add_data_segment(WASM_PAGE_BYTES - 3, vec![0; 4])
            .unwrap_err();
        assert!(matches!(err, WasmEncodeError::DataOutOfRange(_)), "{err}");
        assert!(err.to_string().contains("1-page"), "{err}");
    }

    /// The contract question this slice exists to ask out loud: an ACTIVE
    /// segment writes into the HOST's memory at instantiation. Refused unless
    /// the host's grant is recorded — and the refusal names the fix.
    #[test]
    fn a_data_segment_into_an_imported_memory_needs_the_hosts_grant() {
        let policy = WasmMemoryPolicy::Imported {
            module: "trust:island/abi@1".to_string(),
            name: "memory".to_string(),
        };
        let mut m = WasmModule::with_memory_policy(policy.clone());
        m.require_memory().unwrap();
        let err = m.add_data_segment(4096, vec![7; 16]).unwrap_err();
        assert!(
            matches!(err, WasmEncodeError::DataIntoImportedMemory { .. }),
            "{err}"
        );
        let msg = err.to_string();
        assert!(msg.contains("trust:island/abi@1.memory"), "{msg}");
        assert!(msg.contains("grant_imported_memory_data"), "{msg}");
        assert_eq!(m.data_segment_count(), 0, "nothing was recorded");

        let mut granted = WasmModule::with_memory_policy(policy);
        granted.require_memory().unwrap();
        granted.grant_imported_memory_data();
        granted.add_data_segment(4096, vec![7; 16]).unwrap();
        assert_eq!(granted.data_segment_count(), 1);
    }

    /// `memory.size` / `memory.grow` carry a single-byte memory index (0).
    #[test]
    fn memory_size_and_grow_encode_their_memory_index() {
        let mut code = Vec::new();
        emit_memory_size(&mut code);
        emit_memory_grow(&mut code);
        assert_eq!(code, vec![0x3f, 0x00, 0x40, 0x00]);
    }

    /// The memory opcodes are FIXED by the spec: pin the whole 0x28..=0x40
    /// block plus the two i32 sign-extension operators, so a typo in the table
    /// is a failing test rather than a module that loads the wrong width.
    #[test]
    fn memory_opcode_bytes_match_the_specification() {
        let table: &[(u8, &str)] = &[
            (op::I32_LOAD, "i32.load"),
            (op::I64_LOAD, "i64.load"),
            (op::F32_LOAD, "f32.load"),
            (op::F64_LOAD, "f64.load"),
            (op::I32_LOAD8_S, "i32.load8_s"),
            (op::I32_LOAD8_U, "i32.load8_u"),
            (op::I32_LOAD16_S, "i32.load16_s"),
            (op::I32_LOAD16_U, "i32.load16_u"),
            (op::I64_LOAD8_S, "i64.load8_s"),
            (op::I64_LOAD8_U, "i64.load8_u"),
            (op::I64_LOAD16_S, "i64.load16_s"),
            (op::I64_LOAD16_U, "i64.load16_u"),
            (op::I64_LOAD32_S, "i64.load32_s"),
            (op::I64_LOAD32_U, "i64.load32_u"),
            (op::I32_STORE, "i32.store"),
            (op::I64_STORE, "i64.store"),
            (op::F32_STORE, "f32.store"),
            (op::F64_STORE, "f64.store"),
            (op::I32_STORE8, "i32.store8"),
            (op::I32_STORE16, "i32.store16"),
            (op::I64_STORE8, "i64.store8"),
            (op::I64_STORE16, "i64.store16"),
            (op::I64_STORE32, "i64.store32"),
            (op::MEMORY_SIZE, "memory.size"),
            (op::MEMORY_GROW, "memory.grow"),
        ];
        // The block is contiguous and ascending from 0x28 by construction.
        for (i, (byte, name)) in table.iter().enumerate() {
            assert_eq!(
                *byte,
                0x28 + i as u8,
                "{name} must encode as {:#04x}",
                0x28 + i as u8
            );
        }
        assert_eq!(op::BR_TABLE, 0x0e, "br_table");
        assert_eq!(op::I32_EXTEND8_S, 0xc0, "i32.extend8_s");
        assert_eq!(op::I32_EXTEND16_S, 0xc1, "i32.extend16_s");
    }

    /// `Owned { export: Some(..) }` defines the memory AND exports it.
    #[test]
    fn owned_memory_can_be_exported() {
        let mut m = WasmModule::with_memory_policy(WasmMemoryPolicy::Owned {
            pages: 2,
            export: Some("memory".to_string()),
        });
        m.require_memory().unwrap();
        m.require_memory().unwrap(); // idempotent
        let bytes = m.finish();
        assert_eq!(section(&bytes, 5).unwrap(), vec![0x01, 0x00, 0x02]);
        assert_eq!(
            section(&bytes, 7).unwrap(),
            vec![0x01, 0x06, b'm', b'e', b'm', b'o', b'r', b'y', 0x02, 0x00]
        );
        assert!(
            m.host_contract().is_empty(),
            "an owned memory binds no host"
        );
    }
}
