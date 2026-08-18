// trust-cg-llvm-import / parser.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Hand-written line-oriented LLVM IR text parser. See the crate README
// for the supported subset and rationale for writing this instead of
// using the `llvm-ir` crate (system-LLVM version drift).
//
// Parsing strategy:
//   * Pre-process: strip comments (`; ...`), `!dbg !N` / `!tbaa !N`
//     attachments, and normalise whitespace.
//   * Classify each line:
//       - module header / directives (target triple, datalayout)
//       - global declaration (`@name = ... constant [N x i8] c"..."`)
//       - function declaration (`declare` ...)
//       - function definition (`define` ...)
//       - inside a function: block label, terminator, instruction,
//         or metadata.
//   * Translate supported constructs directly to `trust_ir::Inst`. Fail
//     fast with `Error::Unsupported("<description>")` for anything
//     outside the subset.
//
// This is deliberately narrow. The goal is to unblock the WS2 driver,
// not to implement a full LLVM frontend. See the expansion plan in the
// README for the sequence of features to add.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

use trust_ir::{
    BinOp, BlockId, CallingConv, CastOp, Constant, FCmpOp, FuncId, FuncTy, FuncTyId, Function,
    Global, ICmpOp, InstrNode, Linkage, Module, ProofAnnotation, ProofTag, SwitchCase, Ty, UnOp,
    ValueId, inst::Inst,
};

use crate::native_vector::{NativeForm, NativePlan, Shape};
use crate::{Error, Result};
use trust_cg_lower::{
    LLVM_LIBM_PURE_FUNCTION_ATTR_TAG, LLVM_STACK_PROTECTOR_FUNCTION_ATTR_TAG,
    LLVM_STACK_PROTECTOR_REQUIRED_FUNCTION_ATTR_TAG,
};

const MAX_IMPORTED_GLOBAL_INIT_BYTES: u64 = 64 * 1024 * 1024;
const MAX_LLVM_IR_INPUT_BYTES: u64 = 64 * 1024 * 1024;

// --------------------------------------------------------------------------
// Public entry points
// --------------------------------------------------------------------------

/// Read the file at `path` and import its LLVM IR text into a `trust_ir::Module`.
pub fn import_module(path: &Path) -> Result<trust_ir::Module> {
    let text = read_llvm_ir_text(path)?;
    let name = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("module")
        .to_string();
    import_text(&text, &name)
}

/// Import an in-memory LLVM IR text string into a `trust_ir::Module`.
pub fn import_text(text: &str, module_name: &str) -> Result<trust_ir::Module> {
    let mut parser = Parser::new(text, module_name.to_string());
    parser.parse()?;
    Ok(parser.module)
}

fn read_llvm_ir_text(path: &Path) -> Result<String> {
    let size = fs::metadata(path)?.len();
    if size > MAX_LLVM_IR_INPUT_BYTES {
        return Err(Error::Unsupported(format!(
            "LLVM IR input '{}' is {} byte(s), over importer limit {}",
            path.display(),
            size,
            MAX_LLVM_IR_INPUT_BYTES
        )));
    }

    let text = fs::read_to_string(path)?;
    if text.len() as u64 > MAX_LLVM_IR_INPUT_BYTES {
        return Err(Error::Unsupported(format!(
            "LLVM IR input '{}' grew over importer limit {} while reading",
            path.display(),
            MAX_LLVM_IR_INPUT_BYTES
        )));
    }
    Ok(text)
}

// --------------------------------------------------------------------------
// Parser state
// --------------------------------------------------------------------------

struct Parser {
    module: Module,
    /// Map from LLVM function name (without `@`) to `FuncId`.
    func_ids: HashMap<String, FuncId>,
    /// Map from LLVM function name to its `FuncTyId`.
    func_tys: HashMap<String, FuncTyId>,
    /// Map from LLVM global name (without `@`) to the index in
    /// `module.globals`. Used to flag the "string head" GEP pattern.
    globals: HashMap<String, usize>,
    /// Named LLVM aggregate layouts keyed by the full `%name` spelling.
    struct_layouts: HashMap<String, StructLayout>,
    /// LLVM `attributes #N = { ... }` groups keyed by the `#N` spelling.
    attribute_groups: HashMap<String, FunctionAttributeSet>,
    /// Libm purity licensing (loop-dead-pure-sink plumbing) — per libm
    /// `llvm.<fn>.fN` intrinsic name, whether EVERY `declare` of it carried the
    /// full pure-math attribute set (`speculatable willreturn nounwind
    /// memory(none)`). Merged with AND across duplicate declares (fail-closed).
    libm_intrinsic_decl_pure: HashMap<String, bool>,
    /// Libm symbols the importer synthesized by rewriting a libm intrinsic
    /// call (`llvm.asin.f64` -> `asin`), keyed libm symbol -> intrinsic name.
    /// BTreeMap so the finalize pass licenses in deterministic name order.
    libm_rewritten_calls: std::collections::BTreeMap<String, String>,
    /// Every OTHER (non-intrinsic-origin) reference to a symbol name: plain
    /// direct calls, address-taken function references (`ptr @sym` operands,
    /// pointer-table global initializers). Any name in here is NEVER licensed
    /// libm-pure, however many intrinsic-origin calls it also has (fail-closed
    /// against a user-supplied impure `asin`). RefCell because two recording
    /// sites (`lookup_operand`, pointer-array globals) hold `&self`.
    libm_plain_uses: std::cell::RefCell<HashSet<String>>,
    /// Per canonical (de-mangled) symbol name, whether it was first introduced
    /// by an LLVM `\01` asm-label or by an ordinary symbol. Used to fail closed
    /// on the ambiguous case where `@"\01_foo"` and a distinct `@foo` both map
    /// to the same linker symbol after de-mangling. Keyed by canonical name.
    symbol_origin: HashMap<String, SymbolOrigin>,
    /// Canonical names of every symbol DEFINED or DECLARED in the module
    /// (data globals + functions), collected by a name-only pre-scan so a
    /// forward reference (a global initializer that names a symbol defined
    /// LATER in the file — e.g. `@refarr = [ptr @.str.22, ...]` where the
    /// strings come after) resolves without a full two-pass parse. Used to
    /// fail closed on a typo'd/undeclared symbol rather than fabricate a
    /// relocation.
    known_symbol_names: HashSet<String>,
    /// Lines of the input, for error context.
    lines: Vec<String>,
}

/// Records how a canonical symbol name was first introduced (see
/// `Parser::symbol_origin`).
#[derive(Clone, Debug)]
struct SymbolOrigin {
    /// True when the source spelling carried the LLVM `\01` asm-label escape.
    is_asm_label: bool,
    /// The raw source spelling (with the leading `@` stripped) for diagnostics.
    original: String,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct StructLayout {
    /// (field_ty, byte_offset)
    fields: Vec<(Ty, u64)>,
    /// Total size rounded up to the struct alignment.
    size: u64,
    /// Maximum field alignment, at least 1.
    align: u64,
}

#[derive(Clone, Copy, Debug, Default)]
struct FunctionAttributeSet {
    stack_protector: ImportedStackProtectorAttr,
    allocsize: bool,
    /// True when the group carries the exact errno-free pure-math license set
    /// LLVM stamps on libm intrinsics: `speculatable willreturn nounwind` plus
    /// the literal `memory(none)` effect. Consumed ONLY for `llvm.<fn>.fN`
    /// libm-intrinsic declarations (libm purity licensing).
    libm_pure_math: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
enum ImportedStackProtectorAttr {
    #[default]
    None,
    Eligible,
    Required,
}

#[derive(Clone, Debug)]
enum FixedLayout {
    Scalar(Ty),
    Struct {
        fields: Vec<FixedStructField>,
        size: u64,
        align: u64,
    },
    Array {
        len: usize,
        elem: Box<FixedLayout>,
        size: u64,
        align: u64,
    },
}

#[derive(Clone, Debug)]
struct FixedStructField {
    layout: FixedLayout,
    offset: u64,
}

impl FixedLayout {
    fn size(&self) -> u64 {
        match self {
            FixedLayout::Scalar(ty) => scalar_layout(ty).map(|(size, _)| size).unwrap_or(0),
            FixedLayout::Struct { size, .. } | FixedLayout::Array { size, .. } => *size,
        }
    }

    fn align(&self) -> u64 {
        match self {
            FixedLayout::Scalar(ty) => scalar_layout(ty).map(|(_, align)| align).unwrap_or(1),
            FixedLayout::Struct { align, .. } | FixedLayout::Array { align, .. } => *align,
        }
    }

    fn top_array_scalar_elem(&self) -> Option<(usize, &Ty)> {
        let FixedLayout::Array { len, elem, .. } = self else {
            return None;
        };
        match elem.as_ref() {
            FixedLayout::Scalar(ty) => Some((*len, ty)),
            _ => None,
        }
    }

    fn supported_zero_global(&self) -> bool {
        match self {
            FixedLayout::Array { elem, .. } => match elem.as_ref() {
                // A `zeroinitializer` is `size()` zero bytes regardless of the
                // element type — the byte image is layout-independent, so ANY
                // scalar element (i1/i8/i16/i32/i64/i128, f16/f32/f64, ptr) is
                // exact. Nested arrays/structs of zeros are likewise all-zero
                // byte images.
                FixedLayout::Scalar(_) => true,
                FixedLayout::Struct { .. } => true,
                FixedLayout::Array { .. } => elem.supported_zero_global(),
            },
            _ => false,
        }
    }

    fn supported_array_gep(&self) -> bool {
        match self {
            FixedLayout::Array { elem, .. } => match elem.as_ref() {
                // The GEP lowers to a byte offset `index * elem.size()`
                // (`pointee_ty: i8`), which is exact for ANY scalar element
                // (i1/i8/i16/i32/i64/i128, f16/f32/f64, ptr) — the element
                // size is all that matters, not its kind.
                FixedLayout::Scalar(_) => true,
                FixedLayout::Struct { .. } => true,
                FixedLayout::Array { .. } => elem.supported_array_gep(),
            },
            _ => false,
        }
    }

    fn is_top_i8_array(&self) -> bool {
        matches!(self.top_array_scalar_elem(), Some((_, Ty::I8)))
    }
}

/// Per-function scratch state: SSA value map, block map, in-progress
/// block list.
struct FuncScratch {
    /// LLVM SSA name (without `%`) -> trust_ir ValueId.
    value_map: HashMap<String, ValueId>,
    /// LLVM block label (without `%`) -> trust_ir BlockId.
    block_map: HashMap<String, BlockId>,
    /// Block bodies indexed by BlockId order of appearance.
    blocks: Vec<trust_ir::Block>,
    /// Next fresh ValueId.
    next_value: u32,
    /// Current block being built (index into blocks).
    current: Option<usize>,
    /// LLVM phi nodes parsed as target block params and applied to
    /// predecessor terminators once every block has been read.
    pending_phis: Vec<PendingPhi>,
    /// Stack slots created by `alloca ptr`; used for bounded O0 proof recovery.
    pointer_stack_slots: HashSet<ValueId>,
    /// Imported proof facts attached to SSA pointer values.
    imported_pointer_proofs: HashMap<ValueId, Vec<ProofAnnotation>>,
    /// Operand-token aliases installed by the vector lane expander (see
    /// [`crate::vector`]): SSA name (no `%`) -> the token it stands for.
    ///
    /// `extractelement` / `insertelement` / `shufflevector` are pure lane
    /// RENAMINGS, so they emit no instruction at all: the result name simply
    /// resolves to the source lane's token, which may itself be another lane
    /// name or a literal. Resolution happens in `lookup_operand` /
    /// `lookup_phi_operand`, and `check_alias_registration_order` proves no
    /// alias was installed after a use of the same name had already been
    /// interned.
    token_alias: HashMap<String, String>,
    /// SSA names `intern_value` resolved WITHOUT an alias being in force.
    /// Used only by `check_alias_registration_order`.
    interned_unaliased: HashSet<String>,
    /// Monotone counter naming the address temporaries a scalarized vector
    /// load/store needs. Function-local and sequential, so it is stable
    /// across runs (reproducible-builds requirement).
    vec_uid: u32,
    /// Which of this function's vector SSA values are carried as ONE native
    /// 128-bit value rather than as scalar lanes. Computed once, before the
    /// body is parsed, by [`crate::native_vector::plan_function`].
    native_plan: NativePlan,
}

#[derive(Clone, Debug)]
struct PendingPhi {
    target: BlockId,
    ty: Ty,
    incomings: Vec<PhiIncoming>,
    lineno: usize,
}

#[derive(Clone, Debug)]
struct PhiIncoming {
    value_tok: String,
    pred: BlockId,
}

impl FuncScratch {
    fn new() -> Self {
        Self {
            value_map: HashMap::new(),
            block_map: HashMap::new(),
            blocks: Vec::new(),
            next_value: 0,
            current: None,
            pending_phis: Vec::new(),
            pointer_stack_slots: HashSet::new(),
            imported_pointer_proofs: HashMap::new(),
            token_alias: HashMap::new(),
            interned_unaliased: HashSet::new(),
            vec_uid: 0,
            native_plan: NativePlan::default(),
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let v = ValueId::new(self.next_value);
        self.next_value += 1;
        v
    }

    fn intern_value(&mut self, name: &str) -> ValueId {
        if !self.token_alias.contains_key(name) {
            self.interned_unaliased.insert(name.to_string());
        }
        if let Some(v) = self.value_map.get(name) {
            return *v;
        }
        let v = self.fresh_value();
        self.value_map.insert(name.to_string(), v);
        v
    }

    /// Resolve an operand token through the vector lane-alias chain.
    ///
    /// `%r` -> `%a#v2` -> `3` collapses to `3`. The chain is finite because an
    /// alias is only ever installed for a FRESH SSA result name, so following
    /// it strictly walks backwards through already-defined names; the bound is
    /// belt-and-braces against a malformed input.
    fn resolve_token_alias(&self, tok: &str) -> String {
        let mut cur = tok.trim().to_string();
        for _ in 0..self.token_alias.len() + 1 {
            let Some(name) = cur.strip_prefix('%') else {
                return cur;
            };
            match self.token_alias.get(name) {
                Some(next) => cur = next.clone(),
                None => return cur,
            }
        }
        cur
    }

    /// Fail closed if any lane alias was installed AFTER a use of the same
    /// name had already been interned as a plain SSA value.
    ///
    /// LLVM prints a definition before its non-phi uses, so this cannot happen
    /// on well-formed clang output — but if it ever did, the use would have
    /// been bound to a value with no definition, which is a MISCOMPILE. This
    /// converts that into a clean `Unsupported`.
    fn check_alias_registration_order(&self) -> Result<()> {
        let mut late: Vec<&str> = self
            .token_alias
            .keys()
            .filter(|k| self.interned_unaliased.contains(*k))
            .map(String::as_str)
            .collect();
        if late.is_empty() {
            return Ok(());
        }
        late.sort_unstable();
        Err(Error::Unsupported(format!(
            "vector lane alias for `%{}` was installed after the name was already \
             used (definition does not textually precede its use)",
            late[0]
        )))
    }

    /// Fail closed if a named SSA value was referenced but never defined.
    ///
    /// Every `%name` the parser interns must end up as a block parameter or as
    /// the result of some instruction. A name that is only ever READ would
    /// lower to an uninitialized register — the exact silent-miscompile shape
    /// that lane expansion could introduce if a vector value's producer were
    /// ever skipped instead of refused.
    fn check_all_named_values_defined(&self) -> Result<()> {
        let mut defined: HashSet<ValueId> = HashSet::new();
        for block in &self.blocks {
            for (v, _) in &block.params {
                defined.insert(*v);
            }
            for node in &block.body {
                for r in &node.results {
                    defined.insert(*r);
                }
            }
        }
        let mut undefined: Vec<&str> = self
            .value_map
            .iter()
            .filter(|(_, v)| !defined.contains(v))
            .map(|(k, _)| k.as_str())
            .collect();
        if undefined.is_empty() {
            return Ok(());
        }
        undefined.sort_unstable();
        Err(Error::Unsupported(format!(
            "SSA value `%{}` is used but never defined ({} such value(s))",
            undefined[0],
            undefined.len()
        )))
    }

    fn next_vec_uid(&mut self) -> u32 {
        let id = self.vec_uid;
        self.vec_uid += 1;
        id
    }

    fn intern_block(&mut self, label: &str) -> BlockId {
        if let Some(b) = self.block_map.get(label) {
            return *b;
        }
        let id = BlockId::new(self.blocks.len() as u32);
        self.blocks.push(trust_ir::Block::new(id));
        self.block_map.insert(label.to_string(), id);
        id
    }

    fn alias_block(&mut self, label: &str, id: BlockId) {
        self.block_map.entry(label.to_string()).or_insert(id);
    }

    fn push_inst(&mut self, node: InstrNode) {
        if let Some(idx) = self.current {
            self.blocks[idx].body.push(node);
        }
    }

    fn record_pointer_stack_slot(&mut self, slot: ValueId) {
        self.pointer_stack_slots.insert(slot);
    }

    fn record_imported_pointer_proofs(
        &mut self,
        value: ValueId,
        proofs: impl IntoIterator<Item = ProofAnnotation>,
    ) {
        let entry = self.imported_pointer_proofs.entry(value).or_default();
        for proof in proofs {
            push_unique_proof(entry, proof);
        }
    }

    fn imported_pointer_proofs_for(&self, value: ValueId) -> Vec<ProofAnnotation> {
        self.imported_pointer_proofs
            .get(&value)
            .cloned()
            .unwrap_or_default()
    }

    fn propagate_imported_o0_pointer_proofs(&mut self, entry: BlockId) {
        let mut slot_facts: HashMap<ValueId, Vec<ProofAnnotation>> = HashMap::new();
        let mut invalid_slots = HashSet::new();

        for (block_idx, block) in self.blocks.iter().enumerate() {
            for node in &block.body {
                let Inst::Store { ty, ptr, value, .. } = &node.inst else {
                    continue;
                };
                if !matches!(ty, Ty::Ptr) || !self.pointer_stack_slots.contains(ptr) {
                    continue;
                }

                let facts = self.imported_pointer_proofs_for(*value);
                if block_idx != entry.as_usize()
                    || facts.is_empty()
                    || slot_facts.insert(*ptr, facts).is_some()
                {
                    invalid_slots.insert(*ptr);
                }
            }
        }

        for slot in &invalid_slots {
            slot_facts.remove(slot);
        }

        let mut loaded_facts = Vec::new();
        for block in &mut self.blocks {
            for node in &mut block.body {
                let Inst::Load { ty, ptr, .. } = &node.inst else {
                    continue;
                };
                if !matches!(ty, Ty::Ptr) {
                    continue;
                }
                let Some(facts) = slot_facts.get(ptr) else {
                    continue;
                };
                for fact in facts.iter().cloned() {
                    push_unique_proof(&mut node.proofs, fact);
                }
                if let Some(result) = node.results.first().copied() {
                    loaded_facts.push((result, facts.clone()));
                }
            }
        }
        for (value, facts) in loaded_facts {
            self.record_imported_pointer_proofs(value, facts);
        }

        let imported_pointer_proofs = self.imported_pointer_proofs.clone();
        let mut derived_facts = Vec::new();
        for block in &mut self.blocks {
            for node in &mut block.body {
                let Inst::GEP { base, .. } = &node.inst else {
                    continue;
                };
                if !node
                    .proofs
                    .iter()
                    .any(|proof| matches!(proof, ProofAnnotation::InBounds))
                {
                    continue;
                }
                let Some(base_facts) = imported_pointer_proofs.get(base) else {
                    continue;
                };
                let derived_noalias: Vec<_> = base_facts
                    .iter()
                    .filter(|&proof| matches!(proof, ProofAnnotation::NoAlias))
                    .cloned()
                    .collect();
                if derived_noalias.is_empty() {
                    continue;
                }
                for fact in derived_noalias.iter().cloned() {
                    push_unique_proof(&mut node.proofs, fact);
                }
                if let Some(result) = node.results.first().copied() {
                    derived_facts.push((result, derived_noalias));
                }
            }
        }
        for (value, facts) in derived_facts {
            self.record_imported_pointer_proofs(value, facts);
        }
    }

    fn set_current(&mut self, id: BlockId) {
        self.current = Some(id.as_usize());
    }

    fn block_label(&self, id: BlockId) -> Option<String> {
        self.block_map
            .iter()
            .find_map(|(label, block)| (*block == id).then(|| label.clone()))
    }

    fn insert_before_terminator(
        &mut self,
        block: BlockId,
        node: InstrNode,
        lineno: usize,
    ) -> Result<()> {
        let block = self.blocks.get_mut(block.as_usize()).ok_or(Error::Parse {
            line: lineno,
            message: format!("unknown block {:?}", block),
        })?;
        let pos = block
            .body
            .iter()
            .position(|n| n.is_terminator())
            .ok_or(Error::Parse {
                line: lineno,
                message: "phi incoming predecessor has no terminator".into(),
            })?;
        block.body.insert(pos, node);
        Ok(())
    }
}

// --------------------------------------------------------------------------
// Parsing
// --------------------------------------------------------------------------

impl Parser {
    fn new(text: &str, module_name: String) -> Self {
        Self {
            module: Module::new(module_name),
            func_ids: HashMap::new(),
            func_tys: HashMap::new(),
            globals: HashMap::new(),
            struct_layouts: HashMap::new(),
            attribute_groups: HashMap::new(),
            libm_intrinsic_decl_pure: HashMap::new(),
            libm_rewritten_calls: std::collections::BTreeMap::new(),
            libm_plain_uses: std::cell::RefCell::new(HashSet::new()),
            symbol_origin: HashMap::new(),
            known_symbol_names: HashSet::new(),
            lines: text.lines().map(|s| s.to_string()).collect(),
        }
    }

    fn err_unsupported(&self, what: &str) -> Error {
        Error::Unsupported(what.to_string())
    }

    fn err_parse(&self, line: usize, msg: &str) -> Error {
        Error::Parse {
            line,
            message: msg.to_string(),
        }
    }

    /// De-mangle an LLVM symbol spelling (with the leading `@` already stripped)
    /// into the canonical name the importer/codegen use, and report whether it
    /// carried the `\01` asm-label escape.
    ///
    /// LLVM prefixes a symbol with the literal byte `\01` (spelled as the three
    /// characters `\`, `0`, `1` inside a quoted name in textual IR) to mean
    /// "emit this symbol VERBATIM — do NOT apply platform mangling". On Mach-O,
    /// codegen unconditionally prepends `_`, so a verbatim Darwin C symbol like
    /// `_fopen` is written by clang as `@"\01_fopen"`. To make codegen's
    /// re-prepend reproduce the labeled name exactly, we strip the `\01` and
    /// ONE leading `_`, yielding `fopen` (codegen re-adds `_` -> `_fopen`).
    ///
    /// A `\01` label that does NOT start with `_` cannot be represented on
    /// Mach-O without threading a real no-mangle flag through lower/codegen, so
    /// it fails closed rather than emit a wrong symbol.
    ///
    /// Non-`\01` spellings (including ordinary quoted names) are returned
    /// unchanged, preserving existing behavior exactly.
    fn split_asm_label(&self, raw_after_at: &str) -> Result<(String, bool)> {
        let inner = if raw_after_at.len() >= 2
            && raw_after_at.starts_with('"')
            && raw_after_at.ends_with('"')
        {
            &raw_after_at[1..raw_after_at.len() - 1]
        } else {
            raw_after_at
        };
        if let Some(rest) = inner.strip_prefix("\\01") {
            if let Some(sym) = rest.strip_prefix('_') {
                return Ok((sym.to_string(), true));
            }
            return Err(self.err_unsupported(&format!(
                "`\\01` asm-label symbol `{}` does not start with `_`; cannot represent a \
                 no-mangle symbol on Mach-O without a dedicated flag (fail closed)",
                inner
            )));
        }
        Ok((raw_after_at.to_string(), false))
    }

    /// De-mangle a symbol spelling into its canonical name (no origin tracking).
    /// Use at symbol *reference* sites; use `canon_and_note_symbol` at *defining*
    /// or *declaring* sites so collisions are detected.
    fn canon_symbol_name(&self, raw_after_at: &str) -> Result<String> {
        Ok(self.split_asm_label(raw_after_at)?.0)
    }

    /// De-mangle a symbol spelling and record its origin. Fails closed if the
    /// same canonical name is introduced both as a `\01` asm-label and as an
    /// ordinary symbol (they would silently merge into one linker symbol).
    fn canon_and_note_symbol(&mut self, raw_after_at: &str) -> Result<String> {
        let (canon, is_asm_label) = self.split_asm_label(raw_after_at)?;
        match self.symbol_origin.get(&canon) {
            Some(prev) if prev.is_asm_label != is_asm_label => {
                return Err(self.err_unsupported(&format!(
                    "symbol `{}` appears both as a `\\01` asm-label (`@{}`) and as a plain \
                     symbol (`@{}`); ambiguous after de-mangling — fail closed",
                    canon,
                    if is_asm_label {
                        raw_after_at
                    } else {
                        &prev.original
                    },
                    if is_asm_label {
                        &prev.original
                    } else {
                        raw_after_at
                    },
                )));
            }
            _ => {}
        }
        self.symbol_origin
            .entry(canon.clone())
            .or_insert_with(|| SymbolOrigin {
                is_asm_label,
                original: raw_after_at.to_string(),
            });
        Ok(canon)
    }

    fn checked_global_initializer_len(&self, name: &str, byte_len: u64) -> Result<usize> {
        if byte_len > MAX_IMPORTED_GLOBAL_INIT_BYTES {
            return Err(self.err_unsupported(&format!(
                "global @{} initializer is {} byte(s), over importer limit {}",
                name, byte_len, MAX_IMPORTED_GLOBAL_INIT_BYTES
            )));
        }
        usize::try_from(byte_len)
            .map_err(|_| self.err_unsupported("global initializer byte size overflows usize"))
    }

    fn parse_ty_ctx(&self, s: &str) -> Result<Ty> {
        match parse_ty(s) {
            Ok(ty) => Ok(ty),
            Err(Error::Unsupported(_)) if s.trim().starts_with('%') => self
                .struct_layouts
                .contains_key(s.trim())
                .then_some(Ty::Ptr)
                .ok_or_else(|| self.err_unsupported(&format!("type `{}`", s.trim()))),
            Err(e) => Err(e),
        }
    }

    fn parse_fixed_array_layout(&self, s: &str) -> Result<Option<FixedLayout>> {
        let trimmed = s.trim();
        if !trimmed.starts_with('[') {
            return Ok(None);
        }
        self.parse_fixed_layout_ty(trimmed).map(Some)
    }

    fn parse_fixed_layout_ty(&self, s: &str) -> Result<FixedLayout> {
        let trimmed = s.trim();
        if let Some(inner) = trimmed
            .strip_prefix('[')
            .and_then(|tail| tail.strip_suffix(']'))
        {
            let Some((len_str, elem_ty_str)) = inner.split_once(" x ") else {
                return Err(self.err_unsupported(&format!("array type `{}`", trimmed)));
            };
            let len = len_str
                .trim()
                .parse::<usize>()
                .map_err(|_| self.err_unsupported(&format!("array length `{}`", len_str.trim())))?;
            let elem = self.parse_fixed_layout_ty(elem_ty_str.trim())?;
            let len_u64 = u64::try_from(len)
                .map_err(|_| self.err_unsupported("fixed array length overflows u64"))?;
            let size = elem
                .size()
                .checked_mul(len_u64)
                .ok_or_else(|| self.err_unsupported("fixed array byte size overflow"))?;
            let align = elem.align();
            return Ok(FixedLayout::Array {
                len,
                elem: Box::new(elem),
                size,
                align,
            });
        }

        if let Some(inner) = trimmed
            .strip_prefix('{')
            .and_then(|tail| tail.strip_suffix('}'))
        {
            // Anonymous (inline) struct type: lay out its fields exactly, the
            // same way `parse_struct_type_def` handles a named `%struct.foo`.
            let mut fields: Vec<FixedStructField> = Vec::new();
            let mut offset = 0u64;
            let mut struct_align = 1u64;
            let inner = inner.trim();
            if !inner.is_empty() {
                for field_str in split_aggregate_elems(inner) {
                    let field_layout = self.parse_fixed_layout_ty(field_str.trim())?;
                    let field_align = field_layout.align();
                    let field_size = field_layout.size();
                    offset = align_up(offset, field_align);
                    fields.push(FixedStructField {
                        layout: field_layout,
                        offset,
                    });
                    offset += field_size;
                    struct_align = struct_align.max(field_align);
                }
            }
            return Ok(FixedLayout::Struct {
                fields,
                size: align_up(offset, struct_align),
                align: struct_align,
            });
        }

        if trimmed.starts_with('%') {
            let layout = self
                .struct_layouts
                .get(trimmed)
                .ok_or_else(|| self.err_unsupported(&format!("type `{}`", trimmed)))?;
            let fields = layout
                .fields
                .iter()
                .map(|(ty, offset)| FixedStructField {
                    layout: FixedLayout::Scalar(ty.clone()),
                    offset: *offset,
                })
                .collect();
            return Ok(FixedLayout::Struct {
                fields,
                size: layout.size,
                align: layout.align,
            });
        }

        let ty = parse_ty(trimmed)?;
        scalar_layout(&ty)
            .map(|_| FixedLayout::Scalar(ty))
            .ok_or_else(|| {
                self.err_unsupported(&format!("fixed aggregate element type `{}`", trimmed))
            })
    }

    fn parse(&mut self) -> Result<()> {
        // Snapshot lines so we can iterate with look-ahead for function
        // bodies without fighting the borrow checker. Strip comments and
        // metadata attachments up front.
        let lines: Vec<(usize, String)> = self
            .lines
            .iter()
            .enumerate()
            .map(|(i, l)| (i + 1, strip_line(l)))
            .collect();

        for (_, raw) in &lines {
            let line = raw.trim();
            if let Some((group, attrs)) = parse_attribute_group(line) {
                self.attribute_groups.insert(group, attrs);
            }
        }

        // Pre-pass: resolve struct type definitions with a fixpoint, so a struct
        // whose field is a LATER-defined named struct (a forward reference, which
        // LLVM does not topologically order) lays out correctly. Each round
        // resolves every def whose dependencies are already known; C aggregates
        // never contain themselves by value, so there are no cycles and the
        // iteration terminates. Defs that never resolve are left for the main
        // pass to report (fail-closed) when their `= type` line is reached.
        let mut pending: Vec<(usize, String)> = lines
            .iter()
            .map(|(ln, raw)| (*ln, raw.trim().to_string()))
            .filter(|(_, l)| l.starts_with('%') && l.contains("= type"))
            .collect();
        while !pending.is_empty() {
            let before = pending.len();
            pending.retain(|(ln, line)| self.parse_struct_type_def(line, *ln).is_err());
            if pending.len() == before {
                break;
            }
        }

        // Name-only pre-scan: record every symbol DEFINED/DECLARED in the module
        // (data globals + functions) so an initializer that names a symbol
        // defined LATER in the file resolves, and a typo fails closed.
        for (_, raw) in &lines {
            let line = raw.trim();
            if let Some(name) = scan_defined_symbol_name(line)
                && let Ok(canon) = self.canon_symbol_name(name)
            {
                self.known_symbol_names.insert(canon);
            }
        }

        let mut i = 0;
        while i < lines.len() {
            let (lineno, raw) = &lines[i];
            let line = raw.trim();
            if line.is_empty() {
                i += 1;
                continue;
            }
            if line.starts_with("target ") || line.starts_with("source_filename") {
                // Informational only.
                i += 1;
                continue;
            }
            if line.starts_with("module asm") {
                return Err(self.err_unsupported("inline module asm"));
            }
            if line.starts_with("attributes ") {
                // attribute group decl — ignore.
                i += 1;
                continue;
            }
            if line.starts_with('!') {
                // Metadata definition — ignore.
                i += 1;
                continue;
            }
            if line.starts_with('@') {
                self.parse_global(line, *lineno)?;
                i += 1;
                continue;
            }
            if line.starts_with("declare") {
                self.parse_declare(line, *lineno)?;
                i += 1;
                continue;
            }
            if line.starts_with("define") {
                // Consume the define ... { line plus the body up to the
                // matching closing `}`.
                let (end, body) = collect_function_body(&lines, i, *lineno)?;
                self.parse_define(line, &body, *lineno)?;
                i = end + 1;
                continue;
            }
            if line.starts_with('%') && line.contains("= type") {
                self.parse_struct_type_def(line, *lineno)?;
                i += 1;
                continue;
            }
            // Unknown top-level line; most commonly `%struct.X = type ...`
            if line.contains("= type") {
                return Err(self.err_unsupported("named struct types"));
            }
            return Err(self.err_parse(*lineno, &format!("unexpected top-level line: {}", line)));
        }

        self.apply_libm_purity_licenses();

        Ok(())
    }

    /// Finalize the libm purity licensing (loop-dead-pure-sink plumbing).
    ///
    /// A libm symbol (e.g. `asin`) synthesized by the `llvm.<fn>.fN` intrinsic
    /// rewrite is licensed pure — its bodyless external declaration gets
    /// `ProofAnnotation::Custom(LLVM_LIBM_PURE_FUNCTION_ATTR_TAG)` — only when
    /// ALL of the following hold (every leg fail-closed):
    ///
    ///  1. every `declare` of the ORIGIN intrinsic carried the full pure-math
    ///     attribute set `speculatable willreturn nounwind memory(none)`
    ///     (the license authority: LLVM's own errno-free intrinsic contract);
    ///  2. the module contains NO other reference to the libm symbol — no
    ///     plain direct call, no address-taken use, no pointer-table entry
    ///     (a user-supplied impure `asin` can therefore never be licensed);
    ///  3. the symbol resolves to a BODYLESS EXTERNAL function stub in the
    ///     module (never a defined body, never a data global).
    ///
    /// Runs after the whole module is parsed so late declares/uses are seen.
    fn apply_libm_purity_licenses(&mut self) {
        let plain_uses = self.libm_plain_uses.borrow();
        for (libm_sym, intrinsic_name) in &self.libm_rewritten_calls {
            let intrinsic_licensed = self
                .libm_intrinsic_decl_pure
                .get(intrinsic_name)
                .copied()
                .unwrap_or(false);
            if !intrinsic_licensed {
                continue;
            }
            if plain_uses.contains(libm_sym) {
                continue;
            }
            if self.globals.contains_key(libm_sym) {
                continue;
            }
            let Some(func) = self
                .module
                .functions
                .iter_mut()
                .find(|func| func.name == *libm_sym)
            else {
                continue;
            };
            // Bodyless external stub only — a defined body is the user's own
            // function and must never be licensed.
            if !func.blocks.is_empty() || !matches!(func.linkage, Linkage::External) {
                continue;
            }
            push_unique_proof(
                &mut func.proofs,
                ProofAnnotation::Custom(ProofTag::new(LLVM_LIBM_PURE_FUNCTION_ATTR_TAG)),
            );
        }
    }

    // --- Globals -----------------------------------------------------------

    fn parse_struct_type_def(&mut self, line: &str, lineno: usize) -> Result<()> {
        let (name, rest) = split_eq(line).ok_or_else(|| self.err_parse(lineno, "bad type def"))?;
        let name = name.trim();
        if !name.starts_with('%') {
            return Err(self.err_unsupported("named type definition without `%name`"));
        }

        let body = rest
            .trim()
            .strip_prefix("type")
            .ok_or_else(|| self.err_parse(lineno, "type def missing `type` keyword"))?
            .trim();

        if !body.starts_with('{') || !body.ends_with('}') {
            return Err(self.err_unsupported(&format!(
                "named type `{}` with non-struct body `{}`",
                name, body
            )));
        }

        let inner = &body[1..body.len() - 1];
        let mut fields = Vec::new();
        let mut offset = 0u64;
        let mut struct_align = 1u64;
        if !inner.trim().is_empty() {
            for field_str in split_call_args(inner) {
                let fs = field_str.trim();
                // Fields may be scalars, arrays (`[N x T]`) or earlier-defined
                // named aggregates (`%struct.X`). `parse_fixed_layout_ty`
                // computes the exact size/align for all three per the Apple
                // arm64 ABI, so nested-aggregate structs lay out correctly.
                let field_layout = self.parse_fixed_layout_ty(fs)?;
                let field_size = field_layout.size();
                let field_align = field_layout.align();
                offset = align_up(offset, field_align);
                // The stored `Ty` is only consulted for scalar fields (struct
                // GEP reads the offset, not the type; the total struct size is
                // tracked in `size` below). An aggregate field keeps an `i8`
                // placeholder — a field-precise GEP into it is a separate,
                // independently-guarded path.
                let field_ty = match &field_layout {
                    FixedLayout::Scalar(t) => t.clone(),
                    _ => Ty::I8,
                };
                fields.push((field_ty, offset));
                offset += field_size;
                struct_align = struct_align.max(field_align);
            }
        }

        let layout = StructLayout {
            fields,
            size: align_up(offset, struct_align),
            align: struct_align,
        };
        self.struct_layouts.insert(name.to_string(), layout);
        Ok(())
    }

    fn parse_string_global(
        &mut self,
        name: String,
        rest: &str,
        lineno: usize,
        mutable: bool,
        linkage: Linkage,
        align: Option<u32>,
    ) -> Result<()> {
        let ty_start = rest
            .find('[')
            .ok_or_else(|| self.err_unsupported("global without [N x T] type"))?;
        let ty_end = rest[ty_start..]
            .find(']')
            .ok_or_else(|| self.err_parse(lineno, "unterminated global type"))?;
        let ty_body = &rest[ty_start + 1..ty_start + ty_end];
        // `find(']')` returns the FIRST `]`. For a top-level `[N x i8]` that is
        // the matching bracket, but for a nested aggregate like
        // `[3 x { i32, [10 x i8], ... }]` it closes the INNER array, leaving
        // `ty_body = "3 x { i32, [10 x i8"`. That still contains "x i8", so the
        // old check would wrongly treat the whole struct-array as a string and
        // decode the first embedded `c"..."` as the entire global image — a
        // miscompile. If the extracted body contains any `[`/`{`, the first `]`
        // was NOT the outer bracket: fail closed.
        if ty_body.contains('[') || ty_body.contains('{') {
            return Err(self.err_unsupported(&format!(
                "aggregate global @{} with embedded string (not a top-level [N x i8])",
                name
            )));
        }
        // A genuine string global's body is exactly `N x i8`.
        let is_byte_array = ty_body.split_once(" x ").is_some_and(|(len, elem)| {
            !len.trim().is_empty()
                && len.trim().bytes().all(|b| b.is_ascii_digit())
                && elem.trim() == "i8"
        });
        if !is_byte_array {
            return Err(self.err_unsupported(&format!(
                "non-string global @{} (type [{}] not [N x i8])",
                name, ty_body
            )));
        }

        let init_start = rest[ty_start + ty_end..]
            .find("c\"")
            .ok_or_else(|| self.err_unsupported("global with non-c-string initializer"))?;
        let init_tail = &rest[ty_start + ty_end + init_start + 2..];
        let close = find_ll_string_end(init_tail)
            .ok_or_else(|| self.err_parse(lineno, "unterminated c-string"))?;
        let raw = &init_tail[..close];
        let bytes = decode_ll_string(raw);
        self.checked_global_initializer_len(&name, bytes.len() as u64)?;

        let elems: Vec<Constant> = bytes.iter().map(|b| Constant::Int(*b as i128)).collect();
        let idx = self.module.globals.len();
        self.module.globals.push(Global {
            name: name.clone(),
            ty: Ty::Ptr,
            mutable,
            initializer: Some(Constant::Aggregate(elems)),
            linkage,
            tls: None,
            align,
        });
        self.globals.insert(name, idx);
        Ok(())
    }

    fn parse_scalar_global_initializer(&self, ty: &Ty, tok: &str) -> Result<Constant> {
        let tok = tok.trim();
        match ty {
            Ty::Bool => {
                // A Bool (i1) global must carry a Bool initializer — the codegen
                // global tree rejects a scalar-integer initializer on a Bool
                // global (it needs the typed Bool form for endian emission).
                let b = match tok {
                    "zeroinitializer" | "null" | "false" => false,
                    "true" => true,
                    _ => match parse_int_literal(tok) {
                        Some(0) => false,
                        Some(1) => true,
                        _ => {
                            return Err(
                                self.err_unsupported(&format!("bool global initializer `{}`", tok))
                            );
                        }
                    },
                };
                Ok(Constant::Bool(b))
            }
            Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 => {
                if tok == "zeroinitializer" || tok == "null" {
                    return Ok(Constant::Int(0));
                }
                parse_int_literal(tok).map(Constant::Int).ok_or_else(|| {
                    self.err_unsupported(&format!("scalar global initializer `{}`", tok))
                })
            }
            Ty::F16 | Ty::F32 | Ty::F64 => {
                if tok == "zeroinitializer" {
                    return Ok(Constant::Float(0.0));
                }
                match parse_fp_literal(tok).ok_or_else(|| {
                    self.err_unsupported(&format!("scalar global initializer `{}`", tok))
                })? {
                    FpLit::Double(d) | FpLit::Half(d) => Ok(Constant::Float(d)),
                    FpLit::Extended(tag) => Err(self.err_unsupported(&format!(
                        "extended-precision float literal `0x{}...` (trust_ir only has f16/f32/f64)",
                        tag
                    ))),
                }
            }
            Ty::Ptr => {
                if tok == "null" || tok == "zeroinitializer" {
                    Ok(Constant::Int(0))
                } else {
                    Err(self.err_unsupported(&format!("pointer global initializer `{}`", tok)))
                }
            }
            _ => Err(self.err_unsupported(&format!(
                "non-scalar global initializer for type `{:?}`",
                ty
            ))),
        }
    }

    /// Serialize a typed constant `<ty> <value>` into its little-endian byte
    /// image, appended to `out`, laying out nested structs/arrays exactly per
    /// the Apple arm64 ABI (padding between fields, trailing tail padding). Used
    /// for explicit aggregate global initializers. Any construct without an
    /// exact byte image — a pointer to a symbol (needs a relocation), an f16
    /// field, an unsupported type — fails CLOSED; the importer never guesses a
    /// layout.
    fn serialize_typed_const(&self, s: &str, out: &mut Vec<u8>) -> Result<()> {
        let (ty_str, value) = split_leading_type(s.trim()).ok_or_else(|| {
            self.err_unsupported(&format!("aggregate initializer element `{}`", s.trim()))
        })?;
        let layout = self.parse_fixed_layout_ty(ty_str)?;
        let start = out.len();
        let want_end = start + layout.size() as usize;

        if value == "zeroinitializer" {
            out.resize(want_end, 0);
            return Ok(());
        }

        match &layout {
            FixedLayout::Scalar(ty) => {
                let bytes = self.le_bytes_of_scalar(ty, value)?;
                out.extend_from_slice(&bytes);
            }
            FixedLayout::Array { len, .. } => {
                if let Some(rest) = value.strip_prefix("c\"") {
                    let close = find_ll_string_end(rest).ok_or_else(|| {
                        self.err_unsupported("unterminated c-string in aggregate initializer")
                    })?;
                    out.extend_from_slice(&decode_ll_string(&rest[..close]));
                } else if let Some(inner) =
                    value.strip_prefix('[').and_then(|v| v.strip_suffix(']'))
                {
                    let elems = split_aggregate_elems(inner);
                    if elems.len() != *len {
                        return Err(self.err_unsupported(
                            "array initializer element count does not match type length",
                        ));
                    }
                    for e in &elems {
                        self.serialize_typed_const(e, out)?;
                    }
                } else {
                    return Err(
                        self.err_unsupported(&format!("array initializer form `{}`", value))
                    );
                }
            }
            FixedLayout::Struct { fields, .. } => {
                let inner = value
                    .strip_prefix('{')
                    .and_then(|v| v.strip_suffix('}'))
                    .ok_or_else(|| self.err_unsupported("struct initializer must be `{...}`"))?;
                let field_inits = split_aggregate_elems(inner.trim());
                if field_inits.len() != fields.len() {
                    return Err(
                        self.err_unsupported("struct initializer field count does not match type")
                    );
                }
                for (field, init) in fields.iter().zip(field_inits.iter()) {
                    // Pad up to this field's offset, then serialize it.
                    out.resize(start + field.offset as usize, 0);
                    self.serialize_typed_const(init, out)?;
                }
            }
        }

        // Overwriting is a bug; under-filling (e.g. array/struct tail) pads with
        // zeros to the exact ABI size. A byte image longer than the layout means
        // we mis-parsed — fail closed rather than emit a wrong global.
        if out.len() > want_end {
            return Err(self.err_unsupported("aggregate initializer overran its type size"));
        }
        out.resize(want_end, 0);
        Ok(())
    }

    /// The little-endian byte image of a scalar constant `value` of type `ty`.
    fn le_bytes_of_scalar(&self, ty: &Ty, value: &str) -> Result<Vec<u8>> {
        let value = value.trim();
        match ty {
            Ty::Bool | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 => {
                let width = match ty {
                    Ty::Bool | Ty::I8 => 1usize,
                    Ty::I16 => 2,
                    Ty::I32 => 4,
                    Ty::I64 => 8,
                    Ty::I128 => 16,
                    _ => unreachable!(),
                };
                let v: i128 = match value {
                    "zeroinitializer" | "null" | "false" => 0,
                    "true" => 1,
                    other => parse_int_literal(other).ok_or_else(|| {
                        self.err_unsupported(&format!("integer aggregate field `{}`", other))
                    })?,
                };
                let u = v as u128;
                Ok((0..width).map(|i| (u >> (i * 8)) as u8).collect())
            }
            Ty::F32 => {
                let d = self.aggregate_float_bits(value)?;
                Ok((d as f32).to_bits().to_le_bytes().to_vec())
            }
            Ty::F64 => {
                let d = self.aggregate_float_bits(value)?;
                Ok(d.to_bits().to_le_bytes().to_vec())
            }
            Ty::F16 => Err(self.err_unsupported("f16 aggregate field (no exact byte image yet)")),
            Ty::Ptr => {
                if value == "null" || value == "zeroinitializer" {
                    Ok(vec![0u8; 8])
                } else {
                    // `ptr @sym` needs a relocation in the initializer image.
                    Err(self.err_unsupported(&format!("pointer aggregate field `{}`", value)))
                }
            }
            other => Err(self.err_unsupported(&format!("aggregate field type `{:?}`", other))),
        }
    }

    fn aggregate_float_bits(&self, value: &str) -> Result<f64> {
        match parse_fp_literal(value)
            .ok_or_else(|| self.err_unsupported(&format!("float aggregate field `{}`", value)))?
        {
            FpLit::Double(d) | FpLit::Half(d) => Ok(d),
            FpLit::Extended(tag) => Err(self.err_unsupported(&format!(
                "extended-precision float aggregate field `0x{}...`",
                tag
            ))),
        }
    }

    /// Serialize an explicit aggregate global initializer (`%struct.foo { ... }`
    /// or `[N x T] [ ... ]`) — given as the full `<type> <value>` string — into
    /// its byte image, bounded by the module byte-size limit.
    fn serialize_named_aggregate_global(
        &self,
        name: &str,
        typed_init: &str,
    ) -> Result<Vec<Constant>> {
        let mut bytes = Vec::new();
        self.serialize_typed_const(typed_init, &mut bytes)?;
        self.checked_global_initializer_len(name, bytes.len() as u64)?;
        Ok(bytes
            .into_iter()
            .map(|b| Constant::Int(b as i128))
            .collect())
    }

    /// Serialize a `[N x ptr] [ptr @a, ptr @b, ..., ptr null]` global — an array
    /// of pointers to module symbols (a string/function pointer table) — into a
    /// flat `Constant::Aggregate` the codegen data-emitter turns into a byte
    /// image plus per-slot relocations:
    ///   * `ptr @sym`          -> one `SymbolAddr` element (8 bytes + relocation)
    ///   * `ptr null`/`zeroinitializer` -> 8 zero `Int` bytes (a null pointer)
    ///     Every referenced `@sym` must be a KNOWN module symbol (global or function)
    ///     — verified against the name pre-scan so a forward reference resolves and a
    ///     typo fails closed instead of fabricating a relocation.
    fn parse_pointer_array_global_initializer(
        &self,
        name: &str,
        len: usize,
        value_str: &str,
    ) -> Result<Vec<Constant>> {
        let value_str = value_str.trim();
        let inner = value_str
            .strip_prefix('[')
            .and_then(|tail| tail.strip_suffix(']'))
            .ok_or_else(|| {
                self.err_unsupported(&format!(
                    "pointer array global @{} initializer `{}`",
                    name, value_str
                ))
            })?;
        let items = split_call_args(inner);
        if items.len() != len {
            return Err(self.err_unsupported(&format!(
                "pointer array global @{} length mismatch: type has {}, initializer has {}",
                name,
                len,
                items.len()
            )));
        }
        // Bound the total size (N pointers * 8 bytes) by the module limit.
        let byte_len = (len as u64)
            .checked_mul(8)
            .ok_or_else(|| self.err_unsupported("pointer array global byte size overflow"))?;
        self.checked_global_initializer_len(name, byte_len)?;

        let mut elems: Vec<Constant> = Vec::with_capacity(len);
        for item in items {
            let (elem_ty_str, val) = split_ty_operand(&item)?;
            let elem_ty = parse_ty(&elem_ty_str)?;
            if !matches!(elem_ty, Ty::Ptr) {
                return Err(self.err_unsupported(&format!(
                    "pointer array global @{} element type `{}` (expected ptr)",
                    name, elem_ty_str
                )));
            }
            let val = val.trim();
            if val == "null" || val == "zeroinitializer" {
                // A null pointer: 8 little-endian zero bytes.
                elems.extend(std::iter::repeat_n(Constant::Int(0), 8));
            } else if let Some(sym) = val.strip_prefix('@') {
                let canon = self.canon_symbol_name(sym)?;
                if !self.known_symbol_names.contains(&canon) {
                    return Err(self.err_unsupported(&format!(
                        "pointer array global @{} references undeclared symbol `@{}`",
                        name, canon
                    )));
                }
                // Pointer-table reference: disqualifies the symbol from the
                // libm-pure license (fail-closed).
                self.libm_plain_uses.borrow_mut().insert(canon.clone());
                elems.push(Constant::SymbolAddr {
                    symbol: canon,
                    addend: 0,
                });
            } else {
                // Anything else (inline `getelementptr` const-expr, an integer
                // cast to ptr, …) has no simple relocation form here — fail closed.
                return Err(self.err_unsupported(&format!(
                    "pointer array global @{} element `{}` (only `ptr @sym` or `ptr null`)",
                    name, val
                )));
            }
        }
        Ok(elems)
    }

    fn parse_explicit_integer_array_global_initializer(
        &self,
        name: &str,
        len: usize,
        elem_ty: &Ty,
        value_str: &str,
    ) -> Result<Vec<Constant>> {
        let bits = explicit_integer_array_elem_bits(elem_ty).ok_or_else(|| {
            self.err_unsupported(&format!(
                "explicit integer array global @{} element type `{:?}`",
                name, elem_ty
            ))
        })?;
        let value_str = value_str.trim();
        let Some(inner) = value_str
            .strip_prefix('[')
            .and_then(|tail| tail.strip_suffix(']'))
        else {
            return Err(self.err_unsupported(&format!(
                "explicit integer array global @{} initializer `{}`",
                name, value_str
            )));
        };

        let items = split_call_args(inner);
        if items.len() != len {
            return Err(self.err_unsupported(&format!(
                "explicit integer array global @{} length mismatch: type has {}, initializer has {}",
                name,
                len,
                items.len()
            )));
        }

        let bytes_per_elem = (bits / 8) as usize;
        let byte_len = len.checked_mul(bytes_per_elem).ok_or_else(|| {
            self.err_unsupported("explicit integer array global byte size overflow")
        })?;
        let byte_len_u64 = u64::try_from(byte_len).map_err(|_| {
            self.err_unsupported("explicit integer array global byte size overflows u64")
        })?;
        self.checked_global_initializer_len(name, byte_len_u64)?;
        let mut bytes = Vec::with_capacity(byte_len);
        for item in items {
            let (item_ty_str, literal_str) = split_ty_operand(&item)?;
            let item_ty = parse_ty(&item_ty_str)?;
            if &item_ty != elem_ty {
                return Err(self.err_unsupported(&format!(
                    "explicit integer array global @{} element type `{}` does not match `{}`",
                    name,
                    item_ty_str,
                    format_ty_for_array_error(elem_ty)
                )));
            }
            let value = parse_int_literal(&literal_str).ok_or_else(|| {
                self.err_unsupported(&format!(
                    "explicit integer array global @{} element literal `{}`",
                    name, literal_str
                ))
            })?;
            let value_bytes =
                integer_literal_to_le_byte_constants(value, bits).ok_or_else(|| {
                    self.err_unsupported(&format!(
                    "explicit integer array global @{} element literal `{}` out of range for `{}`",
                    name,
                    literal_str,
                    format_ty_for_array_error(elem_ty)
                ))
                })?;
            bytes.extend(value_bytes);
        }
        Ok(bytes)
    }

    fn parse_global(&mut self, line: &str, lineno: usize) -> Result<()> {
        let (name, rest) = split_eq(line).ok_or_else(|| self.err_parse(lineno, "bad global"))?;
        // De-mangle the `\01` asm-label escape (verbatim symbol) if present, and
        // record the symbol's origin so a later collision fails closed.
        let name = self.canon_and_note_symbol(name.trim_start_matches('@').trim())?;
        let lower = rest.to_lowercase();
        let linkage = parse_linkage(&lower);
        let (mutable, after_storage) = split_global_storage(rest).ok_or_else(|| {
            self.err_unsupported(&format!(
                "global @{} without `global`/`constant` storage class",
                name
            ))
        })?;
        let align = self.parse_global_alignment(after_storage)?;

        let init_part_buf = split_comma(after_storage)
            .map(|(head, _)| head)
            .unwrap_or_else(|| after_storage.trim().to_string());
        let init_part = init_part_buf.trim();
        if after_storage.trim_start().starts_with('[')
            && let Ok((ty_str, value_str)) = split_ty_operand(init_part)
            && let Some(layout) = self.parse_fixed_array_layout(&ty_str)?
        {
            let value = value_str.trim();
            // A genuine top-level `[N x i8] c"..."` byte-string global.
            if layout.is_top_i8_array() && value.starts_with("c\"") {
                return self.parse_string_global(name, rest, lineno, mutable, linkage, align);
            }
            if value != "zeroinitializer" {
                // A scalar-INTEGER-element array keeps its dedicated
                // element-wise path; everything else (arrays of floats,
                // structs, nested arrays, or with embedded strings) is
                // serialized to an exact byte image.
                if let Some((len, elem_ty)) = layout.top_array_scalar_elem() {
                    if is_integer_ty(elem_ty) {
                        let elems = self.parse_explicit_integer_array_global_initializer(
                            &name, len, elem_ty, value,
                        )?;
                        let idx = self.module.globals.len();
                        self.module.globals.push(Global {
                            name: name.clone(),
                            ty: Ty::Ptr,
                            mutable,
                            initializer: Some(Constant::Aggregate(elems)),
                            linkage,
                            tls: None,
                            align,
                        });
                        self.globals.insert(name, idx);
                        return Ok(());
                    }
                    // `[N x ptr] [ptr @a, ptr @b, ...]` — an array of
                    // pointers to module symbols (a string/function table,
                    // e.g. fbench's `@refarr`). Each element is a
                    // pointer-width relocation, not a byte image, so it
                    // needs the structured `SymbolAddr`/zero-slot form the
                    // codegen data-emitter turns into relocations.
                    if matches!(elem_ty, Ty::Ptr) {
                        let elems =
                            self.parse_pointer_array_global_initializer(&name, len, value)?;
                        let idx = self.module.globals.len();
                        self.module.globals.push(Global {
                            name: name.clone(),
                            ty: Ty::Ptr,
                            mutable,
                            initializer: Some(Constant::Aggregate(elems)),
                            linkage,
                            tls: None,
                            align,
                        });
                        self.globals.insert(name, idx);
                        return Ok(());
                    }
                }
                let bytes = self.serialize_named_aggregate_global(&name, init_part)?;
                let idx = self.module.globals.len();
                self.module.globals.push(Global {
                    name: name.clone(),
                    ty: Ty::Ptr,
                    mutable,
                    initializer: Some(Constant::Aggregate(bytes)),
                    linkage,
                    tls: None,
                    align,
                });
                self.globals.insert(name, idx);
                return Ok(());
            }
            if !layout.supported_zero_global() {
                if let Some((_, elem_ty)) = layout.top_array_scalar_elem()
                    && elem_ty != &Ty::I8
                {
                    return Err(self.err_unsupported(&format!(
                        "non-byte zero array global @{} (type `{}`)",
                        name, ty_str
                    )));
                }
                return Err(self.err_unsupported(&format!(
                    "unsupported zero fixed aggregate global @{} (type `{}`)",
                    name, ty_str
                )));
            }
            let byte_len = self.checked_global_initializer_len(&name, layout.size())?;
            let idx = self.module.globals.len();
            self.module.globals.push(Global {
                name: name.clone(),
                ty: Ty::Ptr,
                mutable,
                initializer: Some(Constant::Aggregate(vec![Constant::Int(0); byte_len])),
                linkage,
                tls: None,
                align,
            });
            self.globals.insert(name, idx);
            return Ok(());
        }
        // Named aggregate (struct / union) global: `@g = global %struct.foo
        // <init>`. LLVM lowers a union to a struct sized to its widest member.
        if init_part.starts_with('%') {
            let type_tok = init_part
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_string();
            if self.struct_layouts.contains_key(&type_tok) {
                let layout = self.parse_fixed_layout_ty(&type_tok)?;
                let init_val = init_part[type_tok.len()..].trim();
                if init_val == "zeroinitializer" {
                    // A zero image is exactly `size()` zero bytes, layout-independent.
                    let byte_len = self.checked_global_initializer_len(&name, layout.size())?;
                    let idx = self.module.globals.len();
                    self.module.globals.push(Global {
                        name: name.clone(),
                        ty: Ty::Ptr,
                        mutable,
                        initializer: Some(Constant::Aggregate(vec![Constant::Int(0); byte_len])),
                        linkage,
                        tls: None,
                        align,
                    });
                    self.globals.insert(name, idx);
                    return Ok(());
                }
                // Explicit `{ ... }` initializer: serialize the field values into
                // the struct's exact byte image.
                let bytes = self.serialize_named_aggregate_global(&name, init_part)?;
                let idx = self.module.globals.len();
                self.module.globals.push(Global {
                    name: name.clone(),
                    ty: Ty::Ptr,
                    mutable,
                    initializer: Some(Constant::Aggregate(bytes)),
                    linkage,
                    tls: None,
                    align,
                });
                self.globals.insert(name, idx);
                return Ok(());
            }
        }
        if let Ok(ty) = parse_ty(init_part) {
            if !is_scalar_global_ty(&ty) {
                return Err(self.err_unsupported(&format!(
                    "non-scalar global @{} (type `{}`)",
                    name, init_part
                )));
            }
            let idx = self.module.globals.len();
            self.module.globals.push(Global {
                name: name.clone(),
                ty,
                mutable,
                initializer: None,
                linkage,
                tls: None,
                align,
            });
            self.globals.insert(name, idx);
            return Ok(());
        }
        if init_part.starts_with('[') && !init_part.contains(" c\"") {
            return Err(self.err_unsupported(&format!(
                "non-scalar global @{} (type `{}`)",
                name, init_part
            )));
        }

        if after_storage.trim_start().starts_with('[') {
            return self.parse_string_global(name, rest, lineno, mutable, linkage, align);
        }

        let (ty_str, value_str) = split_ty_operand(init_part)?;
        let ty = parse_ty(&ty_str)?;
        if !is_scalar_global_ty(&ty) {
            return Err(
                self.err_unsupported(&format!("non-scalar global @{} (type `{}`)", name, ty_str))
            );
        }
        let initializer = self.parse_scalar_global_initializer(&ty, &value_str)?;
        // A pointer global (only `null`/`zeroinitializer` reach here) is a
        // pointer-sized zero image. Emit it as 8 zero bytes — the codegen
        // global tree rejects an integer initializer on a `Ptr`-typed global,
        // but accepts the byte-aggregate form used for every other zero global.
        if matches!(ty, Ty::Ptr) {
            let idx = self.module.globals.len();
            self.module.globals.push(Global {
                name: name.clone(),
                ty: Ty::Ptr,
                mutable,
                initializer: Some(Constant::Aggregate(vec![Constant::Int(0); 8])),
                linkage,
                tls: None,
                align,
            });
            self.globals.insert(name, idx);
            return Ok(());
        }
        if lower.contains("common")
            && let Some(elems) = scalar_integer_global_to_le_byte_constants(&ty, &initializer)
        {
            let idx = self.module.globals.len();
            self.module.globals.push(Global {
                name: name.clone(),
                ty: Ty::Ptr,
                mutable,
                initializer: Some(Constant::Aggregate(elems)),
                linkage,
                tls: None,
                align,
            });
            self.globals.insert(name, idx);
            return Ok(());
        }
        let idx = self.module.globals.len();
        self.module.globals.push(Global {
            name: name.clone(),
            ty,
            mutable,
            initializer: Some(initializer),
            linkage,
            tls: None,
            align,
        });
        self.globals.insert(name, idx);
        Ok(())
    }

    fn parse_global_alignment(&self, after_storage: &str) -> Result<Option<u32>> {
        let mut align = None;
        for attribute in split_aggregate_elems(after_storage).into_iter().skip(1) {
            let Some(raw) = attribute.trim().strip_prefix("align ") else {
                continue;
            };
            let mut tokens = raw.split_whitespace();
            let value = tokens
                .next()
                .and_then(|token| token.parse::<u32>().ok())
                .filter(|value| *value != 0 && value.is_power_of_two())
                .ok_or_else(|| {
                    self.err_unsupported(&format!(
                        "global alignment `{}` (expected a nonzero power-of-two u32)",
                        raw
                    ))
                })?;
            if tokens.next().is_some() {
                return Err(self.err_unsupported(&format!(
                    "global alignment `{}` (unexpected trailing tokens)",
                    raw
                )));
            }
            if align.replace(value).is_some() {
                return Err(self.err_unsupported("global with duplicate alignment attributes"));
            }
        }
        Ok(align)
    }

    // --- Declare / define --------------------------------------------------

    fn parse_declare(&mut self, line: &str, lineno: usize) -> Result<()> {
        let sig = parse_function_signature(
            line,
            lineno,
            /*is_define=*/ false,
            &self.attribute_groups,
        );
        let mut sig = match sig {
            Ok(sig) => sig,
            // A `declare` is a SIGNATURE ANNOUNCEMENT with no semantics of its
            // own, so a declaration whose types the importer does not model is
            // simply not registered instead of killing the module. This is
            // fail-closed, not permissive: an unregistered callee cannot be
            // called silently — `parse_call` still has to type every argument
            // and result at the CALL SITE, and the `@llvm.*` classifier still
            // rejects any intrinsic without a modelled lowering. It matters
            // because clang emits `declare <4 x double> @llvm.fmuladd.v4f64(…)`
            // for intrinsics the lane expander rewrites away entirely, so the
            // declaration describes a function the module never calls.
            //
            // The libm purity license reads `unwrap_or(false)` per intrinsic,
            // so a skipped declaration REVOKES the license rather than granting
            // one — the conservative direction.
            Err(Error::Unsupported(_)) => return Ok(()),
            Err(e) => return Err(e),
        };
        // De-mangle a `\01` asm-label callee name (e.g. `declare @"\01_fopen"`)
        // and record its origin so a later plain-`@fopen` collision fails closed.
        sig.name = self.canon_and_note_symbol(&sig.name)?;
        // `llvm.mem{cpy,move,set}.*` declares carry the trailing
        // `i1 <volatile>` parameter. Call sites DROP the literal-false flag
        // (see the call-argument normalization) so the registered signature
        // must match the 3-parameter `(dest, src|val, len)` form the
        // adapter/ISel contract expects — strip the trailing Bool here.
        // Volatile-true call sites fail closed at the call, so the dropped
        // parameter can never carry information.
        if ["llvm.memcpy.", "llvm.memmove.", "llvm.memset."]
            .iter()
            .any(|p| sig.name.starts_with(p))
            && sig.params.len() == 4
        {
            sig.params.pop();
        }
        // Libm purity licensing: record whether this libm intrinsic's declared
        // attribute set carries the full pure-math license. Merged with AND so
        // a duplicate declare WITHOUT the attrs revokes the license.
        if sig.name.starts_with("llvm.") && libm_intrinsic_symbol(&sig.name).is_some() {
            let licensed = sig.libm_pure_math;
            self.libm_intrinsic_decl_pure
                .entry(sig.name.clone())
                .and_modify(|prior| *prior = *prior && licensed)
                .or_insert(licensed);
        }
        let fid = self.register_function(sig.clone())?;
        if !self.module.functions.iter().any(|func| func.id == fid) {
            let mut func = Function::new(
                fid,
                sig.name.clone(),
                self.func_tys[&sig.name],
                BlockId::new(0),
            );
            func.calling_conv = CallingConv::C;
            func.linkage = Linkage::External;
            apply_function_attributes(&mut func, &sig);
            self.module.add_function(func);
        }
        Ok(())
    }

    fn parse_define(
        &mut self,
        header: &str,
        body: &[(usize, String)],
        lineno: usize,
    ) -> Result<()> {
        // Strip trailing "{" from header.
        let header = header.trim_end_matches('{').trim();
        let mut sig = parse_function_signature(
            header,
            lineno,
            /*is_define=*/ true,
            &self.attribute_groups,
        )?;
        // De-mangle a `\01` asm-label on the defined function's own name.
        sig.name = self.canon_and_note_symbol(&sig.name)?;
        let fid = self.register_function(sig.clone())?;
        let existing_placeholder = self
            .module
            .functions
            .iter()
            .position(|function| function.id == fid);
        if existing_placeholder.is_some_and(|index| !self.module.functions[index].blocks.is_empty())
        {
            return Err(self.err_parse(
                lineno,
                &format!("multiple definitions of function `@{}`", sig.name),
            ));
        }

        // Walk the body, assigning ValueIds and BlockIds.
        let mut scratch = FuncScratch::new();

        // NATIVE VECTOR PLAN. Decide, over the WHOLE body and before a single
        // instruction is emitted, which vector SSA values are carried as one
        // 128-bit value instead of as scalar lanes. It has to be a whole-body
        // decision: a value's representation is fixed at its definition, but
        // whether that representation pays depends on its CONSUMERS, which the
        // line-at-a-time walk below has not seen yet.
        scratch.native_plan = crate::native_vector::plan_function(
            &native_vector_plan_input(body),
            !vector_import_disabled() && !crate::native_vector::native_lower_disabled(),
        );

        // Entry block and its parameters.
        let entry_id = scratch.intern_block("entry");
        // Seed %0, %1, ... for parameters in order.
        for (i, (arg_name, ty)) in sig.params.iter().enumerate() {
            let aname = arg_name.clone().unwrap_or_else(|| format!("__param_{}", i));
            let v = scratch.intern_value(&aname);
            scratch.blocks[entry_id.as_usize()]
                .params
                .push((v, ty.clone()));
        }
        if body_starts_with_implicit_entry(body) {
            scratch.alias_block(&implicit_entry_block_label(&sig), entry_id);
        }
        scratch.set_current(entry_id);

        let mut bi = 0usize;
        while bi < body.len() {
            let (ln, raw) = &body[bi];
            let line = raw.trim();
            if line.is_empty() {
                bi += 1;
                continue;
            }
            if line == "{" {
                bi += 1;
                continue;
            }
            if line == "}" {
                break;
            }
            // Block label: `foo:` (possibly with preds comment)
            if let Some(label) = parse_block_label(line) {
                let id = scratch.intern_block(&label);
                scratch.set_current(id);
                bi += 1;
                continue;
            }
            // A `switch` instruction's case-list spans multiple physical
            // lines: header `switch i32 %x, label %d [` followed by one
            // `i32 K, label %L` per line and a closing `]`. Collect the
            // whole thing into a single string before parsing.
            //
            // Detect the switch by leading opcode (switch is a terminator
            // with no result, so it cannot appear on the RHS of `=`).
            let opcode = line.split_whitespace().next().unwrap_or("");
            if opcode == "switch" {
                let mut collected = String::new();
                collected.push_str(line);
                let start_ln = *ln;
                let mut end = bi;
                // After seeing `[`, keep consuming lines until we see the
                // matching `]` (we don't support nested brackets in a
                // switch case list — LLVM doesn't produce them).
                let mut saw_open = collected.contains('[');
                let mut closed = saw_open && collected.contains(']');
                while !closed && end + 1 < body.len() {
                    end += 1;
                    let next = body[end].1.trim();
                    if next.is_empty() {
                        continue;
                    }
                    collected.push(' ');
                    collected.push_str(next);
                    if !saw_open && collected.contains('[') {
                        saw_open = true;
                    }
                    if saw_open && collected.contains(']') {
                        closed = true;
                    }
                }
                if !closed {
                    return Err(
                        self.err_parse(start_ln, "switch: unterminated case list (missing `]`)")
                    );
                }
                self.parse_switch(&collected, start_ln, &mut scratch)?;
                bi = end + 1;
                continue;
            }
            self.parse_body_line(line, *ln, &mut scratch)?;
            bi += 1;
        }

        scratch.check_alias_registration_order()?;
        self.apply_pending_phis(&mut scratch)?;
        scratch.check_all_named_values_defined()?;
        scratch.propagate_imported_o0_pointer_proofs(entry_id);

        // Install blocks into the function. Every block must have a
        // terminator; if not, that's a bug in the importer (all clang -O0
        // blocks end in ret/br/unreachable).
        for b in &scratch.blocks {
            if b.terminator().is_none() {
                return Err(Error::Unsupported(format!(
                    "block in @{} has no terminator (phi or fallthrough not supported)",
                    sig.name,
                )));
            }
        }

        let mut func = Function::new(fid, sig.name.clone(), self.func_tys[&sig.name], entry_id);
        func.blocks = scratch.blocks;
        func.calling_conv = CallingConv::C;
        func.linkage = if sig.internal {
            Linkage::Internal
        } else {
            Linkage::External
        };
        apply_function_attributes(&mut func, &sig);
        if let Some(index) = existing_placeholder {
            // A call can precede the callee's definition. `parse_call` installs
            // a body-less external placeholder so the call always references a
            // registered FuncId; the real definition must replace that exact
            // placeholder instead of leaving two Functions with the same id.
            self.module.functions[index] = func;
        } else {
            self.module.add_function(func);
        }
        Ok(())
    }

    fn register_function(&mut self, sig: FuncSignature) -> Result<FuncId> {
        let ft = FuncTy {
            params: sig.params.iter().map(|(_, t)| t.clone()).collect(),
            returns: sig
                .ret
                .as_ref()
                .map(|t| vec![t.clone()])
                .unwrap_or_default(),
            is_vararg: sig.is_vararg,
        };
        if let Some(existing) = self.func_ids.get(&sig.name) {
            let existing_ty_id = self.func_tys.get(&sig.name).ok_or_else(|| {
                self.err_unsupported(&format!(
                    "function `@{}` has an id but no registered signature",
                    sig.name
                ))
            })?;
            let existing_ty = self
                .module
                .func_types
                .get(existing_ty_id.index() as usize)
                .ok_or_else(|| {
                    self.err_unsupported(&format!(
                        "function `@{}` has an out-of-range registered signature",
                        sig.name
                    ))
                })?;
            if existing_ty != &ft {
                return Err(self.err_unsupported(&format!(
                    "conflicting signatures for function `@{}`: first {:?}, later {:?}",
                    sig.name, existing_ty, ft
                )));
            }
            return Ok(*existing);
        }
        let ftid = self.module.add_func_type(ft);
        let fid = FuncId::new(self.func_ids.len() as u32);
        self.func_ids.insert(sig.name.clone(), fid);
        self.func_tys.insert(sig.name, ftid);
        Ok(fid)
    }

    fn emit_i64_const(&self, value: i128, f: &mut FuncScratch) -> ValueId {
        let v = f.fresh_value();
        f.push_inst(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(value),
            })
            .with_result(v),
        );
        v
    }

    fn emit_i64_binop(
        &self,
        op: BinOp,
        lhs: ValueId,
        rhs: ValueId,
        f: &mut FuncScratch,
    ) -> ValueId {
        let dest = f.fresh_value();
        f.push_inst(
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs,
                rhs,
            })
            .with_result(dest),
        );
        dest
    }

    fn coerce_int_to_i64(&self, value: ValueId, ty: &Ty, f: &mut FuncScratch) -> Result<ValueId> {
        match ty {
            Ty::I64 => Ok(value),
            Ty::Bool => {
                let widened = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty: Ty::Bool,
                        dst_ty: Ty::I64,
                        operand: value,
                    })
                    .with_result(widened),
                );
                Ok(widened)
            }
            Ty::I8 | Ty::I16 | Ty::I32 => {
                let widened = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::Cast {
                        op: CastOp::SExt,
                        src_ty: ty.clone(),
                        dst_ty: Ty::I64,
                        operand: value,
                    })
                    .with_result(widened),
                );
                Ok(widened)
            }
            Ty::I128 => Err(self.err_unsupported("dynamic struct alloca count with i128 type")),
            other => Err(self.err_unsupported(&format!(
                "non-integer struct alloca count type `{:?}`",
                other
            ))),
        }
    }

    /// Register (once) a body-less external `void`-returning C function and
    /// return its `FuncId`, mirroring `parse_call`'s declare-by-use path so no
    /// undefined symbol escapes the module. Reused for the libSystem
    /// `memset_patternN` runtime calls the `memset.pattern` intrinsic lowers to.
    fn register_external_void_fn(&mut self, name: &str, param_tys: &[Ty]) -> Result<FuncId> {
        if let Some(id) = self.func_ids.get(name) {
            return Ok(*id);
        }
        let sig = FuncSignature {
            name: name.to_string(),
            ret: None,
            params: param_tys.iter().map(|t| (None, t.clone())).collect(),
            is_vararg: false,
            internal: false,
            stack_protector: ImportedStackProtectorAttr::None,
            libm_pure_math: false,
        };
        let fid = self.register_function(sig.clone())?;
        if !self.module.functions.iter().any(|func| func.id == fid) {
            let mut func = Function::new(
                fid,
                sig.name.clone(),
                self.func_tys[&sig.name],
                BlockId::new(0),
            );
            func.calling_conv = CallingConv::C;
            func.linkage = Linkage::External;
            apply_function_attributes(&mut func, &sig);
            self.module.add_function(func);
        }
        Ok(fid)
    }

    /// Lower `@llvm.experimental.memset.pattern.p0.<ELEM>.<COUNT>` the way LLVM's
    /// own Darwin backend does: a call to libSystem's `memset_patternN`.
    ///
    /// Intrinsic signature (LangRef):
    ///   `void @llvm.experimental.memset.pattern(ptr <dest>, <ELEM> <value>,
    ///                                           <COUNT> <count>, i1 <volatile>)`
    /// Semantics: store `count` COPIES of `value` starting at `dest` — so the
    /// number of bytes written is `count * sizeof(<ELEM>)`.
    ///
    /// libSystem entry point:
    ///   `void memset_patternN(void *b, const void *pattern, size_t len_BYTES)`
    /// where `N` = sizeof(pattern) ∈ {4, 8, 16} and `len` is in BYTES. The
    /// pattern is passed BY ADDRESS, so `value` (which may be a runtime value)
    /// is spilled to a stack slot whose address we hand to the runtime.
    ///
    /// Only 4/8/16-byte element patterns have a libSystem entry point; any other
    /// element size fails closed rather than risk a wrong byte count.
    fn emit_memset_pattern(
        &mut self,
        args: &[ValueId],
        arg_tys: &[Ty],
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        if result.is_some() {
            return Err(self.err_unsupported("memset.pattern intrinsic with a result value"));
        }
        if args.len() != 4 || arg_tys.len() != 4 {
            return Err(self.err_parse(
                lineno,
                "memset.pattern intrinsic needs (dest, value, count, volatile)",
            ));
        }
        let dest = args[0];
        let pattern_val = args[1];
        let pattern_ty = arg_tys[1].clone();
        let count = args[2];
        let count_ty = arg_tys[2].clone();

        let elem_bytes = memset_pattern_elem_bytes(&pattern_ty).ok_or_else(|| {
            self.err_unsupported(&format!(
                "memset.pattern element type `{:?}` (no fixed byte size)",
                pattern_ty
            ))
        })?;
        let symbol = match elem_bytes {
            4 => "memset_pattern4",
            8 => "memset_pattern8",
            16 => "memset_pattern16",
            other => {
                return Err(self.err_unsupported(&format!(
                    "memset.pattern pattern size {} bytes (libSystem provides only 4/8/16)",
                    other
                )));
            }
        };
        if !is_integer_ty(&count_ty) {
            return Err(self.err_unsupported(&format!(
                "memset.pattern count type `{:?}` (must be integer)",
                count_ty
            )));
        }

        // 1. Stack slot holding the (possibly runtime) pattern value.
        let slot = f.fresh_value();
        f.push_inst(
            InstrNode::new(Inst::Alloca {
                ty: pattern_ty.clone(),
                count: None,
                align: Some(elem_bytes),
            })
            .with_result(slot),
        );
        // 2. Materialize the pattern into that slot.
        f.push_inst(InstrNode::new(Inst::Store {
            ty: pattern_ty,
            ptr: slot,
            value: pattern_val,
            volatile: false,
            align: None,
        }));
        // 3. len_bytes = count * sizeof(pattern).
        let count_i64 = self.coerce_int_to_i64(count, &count_ty, f)?;
        let elem_const = self.emit_i64_const(elem_bytes as i128, f);
        let byte_len = self.emit_i64_binop(BinOp::Mul, count_i64, elem_const, f);
        // 4. memset_patternN(dest, &slot, len_bytes).
        let fid = self.register_external_void_fn(symbol, &[Ty::Ptr, Ty::Ptr, Ty::I64])?;
        f.push_inst(InstrNode::new(Inst::Call {
            callee: fid,
            args: vec![dest, slot, byte_len],
        }));
        Ok(())
    }

    fn combine_i64_offsets(
        &self,
        lhs: Option<ValueId>,
        rhs: Option<ValueId>,
        f: &mut FuncScratch,
    ) -> Option<ValueId> {
        match (lhs, rhs) {
            (None, rhs) => rhs,
            (lhs, None) => lhs,
            (Some(lhs), Some(rhs)) => Some(self.emit_i64_binop(BinOp::Add, lhs, rhs, f)),
        }
    }

    fn emit_scaled_gep_index(
        &self,
        index_clause: &str,
        stride: u64,
        context: &str,
        f: &mut FuncScratch,
    ) -> Result<Option<ValueId>> {
        let (index_ty_str, index_tok) = split_ty_operand(index_clause.trim())?;
        let index_ty = parse_ty(&index_ty_str)?;
        if !is_integer_ty(&index_ty) {
            return Err(self.err_unsupported(&format!("{} type `{}`", context, index_ty_str)));
        }
        if matches!(index_ty, Ty::I128) {
            return Err(self.err_unsupported(&format!("{} with i128 type", context)));
        }

        let stride = i128::from(stride);
        if let Some(index) = parse_int_literal(&index_tok) {
            let byte_offset = index
                .checked_mul(stride)
                .ok_or_else(|| self.err_unsupported("fixed array GEP byte offset overflow"))?;
            if byte_offset == 0 {
                return Ok(None);
            }
            return Ok(Some(self.emit_i64_const(byte_offset, f)));
        }

        let raw_index = self.lookup_operand(&index_tok, &index_ty, f)?;
        let index = self.coerce_int_to_i64(raw_index, &index_ty, f)?;
        if stride == 1 {
            return Ok(Some(index));
        }

        let stride_value = self.emit_i64_const(stride, f);
        Ok(Some(self.emit_i64_binop(
            BinOp::Mul,
            index,
            stride_value,
            f,
        )))
    }

    fn emit_fixed_layout_gep_offset(
        &self,
        layout: &FixedLayout,
        indices: &[String],
        f: &mut FuncScratch,
    ) -> Result<ValueId> {
        if indices.is_empty() {
            return Err(self.err_unsupported("fixed array GEP requires at least one index"));
        }

        let mut offset = None;
        let mut current = layout;
        for (idx, index_clause) in indices.iter().enumerate() {
            if idx == 0 {
                let part = self.emit_scaled_gep_index(
                    index_clause,
                    layout.size(),
                    "fixed array GEP outer index",
                    f,
                )?;
                offset = self.combine_i64_offsets(offset, part, f);
                continue;
            }

            match current {
                FixedLayout::Array { elem, .. } => {
                    let next = elem.as_ref();
                    let part = self.emit_scaled_gep_index(
                        index_clause,
                        next.size(),
                        "fixed array GEP index",
                        f,
                    )?;
                    offset = self.combine_i64_offsets(offset, part, f);
                    current = next;
                }
                FixedLayout::Struct { fields, .. } => {
                    let (field_ty_str, field_tok) = split_ty_operand(index_clause.trim())?;
                    let field_ty = parse_ty(&field_ty_str)?;
                    if !is_integer_ty(&field_ty) {
                        return Err(self.err_unsupported(&format!(
                            "fixed array struct GEP field index type `{}`",
                            field_ty_str
                        )));
                    }
                    let field_idx = parse_int_literal(&field_tok).ok_or_else(|| {
                        self.err_unsupported("fixed array struct GEP with dynamic field index")
                    })?;
                    if field_idx < 0 {
                        return Err(self
                            .err_unsupported("fixed array struct GEP with negative field index"));
                    }
                    let field_idx = field_idx as usize;
                    let field = fields.get(field_idx).ok_or_else(|| {
                        self.err_unsupported(&format!(
                            "fixed array struct GEP field index {} out of bounds",
                            field_idx
                        ))
                    })?;
                    if field.offset != 0 {
                        let part = Some(self.emit_i64_const(i128::from(field.offset), f));
                        offset = self.combine_i64_offsets(offset, part, f);
                    }
                    current = &field.layout;
                }
                FixedLayout::Scalar(_) => {
                    return Err(self.err_unsupported(
                        "fixed array GEP has too many indices for scalar element",
                    ));
                }
            }
        }

        Ok(offset.unwrap_or_else(|| self.emit_i64_const(0, f)))
    }

    // --- Instructions ------------------------------------------------------

    fn parse_body_line(&mut self, line: &str, lineno: usize, f: &mut FuncScratch) -> Result<()> {
        // Form: `  %name = <opcode> ...`  or  `  <opcode-without-result> ...`
        let (result_name, rest) = if let Some((lhs, rhs)) = split_eq_not_icmp(line) {
            let lhs = lhs.trim();
            if !lhs.starts_with('%') {
                return Err(self.err_parse(lineno, "LHS of `=` must be %name"));
            }
            (Some(lhs.trim_start_matches('%').to_string()), rhs.trim())
        } else {
            (None, line)
        };

        // At -O1 and above clang prefixes calls with the tail-call marker
        // (`tail call`, `musttail call`, `notail call`). The marker is a
        // pure optimization hint with no bearing on semantics — dropping it
        // is a refinement. Strip it here so dispatch sees the real opcode
        // (`call`) instead of bucketing the whole program as
        // `unsupported: opcode tail`.
        let rest = {
            let mut r = rest;
            for prefix in ["tail ", "musttail ", "notail "] {
                if let Some(t) = r.strip_prefix(prefix) {
                    r = t.trim_start();
                    break;
                }
            }
            r
        };

        // NATIVE VECTOR LOWERING. Before falling back to lane scalarization,
        // ask the plan whether THIS instruction was chosen to be carried in a
        // single 128-bit register. The plan is subtractive and shape-gated, so
        // an instruction only gets here if every operand shape, lane index and
        // shuffle mask it uses was proven lowerable.
        if !f.native_plan.is_empty()
            && self.try_native_vector(result_name.as_deref(), rest, lineno, f)?
        {
            return Ok(());
        }

        // VECTOR LANE EXPANSION. clang -O2/-O3 emits fixed-width vector types
        // and the element operations; `crate::vector::expand` rewrites one
        // vector instruction into the equivalent sequence of SCALAR textual
        // instructions, which are then parsed by the ordinary scalar paths
        // below. Anything vector-typed without a proven lane-wise expansion
        // comes back as `Err` and fails closed here. `TCG_NO_VECTOR_IMPORT=1`
        // restores the pre-expansion behaviour byte for byte.
        if !vector_import_disabled() {
            let uid = f.vec_uid;
            match crate::vector::expand(result_name.as_deref(), rest, uid) {
                Ok(Some(expansion)) => {
                    let _ = f.next_vec_uid();
                    for (name, token) in expansion.aliases {
                        f.token_alias.insert(name, token);
                    }
                    for (name, text) in expansion.insts {
                        self.dispatch_body_inst(name, &text, lineno, f)?;
                    }
                    // BOUNDARY (lanes -> native). This value scalarized, but
                    // some consumer of it was planned native, so pack the lanes
                    // into one register HERE — at the definition, where the
                    // packed value dominates exactly what the lanes dominate.
                    if let Some(name) = result_name.as_deref()
                        && let Some(shape) = f.native_plan.pack_needed(name)
                    {
                        self.emit_pack_lanes(name, shape, f)?;
                    }
                    return Ok(());
                }
                Ok(None) => {}
                Err(reason) => return Err(self.err_unsupported(&reason)),
            }
        }

        self.dispatch_body_inst(result_name, rest, lineno, f)
    }

    // --- Native 128-bit vector lowering ------------------------------------

    /// Emit `rest` as a NATIVE vector instruction if the function's plan chose
    /// that representation for it. Returns `false` when the instruction is not
    /// native (the caller then falls through to lane scalarization).
    ///
    /// The plan has already proven the shape, the operand spellings, the lane
    /// index and the shuffle mask; this function does no re-deciding, it only
    /// builds the `trust_ir` node the plan asked for. Anything the plan did not
    /// mark stays on the scalarizing path, which is why an unrecognized form
    /// can never be lowered natively by accident.
    fn try_native_vector(
        &mut self,
        result: Option<&str>,
        rest: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<bool> {
        let opcode = rest.split_whitespace().next().unwrap_or("");

        // `store` has no SSA result, so it is not in the plan's `forms` map;
        // it is native exactly when its stored value is (the same rule the
        // planner applied).
        if opcode == "store" {
            return self.try_native_vector_store(rest, lineno, f);
        }

        let Some(name) = result else {
            return Ok(false);
        };
        let Some(form) = f.native_plan.form(name).cloned() else {
            return Ok(false);
        };

        let tail = strip_native_vector_flags(rest, opcode);
        match form {
            NativeForm::Load => self.emit_native_vector_load(name, tail, lineno, f)?,
            NativeForm::BinOp => self.emit_native_vector_binop(opcode, name, tail, lineno, f)?,
            NativeForm::Phi => {
                let (ty_str, _) = split_ty_operand(tail)?;
                let shape = self.require_native_shape(&ty_str)?;
                self.parse_phi_with_ty(tail, Some(name.to_string()), lineno, f, shape.vector_ty())?;
            }
            NativeForm::ExtractElement => {
                self.emit_native_extract_element(name, tail, lineno, f)?
            }
            NativeForm::InsertElement => self.emit_native_insert_element(name, tail, lineno, f)?,
            NativeForm::SplatLane0 { splat_token } => {
                self.emit_native_splat(name, tail, &splat_token, lineno, f)?
            }
            NativeForm::Store => return Ok(false),
        }

        // BOUNDARY (native -> lanes). Some consumer of this value is
        // scalarized, so materialize its lanes right here at the definition:
        // `%name#vi = extractelement <S> %name, i64 i`. Emitting at the
        // definition (not at each use) is what makes the lane values dominate
        // every use the native value dominated.
        if let Some(shape) = f.native_plan.lanes_needed(name) {
            self.emit_native_lane_explosion(name, shape, f)?;
        }
        Ok(true)
    }

    /// The plan says this `store` is native: one `STR Q` of a 128-bit value.
    fn try_native_vector_store(
        &mut self,
        rest: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<bool> {
        let tail = rest.trim_start_matches("store").trim();
        if tail.starts_with("volatile ") || tail.starts_with("atomic ") {
            return Ok(false);
        }
        let Some((val_part, rest2)) = split_comma(tail) else {
            return Ok(false);
        };
        let Ok((ty_str, val_tok)) = split_ty_operand(&val_part) else {
            return Ok(false);
        };
        let Some(shape) = crate::native_vector::native_shape(&ty_str) else {
            return Ok(false);
        };
        // Native exactly when the stored value is itself native (or a vector
        // constant, which materializes directly into a register).
        if let Some(name) = val_tok.trim().strip_prefix('%')
            && !f.native_plan.is_native(name)
        {
            return Ok(false);
        }
        let ty = shape.vector_ty();
        let value = self.lookup_operand(&val_tok, &ty, f)?;
        let ptr_part = split_comma(&rest2)
            .map(|(head, _)| head)
            .unwrap_or_else(|| rest2.trim().to_string());
        let (_, ptr_tok) = split_ty_operand(&ptr_part)?;
        let ptr = self.lookup_operand(&ptr_tok, &Ty::Ptr, f)?;
        let _ = lineno;
        f.push_inst(InstrNode::new(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        }));
        Ok(true)
    }

    fn require_native_shape(&self, ty_str: &str) -> Result<Shape> {
        crate::native_vector::native_shape(ty_str).ok_or_else(|| {
            self.err_unsupported(&format!(
                "native vector lowering reached non-contracted shape `{ty_str}`"
            ))
        })
    }

    fn emit_native_vector_load(
        &mut self,
        name: &str,
        tail: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let (ty_str, rest2) = split_comma(tail)
            .ok_or_else(|| self.err_parse(lineno, "load: expected `<ty>, ptr`"))?;
        let shape = self.require_native_shape(&ty_str)?;
        let ptr_part = split_comma(&rest2)
            .map(|(head, _)| head)
            .unwrap_or_else(|| rest2.trim().to_string());
        let (_, ptr_tok) = split_ty_operand(&ptr_part)?;
        let ptr = self.lookup_operand(&ptr_tok, &Ty::Ptr, f)?;
        let dest = f.intern_value(name);
        f.push_inst(
            InstrNode::new(Inst::Load {
                ty: shape.vector_ty(),
                ptr,
                volatile: false,
                align: None,
            })
            .with_result(dest),
        );
        Ok(())
    }

    fn emit_native_vector_binop(
        &mut self,
        opcode: &str,
        name: &str,
        tail: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // Only the lane-wise operations the AArch64 ISel lowers for the
        // contracted shapes reach here — six integer ops on the integer
        // shapes, four FP ops on `<4 x float>`/`<2 x double>` (the planner
        // admits no other opcode, and refuses the integer/FP cross product).
        // Anything else is a planner/emitter disagreement and fails closed
        // rather than picking a default.
        let op = match opcode {
            "add" => BinOp::Add,
            "sub" => BinOp::Sub,
            "mul" => BinOp::Mul,
            "and" => BinOp::And,
            "or" => BinOp::Or,
            "xor" => BinOp::Xor,
            "fadd" => BinOp::FAdd,
            "fsub" => BinOp::FSub,
            "fmul" => BinOp::FMul,
            "fdiv" => BinOp::FDiv,
            _ => {
                return Err(self.err_unsupported(&format!(
                    "native vector lowering reached unmodelled opcode `{opcode}`"
                )));
            }
        };
        let (ty_str, operands) = split_ty_operand(tail)?;
        let shape = self.require_native_shape(&ty_str)?;
        // Re-check the integer/FP split at the emission site. The planner is
        // the authority on what goes native, but this function is reachable
        // from a single `NativeForm::BinOp` tag that does not itself record
        // which family the opcode came from, so a future planner edit that
        // widened one set without the other would otherwise emit `ADD .2d` for
        // a `<2 x double>`. Cheap, local, and fails closed.
        let op_is_fp = matches!(op, BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv);
        if op_is_fp != shape.elem.is_float() {
            return Err(self.err_unsupported(&format!(
                "native vector lowering: opcode `{opcode}` does not match element type of `{ty_str}`"
            )));
        }
        let ty = shape.vector_ty();
        let (lhs_str, rhs_str) = split_comma(&operands)
            .ok_or_else(|| self.err_parse(lineno, "vector binop: expected `%a, %b`"))?;
        let lhs = self.lookup_operand(&lhs_str, &ty, f)?;
        let rhs = self.lookup_operand(&rhs_str, &ty, f)?;
        let dest = f.intern_value(name);
        f.push_inst(InstrNode::new(Inst::BinOp { op, ty, lhs, rhs }).with_result(dest));
        Ok(())
    }

    fn emit_native_extract_element(
        &mut self,
        name: &str,
        tail: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let parts = split_aggregate_elems(tail);
        if parts.len() != 2 {
            return Err(self.err_parse(lineno, "extractelement: expected `<vec>, <idx>`"));
        }
        let (vec_ty, vec_val) = split_ty_operand(&parts[0])?;
        let shape = self.require_native_shape(&vec_ty)?;
        let array = self.lookup_operand(&vec_val, &shape.vector_ty(), f)?;
        let index = self.native_lane_index(&parts[1], shape, lineno, f)?;
        let dest = f.intern_value(name);
        f.push_inst(
            InstrNode::new(Inst::ExtractElement {
                ty: shape.elem.ty(),
                array,
                index,
            })
            .with_result(dest),
        );
        Ok(())
    }

    fn emit_native_insert_element(
        &mut self,
        name: &str,
        tail: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let parts = split_aggregate_elems(tail);
        if parts.len() != 3 {
            return Err(self.err_parse(lineno, "insertelement: expected `<vec>, <elem>, <idx>`"));
        }
        let (vec_ty, vec_val) = split_ty_operand(&parts[0])?;
        let shape = self.require_native_shape(&vec_ty)?;
        let ty = shape.vector_ty();
        let array = self.lookup_operand(&vec_val, &ty, f)?;
        let (_, ins_val) = split_ty_operand(&parts[1])?;
        let value = self.lookup_operand(&ins_val, &shape.elem.ty(), f)?;
        let index = self.native_lane_index(&parts[2], shape, lineno, f)?;
        let dest = f.intern_value(name);
        f.push_inst(
            InstrNode::new(Inst::InsertElement {
                ty,
                array,
                index,
                value,
            })
            .with_result(dest),
        );
        Ok(())
    }

    /// The lane-0 broadcast idiom, which is exactly NEON `DUP`:
    ///
    /// ```text
    /// %a = insertelement <S> poison, T %x, i64 0
    /// %b = shufflevector <S> %a, <S> poison, <N x i32> zeroinitializer
    /// ```
    ///
    /// The planner has already proven that the source of this shuffle is that
    /// `insertelement`, so lane 0 IS `%x` and the pair collapses to a single
    /// `vector.pack_lanes` of one repeated scalar. No other shuffle reaches
    /// here — everything else scalarizes.
    fn emit_native_splat(
        &mut self,
        name: &str,
        tail: &str,
        splat_token: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let parts = split_aggregate_elems(tail);
        if parts.len() != 3 {
            return Err(self.err_parse(lineno, "shufflevector: expected three operands"));
        }
        let (vec_ty, _) = split_ty_operand(&parts[0])?;
        let shape = self.require_native_shape(&vec_ty)?;
        let lane0 = self.lookup_operand(splat_token, &shape.elem.ty(), f)?;
        let dest = f.intern_value(name);
        let op = trust_ir::dialect::vector::pack_lanes_repeated(shape.vector_ty(), lane0)
            .map_err(|e| self.err_unsupported(&format!("vector splat: {e}")))?;
        f.push_inst(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(dest));
        Ok(())
    }

    /// Materialize the constant lane index of an `insertelement` /
    /// `extractelement` as the `i64` constant `trust_ir` requires.
    fn native_lane_index(
        &mut self,
        clause: &str,
        shape: Shape,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<ValueId> {
        let (_, val) = split_ty_operand(clause)?;
        let idx = parse_int_literal(&val)
            .ok_or_else(|| self.err_parse(lineno, "vector lane index is not a constant"))?;
        if idx < 0 || idx >= i128::from(shape.lanes) {
            return Err(self.err_parse(lineno, "vector lane index out of range"));
        }
        Ok(self.emit_i64_const(idx, f))
    }

    /// BOUNDARY (native -> lanes): bind `%name#v0 … %name#v{n-1}` to the lanes
    /// of the native value `%name`, so a scalarized consumer finds exactly the
    /// lane names [`crate::vector`] would have produced.
    fn emit_native_lane_explosion(
        &mut self,
        name: &str,
        shape: Shape,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let array = f.intern_value(name);
        let elem_ty = shape.elem.ty();
        for i in 0..shape.lanes {
            let index = self.emit_i64_const(i128::from(i), f);
            let lane = f.intern_value(&format!("{name}#v{i}"));
            f.push_inst(
                InstrNode::new(Inst::ExtractElement {
                    ty: elem_ty.clone(),
                    array,
                    index,
                })
                .with_result(lane),
            );
        }
        Ok(())
    }

    /// BOUNDARY (lanes -> native): bind `%name` to a single 128-bit value built
    /// from the lanes `%name#v0 … %name#v{n-1}` a scalarized definition just
    /// produced.
    ///
    /// A lane may be an ALIAS (`extractelement`/`shufflevector` are pure
    /// renamings in the scalarizer) or even a literal, so each lane goes
    /// through the ordinary operand resolution rather than being assumed to be
    /// an SSA name.
    fn emit_pack_lanes(&mut self, name: &str, shape: Shape, f: &mut FuncScratch) -> Result<()> {
        let elem_ty = shape.elem.ty();
        let mut lanes = Vec::with_capacity(shape.lanes as usize);
        for i in 0..shape.lanes {
            let tok = format!("%{name}#v{i}");
            lanes.push(self.lookup_operand(&tok, &elem_ty, f)?);
        }
        let dest = f.intern_value(name);
        let op = trust_ir::dialect::vector::pack_lanes(shape.vector_ty(), lanes);
        f.push_inst(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(dest));
        Ok(())
    }

    /// Dispatch a SCALAR instruction on its leading opcode keyword. Reached
    /// both directly and, one lane at a time, from the vector expander.
    fn dispatch_body_inst(
        &mut self,
        result_name: Option<String>,
        rest: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let opcode = rest.split_whitespace().next().unwrap_or("");
        match opcode {
            "ret" => self.parse_ret(rest, lineno, f),
            "br" => self.parse_br(rest, lineno, f),
            "unreachable" => {
                f.push_inst(InstrNode::new(Inst::Unreachable));
                Ok(())
            }
            "add" | "sub" | "mul" | "and" | "or" | "xor" | "shl" | "lshr" | "ashr" | "sdiv"
            | "udiv" | "srem" | "urem" => self.parse_binop(opcode, rest, result_name, lineno, f),
            "icmp" => self.parse_icmp(rest, result_name, lineno, f),
            "alloca" => self.parse_alloca(rest, result_name, lineno, f),
            "load" => self.parse_load(rest, result_name, lineno, f),
            "store" => self.parse_store(rest, lineno, f),
            "call" => self.parse_call(rest, result_name, lineno, f),
            "getelementptr" => self.parse_gep(rest, result_name, lineno, f),
            "sext" | "zext" | "trunc" | "bitcast" | "ptrtoint" | "inttoptr" | "sitofp"
            | "fptosi" | "uitofp" | "fptoui" | "fpext" | "fptrunc" => {
                self.parse_cast(opcode, rest, result_name, lineno, f)
            }
            "select" => self.parse_select(rest, result_name, lineno, f),
            "freeze" => self.parse_freeze(rest, result_name, lineno, f),
            "phi" => self.parse_phi(rest, result_name, lineno, f),
            "switch" => Err(self.err_parse(
                lineno,
                "internal: switch should be collected multi-line by parse_define",
            )),
            "invoke" => Err(self.err_unsupported("invoke / exceptions")),
            "landingpad" | "resume" => Err(self.err_unsupported("exception handling")),
            "fadd" | "fsub" | "fmul" | "fdiv" | "frem" => {
                self.parse_fbinop(opcode, rest, result_name, lineno, f)
            }
            "fneg" => self.parse_fneg(rest, result_name, lineno, f),
            "fcmp" => self.parse_fcmp(rest, result_name, lineno, f),
            "atomicrmw" | "cmpxchg" | "fence" => Err(self.err_unsupported("atomics")),
            "" => Err(self.err_parse(lineno, "empty instruction")),
            other => Err(self.err_unsupported(&format!("opcode `{}`", other))),
        }
    }

    fn parse_ret(&mut self, rest: &str, _lineno: usize, f: &mut FuncScratch) -> Result<()> {
        // `ret void`  or  `ret i32 %x`  or  `ret i32 42`.
        let tail = rest.trim_start_matches("ret").trim();
        if tail == "void" {
            f.push_inst(InstrNode::new(Inst::Return { values: vec![] }));
            return Ok(());
        }
        let (ty_str, val_str) = split_ty_operand(tail)?;
        let ty = parse_ty(&ty_str)?;
        let v = self.lookup_operand(&val_str, &ty, f)?;
        f.push_inst(InstrNode::new(Inst::Return { values: vec![v] }));
        Ok(())
    }

    fn parse_br(&mut self, rest: &str, lineno: usize, f: &mut FuncScratch) -> Result<()> {
        // `br label %L`  or  `br i1 %c, label %T, label %F`
        let tail = rest.trim_start_matches("br").trim();
        if tail.starts_with("label ") {
            let label = tail
                .trim_start_matches("label")
                .trim()
                .trim_start_matches('%')
                .to_string();
            let id = f.intern_block(&label);
            f.push_inst(InstrNode::new(Inst::Br {
                target: id,
                args: vec![],
            }));
            Ok(())
        } else if tail.starts_with("i1 ") {
            // i1 %c, label %T, label %F
            let mut parts = tail.splitn(2, ',');
            let cond_part = parts
                .next()
                .ok_or_else(|| self.err_parse(lineno, "br: missing cond"))?;
            let rest2 = parts
                .next()
                .ok_or_else(|| self.err_parse(lineno, "br: missing labels"))?;
            // Route the condition through `lookup_operand` rather than
            // interning the bare name. Two things fall out: the vector
            // lane-alias chain is resolved (an `extractelement <N x i1> %m,
            // i32 k` condition is a pure renaming, so `%c` may stand for
            // `%m#vk`), and a LITERAL condition — `br i1 true, …` — becomes a
            // materialized Bool constant instead of an SSA name `true` with no
            // definition anywhere in the function.
            let cond_tok = cond_part.trim_start_matches("i1").trim();
            let cond = self.lookup_operand(cond_tok, &Ty::Bool, f)?;
            let (tlabel, flabel) = split_two_labels(rest2)
                .ok_or_else(|| self.err_parse(lineno, "br: malformed label pair"))?;
            let then_id = f.intern_block(&tlabel);
            let else_id = f.intern_block(&flabel);
            f.push_inst(InstrNode::new(Inst::CondBr {
                cond,
                then_target: then_id,
                then_args: vec![],
                else_target: else_id,
                else_args: vec![],
            }));
            Ok(())
        } else {
            Err(self.err_parse(lineno, &format!("unrecognised br: {}", rest)))
        }
    }

    /// Parse a (multi-line-collected) `switch` instruction.
    ///
    /// Canonical shape:
    /// ```text
    /// switch <ty> <val>, label %<default> [
    ///     <ty> <case_val_0>, label %<case_block_0>
    ///     <ty> <case_val_1>, label %<case_block_1>
    ///     ...
    /// ]
    /// ```
    ///
    /// All case types must match the selector type (LLVM semantics) and
    /// must be one of `i1`, `i8`, `i16`, `i32`, or `i64` — anything else
    /// returns `Error::Unsupported`. Case values must be integer literals;
    /// LLVM does not permit non-constant case labels, so we reject any
    /// `%name` or `@name` tokens in case-value position.
    ///
    /// trust_ir target: `Inst::Switch { value, default, default_args: vec![], cases }`.
    /// Phi parsing patches block arguments onto switch edges after the
    /// function body is read. Without phi nodes, `default_args` and each
    /// case's `args` stay empty. The codegen-side lowering (see
    /// `trust-cg-lower/src/switch.rs`, #323) picks the best strategy
    /// (linear scan / BST / jump table) regardless.
    fn parse_switch(&mut self, collected: &str, lineno: usize, f: &mut FuncScratch) -> Result<()> {
        // Strip leading `switch`.
        let tail = collected.trim_start_matches("switch").trim();

        // Split header and case list at the opening `[`.
        let lbrack = tail
            .find('[')
            .ok_or_else(|| self.err_parse(lineno, "switch: missing `[`"))?;
        let rbrack = tail
            .rfind(']')
            .ok_or_else(|| self.err_parse(lineno, "switch: missing `]`"))?;
        if rbrack <= lbrack {
            return Err(self.err_parse(lineno, "switch: `]` before `[`"));
        }
        let header = tail[..lbrack].trim().trim_end_matches(',').trim();
        let body = tail[lbrack + 1..rbrack].trim();

        // Header: `<ty> <val>, label %<default>`
        let (sel_part, default_part) = split_comma(header).ok_or_else(|| {
            self.err_parse(lineno, "switch: expected `<ty> <val>, label %default`")
        })?;
        let (sel_ty_str, sel_val_tok) = split_ty_operand(&sel_part)?;
        let sel_ty = parse_ty(&sel_ty_str)?;
        if !matches!(sel_ty, Ty::Bool | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64) {
            return Err(self.err_unsupported(&format!(
                "switch selector type `{}` (only i1/i8/i16/i32/i64 are supported)",
                sel_ty_str
            )));
        }
        let value = self.lookup_operand(&sel_val_tok, &sel_ty, f)?;

        let default_label = default_part
            .trim()
            .trim_start_matches("label")
            .trim()
            .trim_start_matches('%')
            .to_string();
        if default_label.is_empty() {
            return Err(self.err_parse(lineno, "switch: empty default label"));
        }
        let default_block = f.intern_block(&default_label);

        // Case list: zero or more `<ty> <K>, label %<L>` entries, separated
        // by whitespace/newlines. We walk the body by whitespace-tokens
        // and group into 4-token chunks: [ty, K_comma, "label", %L]. clang -O0
        // always emits it this way, and comments / `!dbg` metadata have
        // already been stripped by the top-level preprocessor.
        let mut cases: Vec<SwitchCase> = Vec::new();
        let toks: Vec<&str> = body.split_whitespace().collect();
        let mut i = 0;
        while i < toks.len() {
            // Expect: <ty>  <K>[,]  label  %<L>[,]
            if i + 3 >= toks.len() {
                return Err(self.err_parse(
                    lineno,
                    &format!("switch: truncated case at token `{}`", toks[i]),
                ));
            }
            let case_ty_str = toks[i];
            let case_ty = parse_ty(case_ty_str)?;
            if case_ty != sel_ty {
                return Err(self.err_unsupported(&format!(
                    "switch case type `{}` does not match selector `{}`",
                    case_ty_str, sel_ty_str
                )));
            }
            // Case value: may have a trailing comma.
            let raw_val = toks[i + 1].trim_end_matches(',');
            // Reject non-literal case values — LLVM's textual syntax only
            // allows constant integer case labels, but an importer user
            // could feed garbage and we want a typed "no".
            if raw_val.starts_with('%') || raw_val.starts_with('@') {
                return Err(self.err_parse(
                    lineno,
                    &format!("switch case value must be a constant, got `{}`", raw_val),
                ));
            }
            let case_val = parse_int_literal(raw_val).ok_or_else(|| {
                self.err_parse(
                    lineno,
                    &format!("switch: bad case value literal `{}`", raw_val),
                )
            })?;
            if toks[i + 2] != "label" {
                return Err(self.err_parse(
                    lineno,
                    &format!(
                        "switch: expected `label` after case value, got `{}`",
                        toks[i + 2]
                    ),
                ));
            }
            let label_tok = toks[i + 3].trim_end_matches(',');
            let label = label_tok.trim_start_matches('%').to_string();
            if label.is_empty() {
                return Err(self.err_parse(lineno, "switch: empty case label"));
            }
            let target = f.intern_block(&label);
            cases.push(SwitchCase {
                value: Constant::Int(case_val),
                target,
                args: vec![],
            });
            i += 4;
        }

        f.push_inst(InstrNode::new(Inst::Switch {
            value,
            default: default_block,
            default_args: vec![],
            cases,
            // Plain integer switch from imported LLVM IR — not a vetted
            // exhaustive-enum-discriminant match, so the default arm stays live.
            exhaustive_enum_unreachable: false,
        }));
        Ok(())
    }

    fn parse_binop(
        &mut self,
        opcode: &str,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let op = match opcode {
            "add" => BinOp::Add,
            "sub" => BinOp::Sub,
            "mul" => BinOp::Mul,
            "and" => BinOp::And,
            "or" => BinOp::Or,
            "xor" => BinOp::Xor,
            "shl" => BinOp::Shl,
            "lshr" => BinOp::LShr,
            "ashr" => BinOp::AShr,
            "sdiv" => BinOp::SDiv,
            "udiv" => BinOp::UDiv,
            "srem" => BinOp::SRem,
            "urem" => BinOp::URem,
            _ => unreachable!(),
        };
        // Strip leading opcode and any flags like nsw / nuw / exact.
        let tail = strip_binop_flags(rest, opcode);
        // "i32 %a, %b"  OR  "i32 %a, 5"
        let (ty_str, operands) = split_ty_operand(tail)?;
        let ty = parse_ty(&ty_str)?;
        let (lhs_str, rhs_str) = split_comma(&operands)
            .ok_or_else(|| self.err_parse(lineno, "binop: expected `%a, %b`"))?;
        let lhs = self.lookup_operand(&lhs_str, &ty, f)?;
        let rhs = self.lookup_operand(&rhs_str, &ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "binop without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(InstrNode::new(Inst::BinOp { op, ty, lhs, rhs }).with_result(dest));
        Ok(())
    }

    fn parse_icmp(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // `icmp [samesign] <pred> <ty> %a, %b`
        //
        // LLVM-21+ emits the `samesign` flag on comparisons where both operands
        // are known to share a sign bit. It is a poison-generating refinement
        // hint (poison if the signs differ), with no bearing on the compared
        // values themselves — dropping it is a sound refinement, exactly like
        // dropping `nsw`/`nuw` on arithmetic.
        let tail = rest.trim_start_matches("icmp").trim();
        let tail = tail.strip_prefix("samesign ").map_or(tail, str::trim_start);
        let mut parts = tail.splitn(2, char::is_whitespace);
        let pred_str = parts
            .next()
            .ok_or_else(|| self.err_parse(lineno, "icmp: missing predicate"))?;
        let rest = parts
            .next()
            .ok_or_else(|| self.err_parse(lineno, "icmp: missing operands"))?
            .trim();
        let pred = match pred_str {
            "eq" => ICmpOp::Eq,
            "ne" => ICmpOp::Ne,
            "ugt" => ICmpOp::Ugt,
            "uge" => ICmpOp::Uge,
            "ult" => ICmpOp::Ult,
            "ule" => ICmpOp::Ule,
            "sgt" => ICmpOp::Sgt,
            "sge" => ICmpOp::Sge,
            "slt" => ICmpOp::Slt,
            "sle" => ICmpOp::Sle,
            _ => {
                return Err(self.err_unsupported(&format!("icmp predicate `{}`", pred_str)));
            }
        };
        let (ty_str, operands) = split_ty_operand(rest)?;
        let ty = parse_ty(&ty_str)?;
        let (lhs_str, rhs_str) = split_comma(&operands)
            .ok_or_else(|| self.err_parse(lineno, "icmp: expected `%a, %b`"))?;
        let lhs = self.lookup_operand(&lhs_str, &ty, f)?;
        let rhs = self.lookup_operand(&rhs_str, &ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "icmp without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::ICmp {
                op: pred,
                ty,
                lhs,
                rhs,
            })
            .with_result(dest),
        );
        Ok(())
    }

    /// Parse an FP binary op: `fadd|fsub|fmul|fdiv|frem`.
    ///
    /// Canonical clang -O0 shape:
    ///
    ///   %r = fadd float %a, %b
    ///   %r = fadd fast double %a, %b
    ///   %r = fmul reassoc nnan ninf nsz arcp contract afn float %a, 1.500000e+00
    ///
    /// Fast-math flags (`fast`, `reassoc`, `nnan`, `ninf`, `nsz`, `arcp`,
    /// `contract`, `afn`) are accepted and silently dropped, matching the
    /// integer-side behaviour for `nsw`/`nuw`.
    fn parse_fbinop(
        &mut self,
        opcode: &str,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let op = match opcode {
            "fadd" => BinOp::FAdd,
            "fsub" => BinOp::FSub,
            "fmul" => BinOp::FMul,
            "fdiv" => BinOp::FDiv,
            "frem" => BinOp::FRem,
            _ => unreachable!("parse_fbinop opcode `{}`", opcode),
        };
        let tail = strip_fmath_flags(rest, opcode);
        let (ty_str, operands) = split_ty_operand(tail)?;
        let ty = parse_ty(&ty_str)?;
        if !matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
            return Err(
                self.err_unsupported(&format!("`{}` on non-float type `{}`", opcode, ty_str))
            );
        }
        let (lhs_str, rhs_str) = split_comma(&operands)
            .ok_or_else(|| self.err_parse(lineno, "fbinop: expected `%a, %b`"))?;
        let lhs = self.lookup_operand(&lhs_str, &ty, f)?;
        let rhs = self.lookup_operand(&rhs_str, &ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "fbinop without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(InstrNode::new(Inst::BinOp { op, ty, lhs, rhs }).with_result(dest));
        Ok(())
    }

    /// Parse `fneg [fast-math-flags]? <ty> <operand>`. LLVM's `fneg`
    /// corresponds to trust_ir's `UnOp::FNeg`.
    fn parse_fneg(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let tail = strip_fmath_flags(rest, "fneg");
        let (ty_str, operand_tok) = split_ty_operand(tail)?;
        let ty = parse_ty(&ty_str)?;
        if !matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
            return Err(self.err_unsupported(&format!("fneg on non-float type `{}`", ty_str)));
        }
        let operand = self.lookup_operand(&operand_tok, &ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "fneg without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::UnOp {
                op: UnOp::FNeg,
                ty,
                operand,
            })
            .with_result(dest),
        );
        Ok(())
    }

    /// Parse `fcmp [fast-math-flags]? <pred> <ty> <a>, <b>`. All 16 LLVM
    /// predicates are supported: 12 ordered/unordered comparisons plus
    /// `true`, `false`, `ord`, `uno`.
    ///
    ///   * `ord`  → not-NaN on either side: encoded as `FCmpOp::UEq`
    ///     applied to `%a == %a` AND `%b == %b` using a NotUnordered
    ///     predicate built from two comparisons? Too clever. Instead we
    ///     emit `FCmp { op: OEq, lhs: a, rhs: a }` AND `FCmp { op: OEq,
    ///     rhs: b }` and `and` them — that matches LLVM's documented
    ///     semantics (`ord` ≡ neither operand is a QNAN) without relying
    ///     on a trust_ir-level `ord`/`uno` predicate that doesn't exist.
    ///   * `uno` → `not ord`: same pattern, with `FCmpOp::UNe` — again
    ///     because trust_ir's `UNe` is true when either operand is NaN OR
    ///     they differ, which is the correct signal for `uno` when we
    ///     compare %a vs itself.
    ///   * `true` / `false` → `Inst::Const` i1 1/0.
    fn parse_fcmp(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // Strip leading `fcmp` and any fast-math flags before the
        // predicate keyword.
        let tail = strip_fmath_flags(rest, "fcmp");
        let mut parts = tail.splitn(2, char::is_whitespace);
        let pred_str = parts
            .next()
            .ok_or_else(|| self.err_parse(lineno, "fcmp: missing predicate"))?;
        let rest2 = parts
            .next()
            .ok_or_else(|| self.err_parse(lineno, "fcmp: missing operands"))?
            .trim();

        // Handle the two trivial constant predicates without touching
        // the operand types — the operands are still required to be
        // well-typed but their values are dead.
        if pred_str == "true" || pred_str == "false" {
            let (ty_str, operands) = split_ty_operand(rest2)?;
            let ty = parse_ty(&ty_str)?;
            if !matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
                return Err(self.err_unsupported(&format!("fcmp on non-float type `{}`", ty_str)));
            }
            // Force-evaluate both operands so any forward-declared SSA
            // names are still interned (matches integer `icmp` handling).
            if let Some((lhs_s, rhs_s)) = split_comma(&operands) {
                let _ = self.lookup_operand(&lhs_s, &ty, f);
                let _ = self.lookup_operand(&rhs_s, &ty, f);
            }
            let name = result.ok_or_else(|| self.err_parse(lineno, "fcmp without result"))?;
            let dest = f.intern_value(&name);
            f.push_inst(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(pred_str == "true"),
                })
                .with_result(dest),
            );
            return Ok(());
        }

        // `ord` / `uno`: implement via the self-comparison trick.
        //
        //   %o = fcmp ord TY %a, %b
        //     ≡ (a == a) && (b == b)    (both non-NaN)
        //     ≡ FCmp OEq a,a  AND  FCmp OEq b,b
        //
        //   %u = fcmp uno TY %a, %b
        //     ≡ (a != a) || (b != b)    (either is NaN)
        //     ≡ FCmp UNe a,a  OR   FCmp UNe b,b
        //
        // These patterns compile through the AArch64 lowering path
        // because they are expressed entirely in terms of already-
        // supported `FCmp` + integer `BinOp::{And,Or}` on i1.
        if pred_str == "ord" || pred_str == "uno" {
            let (ty_str, operands) = split_ty_operand(rest2)?;
            let ty = parse_ty(&ty_str)?;
            if !matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
                return Err(self.err_unsupported(&format!("fcmp on non-float type `{}`", ty_str)));
            }
            let (lhs_str, rhs_str) = split_comma(&operands)
                .ok_or_else(|| self.err_parse(lineno, "fcmp: expected `%a, %b`"))?;
            let a = self.lookup_operand(&lhs_str, &ty, f)?;
            let b = self.lookup_operand(&rhs_str, &ty, f)?;
            let (per_side_op, combine) = if pred_str == "ord" {
                (FCmpOp::OEq, BinOp::And)
            } else {
                (FCmpOp::UNe, BinOp::Or)
            };
            let aa = f.fresh_value();
            f.push_inst(
                InstrNode::new(Inst::FCmp {
                    op: per_side_op,
                    ty: ty.clone(),
                    lhs: a,
                    rhs: a,
                })
                .with_result(aa),
            );
            let bb = f.fresh_value();
            f.push_inst(
                InstrNode::new(Inst::FCmp {
                    op: per_side_op,
                    ty,
                    lhs: b,
                    rhs: b,
                })
                .with_result(bb),
            );
            let name = result.ok_or_else(|| self.err_parse(lineno, "fcmp without result"))?;
            let dest = f.intern_value(&name);
            f.push_inst(
                InstrNode::new(Inst::BinOp {
                    op: combine,
                    ty: Ty::Bool,
                    lhs: aa,
                    rhs: bb,
                })
                .with_result(dest),
            );
            return Ok(());
        }

        let pred = match pred_str {
            "oeq" => FCmpOp::OEq,
            "one" => FCmpOp::ONe,
            "olt" => FCmpOp::OLt,
            "ole" => FCmpOp::OLe,
            "ogt" => FCmpOp::OGt,
            "oge" => FCmpOp::OGe,
            "ueq" => FCmpOp::UEq,
            "une" => FCmpOp::UNe,
            "ult" => FCmpOp::ULt,
            "ule" => FCmpOp::ULe,
            "ugt" => FCmpOp::UGt,
            "uge" => FCmpOp::UGe,
            other => {
                return Err(self.err_unsupported(&format!("fcmp predicate `{}`", other)));
            }
        };
        let (ty_str, operands) = split_ty_operand(rest2)?;
        let ty = parse_ty(&ty_str)?;
        if !matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
            return Err(self.err_unsupported(&format!("fcmp on non-float type `{}`", ty_str)));
        }
        let (lhs_str, rhs_str) = split_comma(&operands)
            .ok_or_else(|| self.err_parse(lineno, "fcmp: expected `%a, %b`"))?;
        let lhs = self.lookup_operand(&lhs_str, &ty, f)?;
        let rhs = self.lookup_operand(&rhs_str, &ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "fcmp without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::FCmp {
                op: pred,
                ty,
                lhs,
                rhs,
            })
            .with_result(dest),
        );
        Ok(())
    }

    /// Emit a byte-sized (`i8`) stack slot of `size_bytes` bytes for an
    /// aggregate alloca (`alloca %struct.foo` or `alloca [N x T]`). trust_ir
    /// models aggregates on the stack as raw byte buffers; GEPs into the slot
    /// compute explicit byte offsets. `parts[1..]` carry the optional `align`
    /// clause and (rarely) an element-count operand, which multiplies the
    /// per-element `size_bytes`. `ctx` names the aggregate kind for error text.
    fn emit_aggregate_byte_alloca(
        &mut self,
        size_bytes: u64,
        parts: &[String],
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
        ctx: &str,
    ) -> Result<()> {
        let mut align = None;
        let mut count_clause: Option<String> = None;
        for clause in parts.iter().skip(1) {
            let clause = clause.trim();
            if clause.is_empty() {
                continue;
            }
            if clause.starts_with("align ") {
                if align.is_some() {
                    return Err(
                        self.err_unsupported(&format!("{ctx} alloca with multiple align clauses"))
                    );
                }
                align = Some(
                    parse_align_clause(clause)
                        .ok_or_else(|| self.err_parse(lineno, "alloca: malformed align clause"))?,
                );
            } else if count_clause.is_none() {
                count_clause = Some(clause.to_string());
            } else {
                return Err(
                    self.err_unsupported(&format!("{ctx} alloca with multiple count operands"))
                );
            }
        }

        let size_value = self.emit_i64_const(size_bytes as i128, f);
        let count = if let Some(clause) = count_clause {
            let (count_ty_str, count_tok) = split_ty_operand(&clause)?;
            let count_ty = parse_ty(&count_ty_str)?;
            if !is_integer_ty(&count_ty) {
                return Err(
                    self.err_unsupported(&format!("{ctx} alloca count type `{}`", count_ty_str))
                );
            }
            if let Some(n) = parse_int_literal(&count_tok) {
                if n < 0 {
                    return Err(self.err_unsupported(&format!("{ctx} alloca with negative count")));
                }
                let total = (size_bytes as i128).checked_mul(n).ok_or_else(|| {
                    self.err_unsupported(&format!("{ctx} alloca byte count overflow"))
                })?;
                Some(self.emit_i64_const(total, f))
            } else {
                let raw_count = self.lookup_operand(&count_tok, &count_ty, f)?;
                let widened_count = self.coerce_int_to_i64(raw_count, &count_ty, f)?;
                let total = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I64,
                        lhs: widened_count,
                        rhs: size_value,
                    })
                    .with_result(total),
                );
                Some(total)
            }
        } else {
            Some(size_value)
        };

        let name = result.ok_or_else(|| self.err_parse(lineno, "alloca without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I8,
                count,
                align,
            })
            .with_result(dest),
        );
        Ok(())
    }

    fn parse_alloca(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // `alloca <ty>, align N`  or  `alloca <ty>`.
        let tail = rest.trim_start_matches("alloca").trim();
        let parts = split_call_args(tail);
        let ty_str = parts.first().map(|s| s.trim()).unwrap_or("");
        if ty_str.is_empty() {
            return Err(self.err_parse(lineno, "alloca: missing type"));
        }
        if ty_str.starts_with('%') {
            let _ = self.parse_ty_ctx(ty_str)?;
            if let Some(layout) = self.struct_layouts.get(ty_str).cloned() {
                return self.emit_aggregate_byte_alloca(
                    layout.size,
                    &parts,
                    result,
                    lineno,
                    f,
                    "struct",
                );
            }
        }
        // Array / nested-aggregate alloca: `alloca [N x T], align A`. Route
        // through the same byte-sized-slot lowering as struct allocas; the
        // exact Apple arm64 layout comes from `parse_fixed_array_layout`.
        if ty_str.starts_with('[')
            && let Some(layout) = self.parse_fixed_array_layout(ty_str)?
        {
            return self.emit_aggregate_byte_alloca(
                layout.size(),
                &parts,
                result,
                lineno,
                f,
                "array",
            );
        }
        let ty = parse_ty(ty_str)?;
        let mut align = None;
        let mut count_clause: Option<String> = None;
        for clause in parts.iter().skip(1) {
            let clause = clause.trim();
            if clause.is_empty() {
                continue;
            }
            if clause.starts_with("align ") {
                if align.is_some() {
                    return Err(self.err_unsupported("alloca with multiple align clauses"));
                }
                align = Some(
                    parse_align_clause(clause)
                        .ok_or_else(|| self.err_parse(lineno, "alloca: malformed align clause"))?,
                );
            } else if count_clause.is_none() {
                count_clause = Some(clause.to_string());
            } else {
                return Err(self.err_unsupported("alloca with multiple count operands"));
            }
        }
        let count = count_clause
            .as_deref()
            .map(|clause| emit_alloca_count(self, clause, lineno, f, "alloca"))
            .transpose()?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "alloca without result"))?;
        let dest = f.intern_value(&name);
        let is_pointer_slot = matches!(ty, Ty::Ptr);
        f.push_inst(InstrNode::new(Inst::Alloca { ty, count, align }).with_result(dest));
        if is_pointer_slot {
            f.record_pointer_stack_slot(dest);
        }
        Ok(())
    }

    fn parse_load(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // `load [volatile] <ty>, ptr %p, align N`  (LLVM ≥ 15 opaque pointer form)
        let tail = rest.trim_start_matches("load").trim();
        // `volatile` is preserved EXACTLY on the trust_ir Load (not dropped): the
        // qualifier appears immediately after `load`, before the type.
        let (volatile, tail) = match tail.strip_prefix("volatile ") {
            Some(rest) => (true, rest.trim_start()),
            None => (false, tail),
        };
        let (ty_str, rest2) = split_comma(tail)
            .ok_or_else(|| self.err_parse(lineno, "load: expected `<ty>, ptr %p`"))?;
        let ty = parse_ty(&ty_str)?;
        // The next portion is `ptr %p` possibly followed by `, align N`. Split
        // paren-aware so an inline `getelementptr (i8, ptr @g, i64 N)` const-
        // expression pointer (whose body has commas) survives intact.
        let ptr_part = split_comma(&rest2)
            .map(|(head, _)| head)
            .unwrap_or_else(|| rest2.trim().to_string());
        let (_, ptr_tok) = split_ty_operand(&ptr_part)?;
        let ptr = self.lookup_operand(&ptr_tok, &Ty::Ptr, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "load without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::Load {
                ty,
                ptr,
                volatile,
                align: None,
            })
            .with_result(dest),
        );
        Ok(())
    }

    fn parse_store(&mut self, rest: &str, lineno: usize, f: &mut FuncScratch) -> Result<()> {
        // `store [volatile] <ty> <val>, ptr %p, align N`
        let tail = rest.trim_start_matches("store").trim();
        // `volatile` is preserved EXACTLY on the trust_ir Store, not dropped.
        let (volatile, tail) = match tail.strip_prefix("volatile ") {
            Some(rest) => (true, rest.trim_start()),
            None => (false, tail),
        };
        let (val_part, rest2) = split_comma(tail)
            .ok_or_else(|| self.err_parse(lineno, "store: expected `<ty> <val>, ptr %p`"))?;
        let (ty_str, val_tok) = split_ty_operand(&val_part)?;
        let ty = parse_ty(&ty_str)?;
        let value = self.lookup_operand(&val_tok, &ty, f)?;
        // Paren-aware so an inline `getelementptr (...)` const-expr pointer
        // (comma-bearing body) is not truncated at its first inner comma.
        let ptr_part = split_comma(&rest2)
            .map(|(head, _)| head)
            .unwrap_or_else(|| rest2.trim().to_string());
        let (_, ptr_tok) = split_ty_operand(&ptr_part)?;
        let ptr = self.lookup_operand(&ptr_tok, &Ty::Ptr, f)?;
        f.push_inst(InstrNode::new(Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align: None,
        }));
        Ok(())
    }

    /// Parse and resolve a call's `(<args>)` list into parallel value/type
    /// vectors. Each arg is `<ty> [attrs...] <operand>` — the type is the first
    /// token and the operand the last; parameter attributes are dropped. An
    /// inline `getelementptr (...)` const-expr addressing a global is folded via
    /// `lookup_operand`; any other inline const-expr fails closed. Shared by the
    /// direct and indirect call paths.
    fn parse_call_arg_list(
        &mut self,
        args_str: &str,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<(Vec<ValueId>, Vec<Ty>)> {
        let arg_toks = split_call_args(args_str);
        let mut args: Vec<ValueId> = Vec::with_capacity(arg_toks.len());
        let mut arg_tys: Vec<Ty> = Vec::with_capacity(arg_toks.len());
        for tok in arg_toks {
            let trimmed = tok.trim();
            if trimmed.is_empty() {
                continue;
            }
            if let Some(kind) = constant_expr_operand_kind(trimmed) {
                // `getelementptr (...)` const-expr addressing a global folds to
                // the global's base address plus a constant byte offset — the one
                // const-expr the importer evaluates (clang emits it for
                // `&global[k]`). Route it through `lookup_operand`, which requires
                // a pointer result type.
                if kind == "getelementptr"
                    && let Some(gep_start) = trimmed.find("getelementptr")
                {
                    let aty = parse_ty(trimmed.split_whitespace().next().unwrap_or(""))?;
                    let v = self.lookup_operand(&trimmed[gep_start..], &aty, f)?;
                    args.push(v);
                    arg_tys.push(aty);
                    continue;
                }
                // Any other inline const-expr (`inttoptr`, `bitcast`, non-global
                // GEP, …) has no evaluator. Fail closed rather than crash on the
                // mangled `to ptr)` tail.
                return Err(self.err_unsupported(&format!(
                    "constant-expression call argument `{kind} (...)` (no constant-folding evaluator)"
                )));
            }
            let toks: Vec<&str> = trimmed.split_whitespace().collect();
            if toks.len() < 2 {
                return Err(
                    self.err_parse(lineno, &format!("call arg needs `<ty> <val>`: `{}`", tok))
                );
            }
            let aty = parse_ty(toks[0])?;
            let aval = toks.last().copied().unwrap_or("");
            let v = self.lookup_operand(aval, &aty, f)?;
            args.push(v);
            arg_tys.push(aty);
        }
        Ok((args, arg_tys))
    }

    /// Lower an INDIRECT call — `[tail] call <ret-ty> %callee(<args>) [#attrs]` —
    /// to `Inst::CallIndirect`. The callee `%value` is a function pointer (a
    /// vtable/method-table slot loaded as `ptr`); the standard C ABI applies (the
    /// same one direct calls use). The call signature (arg types + return type)
    /// is registered as a `FuncTyId`, which the adapter cross-checks against the
    /// callee value type and argument arity/types.
    ///
    /// The explicit vararg func-type form `<ret> (<params>, ...) %fp(...)` fails
    /// closed: the adapter does not lower an indirect VARIADIC call.
    fn parse_indirect_call(
        &mut self,
        tail: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let (callee_start, paren_open) = find_indirect_callee(tail)
            .ok_or_else(|| self.err_unsupported("indirect call / call on %value"))?;
        let prefix = tail[..callee_start].trim();
        let callee_tok = tail[callee_start..paren_open].trim();

        // Return type: first type-looking token in the prefix. Handles
        // `ptr %16`, `signext i8 %19`, `void %fp`, `i32 (ptr, ...) %fp`.
        let ret_ty_str = prefix
            .split_whitespace()
            .find(|t| is_type_token(t) || *t == "void")
            .unwrap_or("")
            .to_string();
        let ret_ty = if ret_ty_str == "void" || ret_ty_str.is_empty() {
            None
        } else {
            Some(parse_ty(&ret_ty_str)?)
        };

        // An explicit `(<params>, ...)` func type before the callee marks a
        // variadic indirect call, which the adapter fails closed on.
        if parse_explicit_call_func_type(prefix).is_some_and(|(_, is_vararg)| is_vararg) {
            return Err(self.err_unsupported(
                "indirect variadic call (indirect ... %fp with `...` signature)",
            ));
        }

        let paren_close_rel = find_matching_paren(&tail[paren_open..])
            .ok_or_else(|| self.err_parse(lineno, "indirect call: unbalanced parens"))?;
        let args_str = &tail[paren_open + 1..paren_open + paren_close_rel];
        let (args, arg_tys) = self.parse_call_arg_list(args_str, lineno, f)?;

        // The callee is a code pointer (function-pointer value).
        let callee = self.lookup_operand(callee_tok, &Ty::Ptr, f)?;

        // Register the call signature so the adapter can validate the edge.
        let ft = FuncTy {
            params: arg_tys,
            returns: ret_ty.iter().cloned().collect(),
            is_vararg: false,
        };
        let sig = self.module.add_func_type(ft);
        let node = Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv: CallingConv::C,
        };
        match result {
            Some(name) if ret_ty.is_some() => {
                let dest = f.intern_value(&name);
                f.push_inst(InstrNode::new(node).with_result(dest));
            }
            _ => {
                f.push_inst(InstrNode::new(node));
            }
        }
        Ok(())
    }

    fn parse_call(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // `call <ret-ty> @name(<args>)` possibly prefixed with `tail` / `notail`
        // / `musttail` / calling-conv attributes. A `call <ret-ty> %value(<args>)`
        // is an INDIRECT call (function-pointer dispatch), handled separately.
        let mut tail = rest.trim_start_matches("call").trim();
        for prefix in ["tail ", "notail ", "musttail "] {
            if let Some(t) = tail.strip_prefix(prefix) {
                tail = t.trim_start();
            }
        }
        // Strip calling-conv / function attrs tokens that clang -O0 emits
        // between `call` and the return type (e.g. `void @foo(...)` vs
        // `i32 @bar(...)` vs `dso_local i32 @baz(...)`).
        //
        // Clang also emits an explicit function-type form for vararg
        // calls:
        //
        //     call i32 (ptr, ...) @printf(ptr noundef @.str, ...)
        //
        // We find the first `@` at the top level (not inside `(...)`),
        // which reliably points at the callee. Any `(...)` block before
        // it is the explicit function type and is ignored — we recover
        // the return type as the first type-looking token in the prefix.
        // No top-level `@` means the callee is a `%value`: an indirect call.
        let Some(at) = find_top_level_at(tail) else {
            return self.parse_indirect_call(tail, result, lineno, f);
        };
        let prefix = tail[..at].trim();
        let callee_region = &tail[at..];

        // Find the return type: walk `prefix` token-by-token and pick
        // the first token recognised by `is_type_token`. This handles
        // all three shapes:
        //   `i32 @foo(...)`           -> "i32"
        //   `dso_local i32 @foo(...)` -> "i32"
        //   `i32 (ptr, ...) @printf`  -> "i32"
        //   `void @foo(...)`          -> "void"
        let ret_ty_str = prefix
            .split_whitespace()
            .find(|t| is_type_token(t) || *t == "void")
            .unwrap_or("")
            .to_string();
        let ret_ty = if ret_ty_str == "void" || ret_ty_str.is_empty() {
            None
        } else {
            Some(parse_ty(&ret_ty_str)?)
        };

        // callee_region is `@name(<args>) [#attrs]`.
        let paren_open = callee_region
            .find('(')
            .ok_or_else(|| self.err_parse(lineno, "call: missing `(`"))?;
        let mut callee_name = callee_region[1..paren_open].trim().to_string();
        // De-mangle a `\01` asm-label callee spelling (e.g. `@"\01_clock"`) to
        // the verbatim symbol BEFORE the libm/`@llvm.*` classification below, and
        // note its origin so a colliding plain `@clock` fails closed. Non-`\01`
        // names (including `@llvm.*`) pass through unchanged.
        callee_name = self.canon_and_note_symbol(&callee_name)?;
        // Libm math intrinsics (`@llvm.sin.f64`, `@llvm.pow.f32`, …) have no
        // native machine encoding: LLVM's own `-O1` lowering rewrites them to a
        // call to the corresponding C99 libm symbol (`sin`, `powf`, …) resolved
        // out of the target's math library. Do the SAME rewrite here, BEFORE the
        // `@llvm.*` classification below: renaming the callee to the libm symbol
        // turns the intrinsic into an ordinary Call to a linkable external, so no
        // undefined `_llvm.sin.f64` symbol ever escapes. Because trust-cg and
        // clang link the identical libSystem libm, the result is bit-exact with
        // the `clang -O3` reference. The `.f64`/`.f32` suffix selects the
        // double vs `f`-suffixed float entry point.
        let mut was_libm_intrinsic_rewrite = false;
        if let Some(libm) = libm_intrinsic_symbol(&callee_name) {
            // Record the intrinsic origin for libm purity licensing (finalized
            // in `apply_libm_purity_licenses` once all declares/uses are seen).
            self.libm_rewritten_calls
                .insert(libm.to_string(), callee_name.clone());
            callee_name = libm.to_string();
            was_libm_intrinsic_rewrite = true;
        }
        // LLVM intrinsic calls (`@llvm.*`) fall into three classes:
        //
        //  1. Pure runtime no-ops (stack `lifetime` markers, `dbg` records,
        //     `assume`/`donothing` hints, prefetch): DROP them. Removing a
        //     no-op preserves observable behavior exactly.
        //
        //  2. Intrinsics that `trust-cg-lower`'s adapter recognizes by name and
        //     rewrites to a specialized machine opcode (`llvm.memcpy/memmove/
        //     memset.*` -> Memcpy/Memmove/Memset libcalls, `llvm.bitreverse.i32/
        //     i64` -> RBIT, `llvm.objectsize.*` -> constant fold): emit an
        //     ordinary Call to the intrinsic symbol and let the adapter lower it.
        //     Widths/names MUST match the adapter's recognizers exactly.
        //
        //  3. Everything else: fail closed. Emitting a plain Call would leave an
        //     undefined `_llvm.*` symbol that fails to LINK. A `@llvm.*` call the
        //     backend cannot lower can never be part of a passing program, so
        //     rejecting here only converts a latent link failure into an honest
        //     `unsupported`.
        if callee_name.starts_with("llvm.") {
            if is_droppable_intrinsic(&callee_name) {
                return Ok(());
            }
            if !is_lowered_passthrough_intrinsic(&callee_name)
                && !is_importer_lowered_intrinsic(&callee_name)
                && !is_memset_pattern_intrinsic(&callee_name)
            {
                return Err(self.err_unsupported(&format!(
                    "LLVM intrinsic call `@{}` (no intrinsic lowering)",
                    callee_name
                )));
            }
            // class 2/4: fall through — pass-through intrinsics emit an ordinary
            // Call; importer-lowered intrinsics (min/max/fabs) are rewritten to
            // primitive trust_ir ops after the arguments are parsed below.
        }
        let paren_close_rel = find_matching_paren(&callee_region[paren_open..])
            .ok_or_else(|| self.err_parse(lineno, "call: unbalanced parens"))?;
        let args_str = &callee_region[paren_open + 1..paren_open + paren_close_rel];
        let call_attrs = callee_region[paren_open + paren_close_rel + 1..].trim();

        // `llvm.mem{cpy,move,set}.*`: the final argument is the
        // REQUIRED-immediate `i1 <volatile>` flag (LLVM LangRef). The
        // adapter's Memcpy/Memmove/Memset lowering and the aarch64 ISel's
        // exact-3 arity contract take `(dest, src|val, len)` only — drop a
        // literal `i1 false` HERE, where the text is still visible. Fail
        // closed on `i1 true` (a VOLATILE mem operation must not be elided,
        // split or reordered — no sound specialized lowering exists) and on
        // any non-literal flag (the LangRef requires an immediate, so
        // anything else is malformed input).
        let mem_prefix = ["llvm.memcpy.", "llvm.memmove.", "llvm.memset."]
            .iter()
            .any(|p| callee_name.starts_with(p));
        let args_str = if mem_prefix {
            // The flag may carry parameter attributes between the type and
            // the literal (`i1 noundef false`): accept `i1 <attrs...> false`,
            // reject `... true`, fail closed on anything else.
            let split = args_str.rsplit_once(',');
            let tail_tokens: Vec<&str> = split
                .map(|(_, tail)| tail.split_whitespace().collect())
                .unwrap_or_default();
            match (split, tail_tokens.first(), tail_tokens.last()) {
                (Some((head, _)), Some(&"i1"), Some(&"false")) => head,
                (Some(_), Some(&"i1"), Some(&"true")) => {
                    return Err(self.err_unsupported(&format!(
                        "volatile `@{callee_name}` (i1 true) — no sound specialized lowering"
                    )));
                }
                _ => {
                    return Err(self.err_parse(
                        lineno,
                        "llvm.mem* intrinsic without a literal `i1 <volatile>` final argument",
                    ));
                }
            }
        } else {
            args_str
        };

        // Split + resolve the call arguments (shared with the indirect path).
        let (args, arg_tys) = self.parse_call_arg_list(args_str, lineno, f)?;

        // Class 4: intrinsics we rewrite to primitive trust_ir ops. These are
        // EXACT lowerings (no ABI/library dependency), so they run identically
        // to LLVM's own expansion.
        if callee_name.starts_with("llvm.") {
            if is_memset_pattern_intrinsic(&callee_name) {
                return self.emit_memset_pattern(&args, &arg_tys, result, lineno, f);
            }
            if let Some(cmp) = minmax_intrinsic_predicate(&callee_name) {
                // `llvm.{s,u}{max,min}.iN(a, b)` == `select (icmp <cmp> a, b), a, b`.
                let ty = arg_tys
                    .first()
                    .cloned()
                    .ok_or_else(|| self.err_parse(lineno, "min/max intrinsic needs 2 args"))?;
                if args.len() != 2 {
                    return Err(self.err_parse(lineno, "min/max intrinsic needs exactly 2 args"));
                }
                let name = result
                    .ok_or_else(|| self.err_parse(lineno, "min/max intrinsic without result"))?;
                let cond = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::ICmp {
                        op: cmp,
                        ty: ty.clone(),
                        lhs: args[0],
                        rhs: args[1],
                    })
                    .with_result(cond),
                );
                let dest = f.intern_value(&name);
                f.push_inst(
                    InstrNode::new(Inst::Select {
                        ty,
                        cond,
                        then_val: args[0],
                        else_val: args[1],
                    })
                    .with_result(dest),
                );
                return Ok(());
            }
            if callee_name.starts_with("llvm.abs.") {
                // `llvm.abs.iN(x, is_int_min_poison)` ==
                //   `select (icmp slt x, 0), (sub 0, x), x`.
                // The 2nd arg (poison-on-INT_MIN, an i1) is advisory only:
                // computing the wrapping two's-complement value
                // (abs(INT_MIN) == INT_MIN) is always sound, matching what LLVM
                // materializes when the poison flag is false.
                let ty = arg_tys
                    .first()
                    .cloned()
                    .ok_or_else(|| self.err_parse(lineno, "abs intrinsic needs an argument"))?;
                if args.is_empty() {
                    return Err(self.err_parse(lineno, "abs intrinsic needs at least 1 arg"));
                }
                let name =
                    result.ok_or_else(|| self.err_parse(lineno, "abs intrinsic without result"))?;
                let x = args[0];
                let zero = self.lookup_operand("0", &ty, f)?;
                let cond = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Slt,
                        ty: ty.clone(),
                        lhs: x,
                        rhs: zero,
                    })
                    .with_result(cond),
                );
                let neg = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: ty.clone(),
                        lhs: zero,
                        rhs: x,
                    })
                    .with_result(neg),
                );
                let dest = f.intern_value(&name);
                f.push_inst(
                    InstrNode::new(Inst::Select {
                        ty,
                        cond,
                        then_val: neg,
                        else_val: x,
                    })
                    .with_result(dest),
                );
                return Ok(());
            }
            if callee_name.starts_with("llvm.fabs.") {
                // `llvm.fabs.fN(x)` == trust_ir `UnOp::FAbs` (clear the sign bit).
                let ty = arg_tys
                    .first()
                    .cloned()
                    .ok_or_else(|| self.err_parse(lineno, "fabs intrinsic needs 1 arg"))?;
                let name = result
                    .ok_or_else(|| self.err_parse(lineno, "fabs intrinsic without result"))?;
                let dest = f.intern_value(&name);
                f.push_inst(
                    InstrNode::new(Inst::UnOp {
                        op: UnOp::FAbs,
                        ty,
                        operand: args[0],
                    })
                    .with_result(dest),
                );
                return Ok(());
            }
            if let Some(unop) = fp_unary_intrinsic_op(&callee_name) {
                // `llvm.sqrt/floor/ceil/trunc.fN(x)` map 1:1 to the trust_ir
                // native FP unary ops (`FSqrt`->FSQRT, `FFloor`->FRINTM,
                // `FCeil`->FRINTP, `FTrunc`->FRINTZ). These are exact IEEE
                // `roundToIntegral`/`fp.sqrt` operations with a mandatory AArch64
                // encoding, so — like `clang -O3`, which lowers the same
                // intrinsics to the same instructions — no libm call is needed
                // and the result is bit-exact.
                let ty = arg_tys
                    .first()
                    .cloned()
                    .ok_or_else(|| self.err_parse(lineno, "fp unary intrinsic needs 1 arg"))?;
                if args.is_empty() {
                    return Err(self.err_parse(lineno, "fp unary intrinsic needs at least 1 arg"));
                }
                let name = result
                    .ok_or_else(|| self.err_parse(lineno, "fp unary intrinsic without result"))?;
                let dest = f.intern_value(&name);
                f.push_inst(
                    InstrNode::new(Inst::UnOp {
                        op: unop,
                        ty,
                        operand: args[0],
                    })
                    .with_result(dest),
                );
                return Ok(());
            }
            if let Some(is_left) = funnel_shift_is_left(&callee_name) {
                // Funnel shift. `llvm.fshl.iN(a, b, c)` concatenates {a:b} into a
                // 2N-bit value and shifts LEFT by `c mod N`, returning the high N
                // bits; `llvm.fshr` shifts RIGHT and returns the low N bits. N is
                // a power of two, so `c mod N == c & (N-1)`.
                //
                // We use LLVM's own branchless power-of-two expansion, which
                // never shifts by a full width (undefined for a lone shift):
                //
                //   sh  = c & (N-1)            // shift amount, in [0, N-1]
                //   inv = sh ^ (N-1)           // == (N-1) - sh, also in [0, N-1]
                //   fshl = (a << sh) | ((b >> 1) >> inv)
                //          // (b>>1)>>inv == b >> (N - sh) for sh>0; == 0 for sh==0 -> a
                //   fshr = ((a << 1) << inv) | (b >> sh)
                //          // (a<<1)<<inv == a << (N - sh) for sh>0; == 0 for sh==0 -> b
                //
                // Every individual shift distance is < N, so each primitive shift
                // is well-defined; the composition reproduces the modular funnel
                // semantics EXACTLY (including the c==0 identity).
                if args.len() != 3 {
                    return Err(
                        self.err_parse(lineno, "funnel-shift intrinsic needs exactly 3 args")
                    );
                }
                let ty = arg_tys
                    .first()
                    .cloned()
                    .ok_or_else(|| self.err_parse(lineno, "funnel-shift intrinsic needs a type"))?;
                let bw = ty
                    .bit_width()
                    .filter(|w| w.is_power_of_two())
                    .ok_or_else(|| {
                        self.err_unsupported(
                            "funnel-shift on a non-power-of-two / non-integer width",
                        )
                    })?;
                let name = result.ok_or_else(|| {
                    self.err_parse(lineno, "funnel-shift intrinsic without result")
                })?;
                let (a, b, c) = (args[0], args[1], args[2]);
                // CONSTANT-ROTATE special case. When the two data operands are
                // the SAME value (`a == b` — a genuine rotate, not a two-input
                // funnel) AND the shift amount is a compile-time integer literal
                // `k0`, emit the plain literal rotate idiom
                //   fshl: (a << k) | (a >>u (N-k))    k = k0 & (N-1)
                //   fshr: (a >>u k) | (a << (N-k))
                // whose two shift distances are `Iconst`s. ISel's immediate-fold
                // (`iconst_origins`) then selects the `LslRI`/`LsrRI` immediate
                // shift forms, and the machine `rotate-idiom` pass rewrites the
                // resulting `OrrRR(LslRI, LsrRI)` triple into a single `RorRI` —
                // matching clang's `ror`/`eor …, ror #k`. The generic And/Xor
                // expansion below instead hides the distances behind data ops,
                // defeating both folds (it pins the loop-invariant amounts in
                // registers and emits variable `LslRR`/`LsrRR`): the salsa20 /
                // ChaCha ARX hot path. Because `k` is masked into `[0, N-1]` and
                // the non-zero branch uses distances `k` and `N-k` — each in
                // `[1, N-1]` — every primitive shift is well-defined and the
                // result is bit-for-bit identical to the generic expansion.
                if a == b {
                    // Recover the raw shift-amount token (3rd argument) and, when
                    // it is an integer literal, its value. `%`-values (variable
                    // amounts) and non-literal tokens parse to `None` and fall
                    // through to the generic expansion.
                    let const_shift = split_call_args(args_str)
                        .iter()
                        .map(|t| t.trim())
                        .filter(|t| !t.is_empty())
                        .nth(2)
                        .and_then(|t| t.split_whitespace().last())
                        .and_then(parse_int_literal);
                    if let Some(k0) = const_shift {
                        let k = (k0 & (bw as i128 - 1)) as u32; // k in [0, N-1]
                        if k == 0 {
                            // Rotate by 0 is the identity: the result *is* `a`.
                            // Bind the result name to `a` (no instructions). Fall
                            // through to the generic expansion only in the (phi-
                            // deferred, so effectively unreachable) event that the
                            // name was already bound by a forward reference.
                            if !f.value_map.contains_key(&name) {
                                f.value_map.insert(name.clone(), a);
                                return Ok(());
                            }
                        } else {
                            let n_minus_k = bw - k; // in [1, N-1]
                            // (left-shift distance, logical-right-shift distance)
                            let (lsl_amt, lsr_amt) = if is_left {
                                (k, n_minus_k) // fshl == rotate-left by k
                            } else {
                                (n_minus_k, k) // fshr == rotate-right by k
                            };
                            let lsl_c = self.lookup_operand(&lsl_amt.to_string(), &ty, f)?;
                            let lsr_c = self.lookup_operand(&lsr_amt.to_string(), &ty, f)?;
                            let lo = f.fresh_value();
                            f.push_inst(
                                InstrNode::new(Inst::BinOp {
                                    op: BinOp::Shl,
                                    ty: ty.clone(),
                                    lhs: a,
                                    rhs: lsl_c,
                                })
                                .with_result(lo),
                            );
                            let hi = f.fresh_value();
                            f.push_inst(
                                InstrNode::new(Inst::BinOp {
                                    op: BinOp::LShr,
                                    ty: ty.clone(),
                                    lhs: a,
                                    rhs: lsr_c,
                                })
                                .with_result(hi),
                            );
                            let dest = f.intern_value(&name);
                            f.push_inst(
                                InstrNode::new(Inst::BinOp {
                                    op: BinOp::Or,
                                    ty: ty.clone(),
                                    lhs: lo,
                                    rhs: hi,
                                })
                                .with_result(dest),
                            );
                            return Ok(());
                        }
                    }
                }
                let mask = self.lookup_operand(&(bw - 1).to_string(), &ty, f)?;
                let one = self.lookup_operand("1", &ty, f)?;
                let emit_bin = |f: &mut FuncScratch, op: BinOp, lhs: ValueId, rhs: ValueId| {
                    let v = f.fresh_value();
                    f.push_inst(
                        InstrNode::new(Inst::BinOp {
                            op,
                            ty: ty.clone(),
                            lhs,
                            rhs,
                        })
                        .with_result(v),
                    );
                    v
                };
                let sh = emit_bin(f, BinOp::And, c, mask);
                let inv = emit_bin(f, BinOp::Xor, sh, mask);
                let (hi, lo) = if is_left {
                    let lo = emit_bin(f, BinOp::Shl, a, sh); // a << sh
                    let b1 = emit_bin(f, BinOp::LShr, b, one); // b >> 1
                    let hi = emit_bin(f, BinOp::LShr, b1, inv); // (b>>1) >> inv
                    (hi, lo)
                } else {
                    let a1 = emit_bin(f, BinOp::Shl, a, one); // a << 1
                    let hi = emit_bin(f, BinOp::Shl, a1, inv); // (a<<1) << inv
                    let lo = emit_bin(f, BinOp::LShr, b, sh); // b >> sh
                    (hi, lo)
                };
                let dest = f.intern_value(&name);
                f.push_inst(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Or,
                        ty,
                        lhs: hi,
                        rhs: lo,
                    })
                    .with_result(dest),
                );
                return Ok(());
            }
        }

        // Look up or forward-declare the callee.
        let fid = if let Some(id) = self.func_ids.get(&callee_name) {
            *id
        } else {
            // Implicit declare-by-use (common for `printf` when clang emits
            // the declaration later). Prefer the explicit function-type
            // prefix (`i32 (ptr, ...) @printf`) when present so Darwin vararg
            // lowering knows how many leading args are fixed.
            let (params, is_vararg) = parse_explicit_call_func_type(prefix).unwrap_or_else(|| {
                let params = arg_tys.iter().cloned().map(|ty| (None, ty)).collect();
                (params, false)
            });
            let sig = FuncSignature {
                name: callee_name.clone(),
                ret: ret_ty.clone(),
                params,
                is_vararg,
                internal: false,
                stack_protector: ImportedStackProtectorAttr::None,
                libm_pure_math: false,
            };
            let fid = self.register_function(sig.clone())?;
            // A callee reached ONLY through declare-by-use (no explicit
            // `declare` line — e.g. a libm symbol synthesized by rewriting
            // `@llvm.sin.f64` to `sin`) still needs a body-less external
            // `Function` in the module, or the adapter rejects the Call as
            // referencing an unregistered FuncId. Mirror `parse_declare`'s
            // external stub. (When an explicit `declare` already added it, the
            // id-existence guard makes this a no-op.)
            if !self.module.functions.iter().any(|func| func.id == fid) {
                let mut func = Function::new(
                    fid,
                    sig.name.clone(),
                    self.func_tys[&sig.name],
                    BlockId::new(0),
                );
                func.calling_conv = CallingConv::C;
                func.linkage = Linkage::External;
                apply_function_attributes(&mut func, &sig);
                self.module.add_function(func);
            }
            fid
        };

        // Libm purity licensing: a DIRECT call that did NOT come from the
        // intrinsic rewrite is a plain use — it permanently disqualifies the
        // symbol from the libm-pure license (fail-closed).
        if !was_libm_intrinsic_rewrite {
            self.libm_plain_uses
                .borrow_mut()
                .insert(callee_name.clone());
        }
        let node = Inst::Call { callee: fid, args };
        match (result, ret_ty) {
            (Some(name), Some(return_ty)) => {
                let dest = f.intern_value(&name);
                let allocation_proofs = if matches!(return_ty, Ty::Ptr) {
                    imported_allocation_result_proofs(
                        &callee_name,
                        call_attrs,
                        &self.attribute_groups,
                    )
                } else {
                    Vec::new()
                };
                let mut instr = InstrNode::new(node).with_result(dest);
                for proof in allocation_proofs.iter().cloned() {
                    push_unique_proof(&mut instr.proofs, proof);
                }
                if !allocation_proofs.is_empty() {
                    f.record_imported_pointer_proofs(dest, allocation_proofs);
                }
                f.push_inst(instr);
            }
            (None, _) => {
                f.push_inst(InstrNode::new(node));
            }
            (Some(_), None) => {
                return Err(self.err_parse(lineno, "call of void function has a result"));
            }
        }
        Ok(())
    }

    fn parse_gep(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let tail = rest.trim_start_matches("getelementptr").trim();
        let (tail, is_inbounds) = if let Some(tail) = tail.strip_prefix("inbounds") {
            (tail.trim(), true)
        } else {
            (tail, false)
        };
        // LLVM ≥ 19 may follow `inbounds` with the pointer-arithmetic refinement
        // flags `nusw` / `nuw` (`getelementptr inbounds nuw ...`). Drop them: they
        // only assert the address computation does not wrap, so plain GEP
        // semantics are a sound over-approximation — dropping never miscompiles.
        let mut tail = tail;
        loop {
            let next = tail.split_whitespace().next().unwrap_or("");
            match next {
                "nusw" | "nuw" => tail = tail[next.len()..].trim_start(),
                _ => break,
            }
        }
        let (pointee_ty_str, after_pointee) =
            split_comma(tail).ok_or_else(|| self.err_parse(lineno, "gep: missing pointee type"))?;

        if pointee_ty_str.trim().starts_with('%') {
            let name = pointee_ty_str.trim();
            let _ = self.parse_ty_ctx(name)?;
            if let Some(layout) = self.struct_layouts.get(name).cloned() {
                let (base_part, indices_str) = split_comma(&after_pointee)
                    .ok_or_else(|| self.err_parse(lineno, "gep: missing base operand"))?;
                let (_, base_tok) = split_ty_operand(&base_part)?;
                // The base may be a local `%p` OR a module global `@g` (e.g.
                // `getelementptr %struct.S, ptr @g, i64 %i`). `lookup_operand`
                // materializes a global's base-address stub (offset 0, the form
                // codegen remaps to a real relocation) exactly as the constexpr-
                // GEP and fixed-array paths do; the byte offset below is applied
                // to that real address at run time.
                let base = self.lookup_operand(&base_tok, &Ty::Ptr, f)?;
                let indices = split_call_args(&indices_str);
                if indices.is_empty() || indices.len() > 2 {
                    return Err(self.err_unsupported(
                        "struct GEP requires one outer index and optional field index",
                    ));
                }

                let (outer_ty_str, outer_tok) = split_ty_operand(indices[0].trim())?;
                let outer_ty = parse_ty(&outer_ty_str)?;
                if !is_integer_ty(&outer_ty) {
                    return Err(self.err_unsupported(&format!(
                        "struct GEP outer index type `{}`",
                        outer_ty_str
                    )));
                }
                // The field index (if present) is ALWAYS a constant in valid LLVM
                // — a struct field cannot be dynamically indexed. Compute its
                // byte offset first; it is independent of the outer index.
                let field_offset = if let Some(field_clause) = indices.get(1) {
                    let (field_ty_str, field_tok) = split_ty_operand(field_clause.trim())?;
                    let field_ty = parse_ty(&field_ty_str)?;
                    if !is_integer_ty(&field_ty) {
                        return Err(self.err_unsupported(&format!(
                            "struct GEP field index type `{}`",
                            field_ty_str
                        )));
                    }
                    let field_idx = parse_int_literal(&field_tok).ok_or_else(|| {
                        self.err_unsupported("struct GEP with dynamic field index")
                    })?;
                    if field_idx < 0 {
                        return Err(self.err_unsupported("struct GEP with negative field index"));
                    }
                    let field_idx = field_idx as usize;
                    layout
                        .fields
                        .get(field_idx)
                        .map(|(_, off)| *off)
                        .ok_or_else(|| {
                            self.err_unsupported(&format!(
                                "struct GEP field index {} out of bounds for `{}`",
                                field_idx, name
                            ))
                        })?
                } else {
                    0
                };

                // The outer index scales by the WHOLE struct size (array-of-
                // struct stride, INCLUDING tail padding — `layout.size` is already
                // rounded up to the struct alignment). It may be a constant OR a
                // dynamic SSA value: `result = base + outer*sizeof(S) + field_off`.
                let offset_value = match parse_int_literal(&outer_tok) {
                    Some(outer) => {
                        // Constant outer index: fold the entire byte offset.
                        let offset = outer
                            .checked_mul(layout.size as i128)
                            .and_then(|n| n.checked_add(field_offset as i128))
                            .ok_or_else(|| {
                                self.err_unsupported("struct GEP byte offset overflow")
                            })?;
                        self.emit_i64_const(offset, f)
                    }
                    None => {
                        // Dynamic outer index: compute the byte offset at run time.
                        // GEP indices are sign-extended to pointer width, which
                        // `coerce_int_to_i64` does (and it fails closed on i128).
                        let raw_outer = self.lookup_operand(&outer_tok, &outer_ty, f)?;
                        let outer_val = self.coerce_int_to_i64(raw_outer, &outer_ty, f)?;
                        let stride = self.emit_i64_const(layout.size as i128, f);
                        let scaled = self.emit_i64_binop(BinOp::Mul, outer_val, stride, f);
                        if field_offset == 0 {
                            scaled
                        } else {
                            let foff = self.emit_i64_const(field_offset as i128, f);
                            self.emit_i64_binop(BinOp::Add, scaled, foff, f)
                        }
                    }
                };
                let name = result.ok_or_else(|| self.err_parse(lineno, "gep without result"))?;
                let dest = f.intern_value(&name);
                f.push_inst(add_inbounds_proof(
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I8,
                        base,
                        indices: vec![offset_value],
                        // Preserve the LLVM `getelementptr inbounds` flag
                        // verbatim (trust-ir GEP.inbounds). Faithful to source;
                        // defaults to the conservative `false` otherwise.
                        inbounds: is_inbounds,
                    })
                    .with_result(dest),
                    is_inbounds,
                ));
                return Ok(());
            }
        }

        if !tail.starts_with('[') {
            let pointee_ty = parse_ty(&pointee_ty_str)?;
            if scalar_layout(&pointee_ty).is_none() {
                return Err(self.err_unsupported(&format!(
                    "scalar pointer GEP pointee type `{:?}`",
                    pointee_ty
                )));
            }
            let (base_part, indices_str) = split_comma(&after_pointee)
                .ok_or_else(|| self.err_parse(lineno, "gep: missing base operand"))?;
            let (base_ty_str, base_tok) = split_ty_operand(&base_part)?;
            let base_ty = parse_ty(&base_ty_str)?;
            if !matches!(base_ty, Ty::Ptr) {
                return Err(self
                    .err_unsupported(&format!("scalar pointer GEP base type `{}`", base_ty_str)));
            }
            let indices = split_call_args(&indices_str);
            if indices.len() != 1 {
                return Err(self.err_unsupported("scalar pointer GEP requires exactly one index"));
            }
            let (index_ty_str, index_tok) = split_ty_operand(indices[0].trim())?;
            let index_ty = parse_ty(&index_ty_str)?;
            if !is_integer_ty(&index_ty) {
                return Err(self.err_unsupported(&format!(
                    "scalar pointer GEP index type `{}`",
                    index_ty_str
                )));
            }
            if matches!(index_ty, Ty::I128) {
                return Err(self.err_unsupported("scalar pointer GEP index with i128 type"));
            }
            let raw_index = self.lookup_operand(&index_tok, &index_ty, f)?;
            let index = self.coerce_int_to_i64(raw_index, &index_ty, f)?;
            let name = result.ok_or_else(|| self.err_parse(lineno, "gep without result"))?;
            let dest = f.intern_value(&name);
            let base = self.lookup_operand(&base_tok, &Ty::Ptr, f)?;
            f.push_inst(add_inbounds_proof(
                InstrNode::new(Inst::GEP {
                    pointee_ty,
                    base,
                    indices: vec![index],
                    // Preserve the LLVM `getelementptr inbounds` flag verbatim.
                    inbounds: is_inbounds,
                })
                .with_result(dest),
                is_inbounds,
            ));
            return Ok(());
        }
        if let Some(layout) = self.parse_fixed_array_layout(&pointee_ty_str)? {
            let (base_part, indices_str) = split_comma(&after_pointee)
                .ok_or_else(|| self.err_parse(lineno, "gep: missing base operand"))?;
            let (base_ty_str, base_tok) = split_ty_operand(&base_part)?;
            let base_ty = parse_ty(&base_ty_str)?;
            let indices = split_call_args(&indices_str);
            if base_tok.starts_with('@') && layout.is_top_i8_array() {
                if !matches!(base_ty, Ty::Ptr) {
                    return Err(self.err_unsupported(&format!(
                        "byte array global GEP base type `{}`",
                        base_ty_str
                    )));
                }
                if indices.len() != 2 {
                    return Err(self.err_unsupported(
                        "byte array global GEP requires leading zero and one element index",
                    ));
                }

                let (outer_ty_str, outer_tok) = split_ty_operand(indices[0].trim())?;
                let outer_ty = parse_ty(&outer_ty_str)?;
                if !is_integer_ty(&outer_ty) {
                    return Err(self.err_unsupported(&format!(
                        "byte array global GEP outer index type `{}`",
                        outer_ty_str
                    )));
                }
                let outer = parse_int_literal(&outer_tok).ok_or_else(|| {
                    self.err_unsupported("byte array global GEP dynamic outer index")
                })?;
                if outer != 0 {
                    return Err(
                        self.err_unsupported("byte array global GEP requires zero leading index")
                    );
                }

                let (index_ty_str, index_tok) = split_ty_operand(indices[1].trim())?;
                let index_ty = parse_ty(&index_ty_str)?;
                if !is_integer_ty(&index_ty) {
                    return Err(self.err_unsupported(&format!(
                        "byte array global GEP index type `{}`",
                        index_ty_str
                    )));
                }
                if matches!(index_ty, Ty::I128) {
                    return Err(self.err_unsupported("byte array global GEP index with i128 type"));
                }
                let raw_index = self.lookup_operand(&index_tok, &index_ty, f)?;
                let index = self.coerce_int_to_i64(raw_index, &index_ty, f)?;
                let name = result.ok_or_else(|| self.err_parse(lineno, "gep without result"))?;
                let dest = f.intern_value(&name);
                let base = self.lookup_operand(&base_tok, &Ty::Ptr, f)?;
                f.push_inst(add_inbounds_proof(
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I8,
                        base,
                        indices: vec![index],
                        // Preserve the LLVM `getelementptr inbounds` flag verbatim.
                        inbounds: is_inbounds,
                    })
                    .with_result(dest),
                    is_inbounds,
                ));
                return Ok(());
            }

            if !matches!(base_ty, Ty::Ptr) {
                return Err(
                    self.err_unsupported(&format!("fixed array GEP base type `{}`", base_ty_str))
                );
            }
            if !layout.supported_array_gep() {
                return Err(self.err_unsupported(&format!(
                    "fixed array GEP pointee type `{}`",
                    pointee_ty_str
                )));
            }

            let offset = self.emit_fixed_layout_gep_offset(&layout, &indices, f)?;
            let name = result.ok_or_else(|| self.err_parse(lineno, "gep without result"))?;
            let dest = f.intern_value(&name);
            let base = self.lookup_operand(&base_tok, &Ty::Ptr, f)?;
            f.push_inst(add_inbounds_proof(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I8,
                    base,
                    indices: vec![offset],
                    // Preserve the LLVM `getelementptr inbounds` flag verbatim.
                    inbounds: is_inbounds,
                })
                .with_result(dest),
                is_inbounds,
            ));
            return Ok(());
        }
        let ptr_pos = tail
            .find("ptr ")
            .ok_or_else(|| self.err_unsupported("GEP without `ptr` operand"))?;
        let after_ptr = &tail[ptr_pos + 4..];
        let base_tok = after_ptr.split(',').next().unwrap_or("").trim();
        if base_tok.starts_with('@') {
            return Err(self.err_unsupported(
                "address-of global (GEP on `@string`) — needs global-address materialization",
            ));
        }
        let name = result.ok_or_else(|| self.err_parse(lineno, "gep without result"))?;
        let dest = f.intern_value(&name);
        let base = self.lookup_operand(base_tok, &Ty::Ptr, f)?;
        f.push_inst(
            InstrNode::new(Inst::Copy {
                ty: Ty::Ptr,
                operand: base,
            })
            .with_result(dest),
        );
        Ok(())
    }

    /// Compute a deterministic, distinct, non-zero stub pointer value for
    /// `@<global_name>` at byte offset `offset` within the global.
    ///
    /// The importer does not yet carry a first-class trust_ir global-address
    /// operand through lower/codegen. For parser coverage we synthesize a
    /// pointer-sized constant that is distinct per global+offset and accepted
    /// by the lower adapter's `Ty::Ptr` integer-constant bounds check.
    fn global_addr_stub(&self, global_name: &str, offset: i128) -> Result<i128> {
        // De-mangle a `\01` asm-label data-global reference (e.g. `@"\01_x"`) so
        // it resolves against the canonical name stored at definition time. This
        // is the single choke point for global-address resolution; idempotent on
        // already-canonical names.
        let canon = self.canon_symbol_name(global_name)?;
        let global_name = canon.as_str();
        let idx = self.globals.get(global_name).copied().ok_or_else(|| {
            self.err_unsupported(&format!("address-of undeclared global `@{}`", global_name))
        })?;
        if idx >= (1 << 16) {
            return Err(self.err_unsupported(&format!(
                "too many globals ({}) for stub address synthesis",
                idx
            )));
        }
        let off_u32 = if (0..=(u32::MAX as i128)).contains(&offset) {
            offset as u64
        } else {
            return Err(self.err_unsupported(&format!(
                "global address offset {} out of range for stub synthesis",
                offset
            )));
        };
        let bits: u64 = (0xFADEu64 << 48) | ((idx as u64) << 32) | off_u32;
        Ok(bits as i128)
    }

    /// Parse an inline constant-expression GEP that addresses a module global —
    /// the one const-expr the importer evaluates — into `(global_name,
    /// byte_offset)`. clang -O1 canonicalizes these to the byte form
    /// `getelementptr inbounds nuw (i8, ptr @g, i64 N)`, but the general
    /// `(<ty>, ptr @g, <const indices...>)` shape is handled too. A non-constant
    /// index, a non-global base, or an unsupported base type fails CLOSED — the
    /// importer never emits a wrong fold.
    fn parse_constexpr_global_gep(&self, s: &str) -> Result<(String, i128)> {
        let rest = s
            .trim()
            .strip_prefix("getelementptr")
            .ok_or_else(|| self.err_unsupported("constexpr GEP: missing keyword"))?
            .trim_start();
        let open = rest
            .find('(')
            .ok_or_else(|| self.err_unsupported("constexpr GEP: missing `(`"))?;
        let close_rel = find_matching_paren(&rest[open..])
            .ok_or_else(|| self.err_unsupported("constexpr GEP: unbalanced parens"))?;
        let body = &rest[open + 1..open + close_rel];
        let parts = split_call_args(body);
        if parts.len() < 2 {
            return Err(self.err_unsupported("constexpr GEP: too few operands"));
        }
        let base_ty_str = parts[0].trim();
        // parts[1] is `ptr @g` (possibly with attributes) — extract the global.
        let base_ptr = parts[1].trim();
        let at = base_ptr
            .find('@')
            .ok_or_else(|| self.err_unsupported("constexpr GEP base is not a global address"))?;
        let global_name = base_ptr[at + 1..]
            .split(|c: char| c.is_whitespace() || c == ',' || c == ')')
            .next()
            .unwrap_or("")
            .to_string();
        // De-mangle a `\01` asm-label base spelling to the canonical name.
        let global_name = self.canon_symbol_name(&global_name)?;
        // Require the global to exist so a typo/undeclared base fails closed here.
        if !self.globals.contains_key(&global_name) {
            return Err(self.err_unsupported(&format!(
                "constexpr GEP on undeclared global `@{}`",
                global_name
            )));
        }
        let index_toks: Vec<&str> = parts[2..].iter().map(|p| p.trim()).collect();
        let layout = self.parse_fixed_layout_ty(base_ty_str)?;
        let offset = self.const_gep_byte_offset(&layout, &index_toks)?;
        Ok((global_name, offset))
    }

    /// Materialize the address of a constant-expression global GEP as trust_ir
    /// instructions. The base global is emitted at offset 0 — the only stub form
    /// the codegen adapter can remap to a real relocation — and a non-zero byte
    /// offset is added with an ordinary byte GEP (`pointee_ty: i8`, the same
    /// shape used for runtime array indexing into a global), so the offset is
    /// applied to the REAL address at run time rather than baked into the stub.
    fn emit_constexpr_global_gep(&self, s: &str, f: &mut FuncScratch) -> Result<ValueId> {
        let (global_name, offset) = self.parse_constexpr_global_gep(s)?;
        let base_addr = self.global_addr_stub(&global_name, 0)?;
        let base = f.fresh_value();
        f.push_inst(
            InstrNode::new(Inst::Const {
                ty: Ty::Ptr,
                value: Constant::Int(base_addr),
            })
            .with_result(base),
        );
        if offset == 0 {
            return Ok(base);
        }
        let offset_value = self.emit_i64_const(offset, f);
        let dest = f.fresh_value();
        f.push_inst(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base,
                indices: vec![offset_value],
                inbounds: true,
            })
            .with_result(dest),
        );
        Ok(dest)
    }

    /// Compute the constant byte offset of a GEP with all-constant indices, per
    /// LLVM semantics: the first index scales by the whole pointee size, each
    /// subsequent index descends one aggregate level (array element / struct
    /// field). A dynamic index or over-indexing a scalar fails closed.
    fn const_gep_byte_offset(&self, layout: &FixedLayout, index_toks: &[&str]) -> Result<i128> {
        if index_toks.is_empty() {
            return Err(self.err_unsupported("constexpr GEP requires at least one index"));
        }
        let const_index = |clause: &str| -> Result<i128> {
            let (ty_str, tok) = split_ty_operand(clause.trim())?;
            let ty = parse_ty(&ty_str)?;
            if !is_integer_ty(&ty) {
                return Err(self.err_unsupported("constexpr GEP index is not an integer"));
            }
            parse_int_literal(&tok)
                .ok_or_else(|| self.err_unsupported("constexpr GEP with non-constant index"))
        };
        let overflow = || self.err_unsupported("constexpr GEP byte offset overflow");

        let i0 = const_index(index_toks[0])?;
        let mut offset = i0.checked_mul(layout.size() as i128).ok_or_else(overflow)?;
        let mut current = layout;
        for clause in &index_toks[1..] {
            match current {
                FixedLayout::Array { elem, .. } => {
                    let next = elem.as_ref();
                    let i = const_index(clause)?;
                    offset = offset
                        .checked_add(i.checked_mul(next.size() as i128).ok_or_else(overflow)?)
                        .ok_or_else(overflow)?;
                    current = next;
                }
                FixedLayout::Struct { fields, .. } => {
                    let fidx = const_index(clause)?;
                    if fidx < 0 {
                        return Err(self.err_unsupported("constexpr GEP with negative field index"));
                    }
                    let field = fields.get(fidx as usize).ok_or_else(|| {
                        self.err_unsupported("constexpr GEP struct field index out of bounds")
                    })?;
                    offset = offset
                        .checked_add(field.offset as i128)
                        .ok_or_else(overflow)?;
                    current = &field.layout;
                }
                FixedLayout::Scalar(_) => {
                    return Err(
                        self.err_unsupported("constexpr GEP has too many indices for scalar")
                    );
                }
            }
        }
        Ok(offset)
    }

    fn parse_cast(
        &mut self,
        opcode: &str,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // Form: `<op> [flags] <src-ty> <val> to <dst-ty>`
        //
        // LLVM ≥ 18/19 emits poison-refinement flags between the cast opcode and
        // the source type: `zext nneg`, `trunc nuw`, `trunc nsw`. We DROP them —
        // dropping is CONSERVATIVE (never a soundness risk): a flag asserts the
        // operation stays in a narrower well-defined regime (non-negative source /
        // no wrap), so plain zext/trunc/sext semantics are defined on a SUPERSET of
        // the flagged inputs and agree with the flagged op wherever the flag's
        // precondition holds. We model no optimization info from the flags anyway.
        let tail = strip_cast_flags(rest.trim_start_matches(opcode).trim());
        let to_pos = tail
            .find(" to ")
            .ok_or_else(|| self.err_parse(lineno, "cast: missing `to`"))?;
        let head = &tail[..to_pos];
        let dst_ty_str = tail[to_pos + 4..].trim();
        let (src_ty_str, src_val) = split_ty_operand(head)?;
        let src_ty = parse_ty(&src_ty_str)?;
        let dst_ty = parse_ty(dst_ty_str)?;
        let op = match opcode {
            "sext" => CastOp::SExt,
            "zext" => CastOp::ZExt,
            "trunc" => CastOp::Trunc,
            "bitcast" => CastOp::Bitcast,
            "ptrtoint" => CastOp::PtrToInt,
            "inttoptr" => CastOp::IntToPtr,
            "sitofp" => CastOp::SIToFP,
            "uitofp" => CastOp::UIToFP,
            "fptosi" => CastOp::FPToSI,
            "fptoui" => CastOp::FPToUI,
            "fpext" => CastOp::FPExt,
            "fptrunc" => CastOp::FPTrunc,
            _ => unreachable!(),
        };
        let operand = self.lookup_operand(&src_val, &src_ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "cast without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            })
            .with_result(dest),
        );
        Ok(())
    }

    /// `%y = freeze <ty> <operand>`.
    ///
    /// `freeze` stops a poison/undef value from propagating: given a
    /// well-defined input it is the identity; given poison/undef it returns
    /// one arbitrary-but-fixed value of the type. trust_ir has no poison —
    /// the importer already materializes `undef`/`poison` operands as a
    /// concrete `Const 0` (see `lookup_operand`) — so `freeze` is exactly a
    /// `Copy` of the operand. This is a sound refinement: whichever concrete
    /// value flows in is a legal result of freezing it.
    fn parse_freeze(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let tail = rest.trim_start_matches("freeze").trim();
        let (ty_str, operand_str) = split_ty_operand(tail)?;
        let ty = parse_ty(&ty_str)?;
        let operand = self.lookup_operand(&operand_str, &ty, f)?;
        let name = result.ok_or_else(|| self.err_parse(lineno, "freeze without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(InstrNode::new(Inst::Copy { ty, operand }).with_result(dest));
        Ok(())
    }

    fn parse_select(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        // `select i1 %c, <ty> %a, <ty> %b`
        let tail = rest.trim_start_matches("select").trim();
        let parts: Vec<&str> = tail.splitn(3, ',').collect();
        if parts.len() != 3 {
            return Err(self.err_parse(lineno, "select: expected three comma-separated operands"));
        }
        let cond_part = parts[0].trim();
        let (cty, cval) = split_ty_operand(cond_part)?;
        let cond_ty = parse_ty(&cty)?;
        let cond = self.lookup_operand(&cval, &cond_ty, f)?;

        let (t_ty_str, t_val) = split_ty_operand(parts[1].trim())?;
        let t_ty = parse_ty(&t_ty_str)?;
        let t = self.lookup_operand(&t_val, &t_ty, f)?;

        let (_e_ty_str, e_val) = split_ty_operand(parts[2].trim())?;
        let e = self.lookup_operand(&e_val, &t_ty, f)?;

        let name = result.ok_or_else(|| self.err_parse(lineno, "select without result"))?;
        let dest = f.intern_value(&name);
        f.push_inst(
            InstrNode::new(Inst::Select {
                ty: t_ty,
                cond,
                then_val: t,
                else_val: e,
            })
            .with_result(dest),
        );
        Ok(())
    }

    fn parse_phi(
        &mut self,
        rest: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let tail = strip_fmath_flags(rest, "phi");
        let (ty_str, _) = split_ty_operand(tail)?;
        let ty = parse_ty(&ty_str)?;
        self.parse_phi_with_ty(tail, result, lineno, f, ty)
    }

    /// The body of [`Self::parse_phi`], with the block-parameter type supplied
    /// by the caller.
    ///
    /// `tail` is the phi text with the opcode and any fast-math flags already
    /// stripped. The native vector path calls this directly with a
    /// `Ty::Vector(..)` so the phi becomes ONE V128 block parameter instead of
    /// `lanes` scalar ones; every other caller passes `parse_ty`'s result and
    /// the behaviour is unchanged.
    fn parse_phi_with_ty(
        &mut self,
        tail: &str,
        result: Option<String>,
        lineno: usize,
        f: &mut FuncScratch,
        ty: Ty,
    ) -> Result<()> {
        let name = result.ok_or_else(|| self.err_parse(lineno, "phi without result"))?;
        let target = f
            .current
            .ok_or_else(|| self.err_parse(lineno, "phi outside block"))?;
        let target = BlockId::new(target as u32);

        let (_, incoming_str) = split_ty_operand(tail)?;
        let dest = f.intern_value(&name);
        f.blocks[target.as_usize()].params.push((dest, ty.clone()));

        let mut incomings = Vec::new();
        for raw in split_call_args(&incoming_str) {
            let item = raw
                .trim()
                .strip_prefix('[')
                .and_then(|s| s.trim().strip_suffix(']'))
                .ok_or_else(|| {
                    self.err_parse(lineno, &format!("phi: malformed incoming `{}`", raw))
                })?
                .trim();
            let (value_tok, pred_tok) = split_comma(item)
                .ok_or_else(|| self.err_parse(lineno, "phi: expected `[ value, %pred ]`"))?;
            let pred_label = pred_tok
                .trim()
                .trim_start_matches("label")
                .trim()
                .trim_start_matches('%');
            if pred_label.is_empty() {
                return Err(self.err_parse(lineno, "phi: empty predecessor label"));
            }
            let pred = f.intern_block(pred_label);
            incomings.push(PhiIncoming { value_tok, pred });
        }

        if incomings.is_empty() {
            return Err(self.err_parse(lineno, "phi without incoming values"));
        }

        // Collapse PARALLEL EDGES from the same predecessor.
        //
        // An LLVM `switch` that routes several case values to one target label
        // (e.g. `[ i32 0, label %t   i32 1, label %t ]`), and — more rarely — a
        // `br i1 %c, label %x, label %x`, create MULTIPLE edges from a single
        // predecessor block to the same successor. LLVM lists one phi entry per
        // *edge*, so such a phi carries DUPLICATE `[value, %pred]` entries:
        //
        //   %14 = phi ptr [ %9, %7 ], [ null, %3 ], [ null, %3 ]   ; two %3 edges
        //
        // The LLVM verifier guarantees that all entries sharing a predecessor
        // block hold an identical value (a phi can only distinguish by
        // predecessor block, never by individual edge). Our block-parameter
        // model carries exactly one argument-set per unique predecessor edge:
        // `append_phi_edge_arg` fans a single arg out to *every* switch case (or
        // condbr side) that targets this block. Applying each duplicate entry
        // would therefore push N args at a target with 1 param and trip the
        // adapter's branch-arg arity check ("branch-arg count (2) does not match
        // target params (1)"). Collapse the duplicates to ONE logical incoming.
        //
        // Fail closed if a repeated predecessor ever carries a DIFFERENT value:
        // that is an ill-formed module (impossible per the LLVM verifier), and a
        // silent pick-one would be a miscompile.
        let mut deduped: Vec<PhiIncoming> = Vec::with_capacity(incomings.len());
        for incoming in incomings {
            let prior_value = deduped
                .iter()
                .find(|prev| prev.pred == incoming.pred)
                .map(|prev| prev.value_tok.trim().to_string());
            match prior_value {
                Some(prior) if prior != incoming.value_tok.trim() => {
                    let pred_label = f
                        .block_label(incoming.pred)
                        .unwrap_or_else(|| format!("{:?}", incoming.pred));
                    return Err(self.err_parse(
                        lineno,
                        &format!(
                            "phi: predecessor `%{}` has conflicting incoming values on parallel \
                             edges (`{}` vs `{}`)",
                            pred_label,
                            prior,
                            incoming.value_tok.trim()
                        ),
                    ));
                }
                // Identical duplicate parallel edge — drop it.
                Some(_) => {}
                None => deduped.push(incoming),
            }
        }

        f.pending_phis.push(PendingPhi {
            target,
            ty,
            incomings: deduped,
            lineno,
        });
        Ok(())
    }

    fn apply_pending_phis(&self, f: &mut FuncScratch) -> Result<()> {
        for phi in f.pending_phis.clone() {
            for incoming in phi.incomings {
                let arg = self.lookup_phi_operand(
                    &incoming.value_tok,
                    &phi.ty,
                    incoming.pred,
                    phi.lineno,
                    f,
                )?;
                self.append_phi_edge_arg(incoming.pred, phi.target, arg, phi.lineno, f)?;
            }
        }
        Ok(())
    }

    fn append_phi_edge_arg(
        &self,
        pred: BlockId,
        target: BlockId,
        arg: ValueId,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<()> {
        let pred_label = f.block_label(pred).unwrap_or_else(|| format!("{:?}", pred));
        let block = f.blocks.get_mut(pred.as_usize()).ok_or_else(|| {
            self.err_parse(
                lineno,
                &format!("phi: unknown predecessor `{}`", pred_label),
            )
        })?;
        let term = block
            .body
            .last_mut()
            .filter(|n| n.is_terminator())
            .ok_or_else(|| {
                self.err_parse(
                    lineno,
                    &format!("phi: predecessor `{}` has no terminator", pred_label),
                )
            })?;

        let mut matched = false;
        match &mut term.inst {
            Inst::Br {
                target: br_target,
                args,
            } => {
                if *br_target == target {
                    args.push(arg);
                    matched = true;
                }
            }
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                if *then_target == target {
                    then_args.push(arg);
                    matched = true;
                }
                if *else_target == target {
                    else_args.push(arg);
                    matched = true;
                }
            }
            Inst::Switch {
                default,
                default_args,
                cases,
                ..
            } => {
                if *default == target {
                    default_args.push(arg);
                    matched = true;
                }
                for case in cases {
                    if case.target == target {
                        case.args.push(arg);
                        matched = true;
                    }
                }
            }
            _ => {}
        }

        if matched {
            Ok(())
        } else {
            let target_label = f
                .block_label(target)
                .unwrap_or_else(|| format!("{:?}", target));
            Err(self.err_parse(
                lineno,
                &format!(
                    "phi: predecessor `{}` does not branch to `{}`",
                    pred_label, target_label
                ),
            ))
        }
    }

    fn lookup_phi_operand(
        &self,
        tok: &str,
        ty: &Ty,
        pred: BlockId,
        lineno: usize,
        f: &mut FuncScratch,
    ) -> Result<ValueId> {
        let resolved = f.resolve_token_alias(tok);
        let tok = resolved.as_str();
        if let Some(rest) = tok.strip_prefix('%') {
            return Ok(f.intern_value(rest));
        }
        if let Some(global_name) = tok.strip_prefix('@') {
            // A `@g` phi operand is the global's address. Materialize its base
            // stub (offset 0 — the form codegen remaps) in the PREDECESSOR block
            // so the value dominates the phi edge, mirroring the constant path.
            if !matches!(ty, Ty::Ptr) {
                return Err(self.err_unsupported(&format!(
                    "global `@{}` phi operand referenced as non-pointer type {:?}",
                    global_name, ty
                )));
            }
            let addr = self.global_addr_stub(global_name, 0)?;
            let v = f.fresh_value();
            f.insert_before_terminator(
                pred,
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::Int(addr),
                })
                .with_result(v),
                lineno,
            )?;
            return Ok(v);
        }

        // `phi ptr [ getelementptr inbounds (i8, ptr @g, i64 K), %pred ], ...`
        //
        // The address of a global at a CONSTANT byte offset, as a phi incoming.
        // This is the canonical shape of a POINTER-INDUCTION-VARIABLE loop whose
        // walk starts inside a global array (`p = &g[k]`), so clang emits it for
        // exactly the loops we most want to import well. Without this arm the
        // token fell through to `parse_constant_operand`, which has no
        // const-expr evaluator, and the whole module failed to import.
        //
        // Same treatment as the `@g` arm directly above, which is this case with
        // K = 0: fold the offset into the address stub and materialize ONE
        // constant in the PREDECESSOR block, so the value dominates the phi
        // edge. `global_addr_stub` already takes the byte offset and range-checks
        // it, and `parse_constexpr_global_gep` is the same parser the operand
        // path uses -- both fail closed, so an offset or shape either of them
        // rejects still refuses the module rather than mis-importing it.
        if constant_expr_operand_kind(tok) == Some("getelementptr")
            && matches!(ty, Ty::Ptr)
            && let Ok((global_name, offset)) = self.parse_constexpr_global_gep(tok)
        {
            let addr = self.global_addr_stub(&global_name, offset)?;
            let v = f.fresh_value();
            f.insert_before_terminator(
                pred,
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::Int(addr),
                })
                .with_result(v),
                lineno,
            )?;
            return Ok(v);
        }

        let constant = self.parse_constant_operand(tok, ty)?;
        let v = f.fresh_value();
        f.insert_before_terminator(
            pred,
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: constant,
            })
            .with_result(v),
            lineno,
        )?;
        Ok(v)
    }

    /// Decode a whole-vector constant operand into `Constant::Vector`.
    ///
    /// Handles every spelling clang emits for a vector constant. Each lane is
    /// decoded by the SAME `parse_constant_operand` that decodes a scalar of
    /// the element type, so a lane literal can never be read differently here
    /// than it would be on the scalarizing path. Anything else fails closed.
    fn parse_vector_constant(&self, tok: &str, elem: &Ty, lanes: u32) -> Result<Constant> {
        let tok = tok.trim();
        let n = lanes as usize;
        if tok == "zeroinitializer" || tok == "undef" || tok == "poison" {
            let zero = self.parse_constant_operand("undef", elem)?;
            return Ok(Constant::Vector(vec![zero; n]));
        }
        if let Some(inner) = tok
            .strip_prefix("splat (")
            .and_then(|s| s.strip_suffix(')'))
        {
            let (ty_str, val) = split_ty_operand(inner)?;
            let lane_ty = parse_ty(&ty_str)?;
            if lane_ty != *elem {
                return Err(self.err_unsupported(&format!(
                    "vector splat element type `{ty_str}` does not match `{elem:?}`"
                )));
            }
            let lane = self.parse_constant_operand(&val, elem)?;
            return Ok(Constant::Vector(vec![lane; n]));
        }
        if let Some(inner) = tok.strip_prefix('<').and_then(|s| s.strip_suffix('>')) {
            let elems = split_aggregate_elems(inner);
            if elems.len() != n {
                return Err(self.err_unsupported(&format!(
                    "vector constant `{tok}` has {} elements, expected {n}",
                    elems.len()
                )));
            }
            let mut out = Vec::with_capacity(n);
            for e in elems {
                let (ty_str, val) = split_ty_operand(&e)?;
                let lane_ty = parse_ty(&ty_str)?;
                if lane_ty != *elem {
                    return Err(self.err_unsupported(&format!(
                        "vector constant element type `{ty_str}` does not match `{elem:?}`"
                    )));
                }
                out.push(self.parse_constant_operand(&val, elem)?);
            }
            return Ok(Constant::Vector(out));
        }
        Err(self.err_unsupported(&format!("vector constant operand `{tok}`")))
    }

    fn parse_constant_operand(&self, tok: &str, ty: &Ty) -> Result<Constant> {
        if let Ty::Vector(elem, lanes) = ty {
            return self.parse_vector_constant(tok, elem, *lanes);
        }
        if tok == "true" {
            Ok(Constant::Bool(true))
        } else if tok == "false" {
            Ok(Constant::Bool(false))
        } else if tok == "null" || tok == "undef" || tok == "poison" {
            let value = match ty {
                Ty::F16 | Ty::F32 | Ty::F64 => Constant::Float(0.0),
                _ => Constant::Int(0),
            };
            Ok(value)
        } else if matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
            let parsed = parse_fp_literal(tok).ok_or_else(|| Error::Parse {
                line: 0,
                message: format!("unknown float operand token `{}`", tok),
            })?;
            match parsed {
                FpLit::Double(d) | FpLit::Half(d) => Ok(Constant::Float(d)),
                FpLit::Extended(tag) => Err(self.err_unsupported(&format!(
                    "extended-precision float literal `0x{}...` (trust_ir only has f16/f32/f64)",
                    tag
                ))),
            }
        } else {
            let n = parse_int_literal(tok).ok_or_else(|| Error::Parse {
                line: 0,
                message: format!("unknown operand token `{}`", tok),
            })?;
            Ok(Constant::Int(n))
        }
    }

    // --- Operand resolution -----------------------------------------------

    fn lookup_operand(&self, tok: &str, ty: &Ty, f: &mut FuncScratch) -> Result<ValueId> {
        // Vector lane aliases first: `%r` may stand for `%a#v2` or for a bare
        // literal after an `extractelement` / `shufflevector` renaming.
        let resolved = f.resolve_token_alias(tok);
        let tok = resolved.as_str();
        // A whole-vector CONSTANT operand of a natively-lowered instruction:
        // `zeroinitializer`, an element list, `splat (T v)`, `undef`/`poison`.
        // Only reached with a `Ty::Vector` annotation, which only the native
        // path produces — the scalarizer splits constants lane by lane before
        // any operand resolution happens.
        if let Ty::Vector(elem, lanes) = ty
            && !tok.starts_with('%')
        {
            let constant = self.parse_vector_constant(tok, elem, *lanes)?;
            let v = f.fresh_value();
            f.push_inst(
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value: constant,
                })
                .with_result(v),
            );
            return Ok(v);
        }
        if let Some(kind) = constant_expr_operand_kind(tok) {
            // A `getelementptr (...)` const-expr addressing a global folds to the
            // global's base address plus a constant byte offset — the one const-
            // expr we evaluate (clang -O1 emits it constantly for `&global[k]`).
            if kind == "getelementptr" && matches!(ty, Ty::Ptr) {
                return self.emit_constexpr_global_gep(tok, f);
            }
            // Any other inline const-expr (inttoptr, bitcast, non-global GEP, …)
            // has no evaluator; fail closed rather than crash on the inner tokens.
            return Err(self.err_unsupported(&format!(
                "constant-expression operand `{kind} (...)` (no constant-folding evaluator)"
            )));
        }
        if let Some(rest) = tok.strip_prefix('%') {
            Ok(f.intern_value(rest))
        } else if let Some(global_name) = tok.strip_prefix('@') {
            if !matches!(ty, Ty::Ptr) {
                return Err(self.err_unsupported(&format!(
                    "global `@{}` referenced as non-pointer type {:?}",
                    global_name, ty
                )));
            }
            let canon = self.canon_symbol_name(global_name)?;
            if self.globals.contains_key(&canon) {
                // Address of a DATA global: the `0xFADE` stub the codegen adapter
                // remaps to the global's real relocation.
                let v = f.fresh_value();
                f.push_inst(
                    InstrNode::new(Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::Int(self.global_addr_stub(global_name, 0)?),
                    })
                    .with_result(v),
                );
                Ok(v)
            } else if self.func_ids.contains_key(&canon) {
                // Address of a FUNCTION (a function pointer, e.g.
                // `store ptr @toggle_value`): materialize the symbol's link-time
                // address as a relocatable `Constant::SymbolAddr`. The adapter
                // lowers it to a direct `GlobalRef` (ADRP+ADD) for a function
                // defined in this module, or a GOT-indirect `ExternRef` for a
                // declared external — resolution is by NAME, so any function
                // registered by a `define`/`declare` links correctly. Only a
                // KNOWN function reaches here, so no extern is fabricated for a
                // typo/undeclared symbol (that falls through to fail-closed).
                let v = f.fresh_value();
                // Address-taken function reference: disqualifies the symbol
                // from the libm-pure license (fail-closed).
                self.libm_plain_uses.borrow_mut().insert(canon.clone());
                f.push_inst(
                    InstrNode::new(Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::SymbolAddr {
                            symbol: canon,
                            addend: 0,
                        },
                    })
                    .with_result(v),
                );
                Ok(v)
            } else {
                // Neither a known data global nor a known function: fail closed
                // (preserve the historical diagnostic) rather than invent a symbol.
                Err(self.err_unsupported(&format!("address-of undeclared global `@{}`", canon)))
            }
        } else if tok == "true" {
            let v = f.fresh_value();
            f.push_inst(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(v),
            );
            Ok(v)
        } else if tok == "false" {
            let v = f.fresh_value();
            f.push_inst(
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                })
                .with_result(v),
            );
            Ok(v)
        } else if tok == "null" || tok == "undef" || tok == "poison" {
            // For FP types, `undef`/`poison` must materialize as a Float
            // constant or downstream lowering will see a type mismatch
            // when a `Constant::Int(0)` flows into an F32/F64 context.
            let v = f.fresh_value();
            let value = match ty {
                Ty::F16 | Ty::F32 | Ty::F64 => Constant::Float(0.0),
                _ => Constant::Int(0),
            };
            f.push_inst(
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value,
                })
                .with_result(v),
            );
            Ok(v)
        } else if matches!(ty, Ty::F16 | Ty::F32 | Ty::F64) {
            // Floating-point immediate. LLVM textual IR emits these in
            // three shapes:
            //   * Decimal:  `1.5`, `-3.14`, `1.500000e+00`
            //   * Hex f64:  `0x3FF8000000000000`  (bit pattern of 1.5)
            //   * Hex f16:  `0xH3C00` (bit pattern of half 1.0)
            //   * Hex f80 / f128 extended: `0xK...`, `0xL...`, `0xM...`
            //     — we reject these because trust_ir only models f16/f32/f64.
            let parsed = parse_fp_literal(tok).ok_or_else(|| Error::Parse {
                line: 0,
                message: format!("unknown float operand token `{}`", tok),
            })?;
            match parsed {
                FpLit::Double(d) | FpLit::Half(d) => {
                    let v = f.fresh_value();
                    f.push_inst(
                        InstrNode::new(Inst::Const {
                            ty: ty.clone(),
                            value: Constant::Float(d),
                        })
                        .with_result(v),
                    );
                    Ok(v)
                }
                FpLit::Extended(tag) => Err(self.err_unsupported(&format!(
                    "extended-precision float literal `0x{}...` (trust_ir only has f16/f32/f64)",
                    tag
                ))),
            }
        } else {
            // Integer literal (possibly negative, possibly hex).
            let n = parse_int_literal(tok).ok_or_else(|| Error::Parse {
                line: 0,
                message: format!("unknown operand token `{}`", tok),
            })?;
            let v = f.fresh_value();
            f.push_inst(
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Int(n),
                })
                .with_result(v),
            );
            Ok(v)
        }
    }
}

fn apply_function_attributes(func: &mut Function, sig: &FuncSignature) {
    let tag = match sig.stack_protector {
        ImportedStackProtectorAttr::None => return,
        ImportedStackProtectorAttr::Eligible => LLVM_STACK_PROTECTOR_FUNCTION_ATTR_TAG,
        ImportedStackProtectorAttr::Required => LLVM_STACK_PROTECTOR_REQUIRED_FUNCTION_ATTR_TAG,
    };
    func.proofs
        .push(ProofAnnotation::Custom(ProofTag::new(tag)));
}

fn merge_stack_protector_attr(
    lhs: ImportedStackProtectorAttr,
    rhs: ImportedStackProtectorAttr,
) -> ImportedStackProtectorAttr {
    lhs.max(rhs)
}

fn emit_alloca_count(
    parser: &Parser,
    clause: &str,
    lineno: usize,
    f: &mut FuncScratch,
    context: &str,
) -> Result<ValueId> {
    let (count_ty_str, count_tok) = split_ty_operand(clause)?;
    let count_ty = parse_ty(&count_ty_str)?;
    if !is_integer_ty(&count_ty) {
        return Err(parser.err_unsupported(&format!("{} count type `{}`", context, count_ty_str)));
    }
    if parse_int_literal(&count_tok).is_some_and(|n| n < 0) {
        return Err(parser.err_unsupported(&format!("{} with negative count", context)));
    }
    parser
        .lookup_operand(&count_tok, &count_ty, f)
        .map_err(|err| match err {
            Error::Parse { message, .. } => Error::Parse {
                line: lineno,
                message,
            },
            other => other,
        })
}

// --------------------------------------------------------------------------
// Small helpers / token utilities
// --------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct FuncSignature {
    name: String,
    ret: Option<Ty>,
    /// Parameters: (optional ssa name, type).
    params: Vec<(Option<String>, Ty)>,
    is_vararg: bool,
    internal: bool,
    stack_protector: ImportedStackProtectorAttr,
    /// The header carried the libm pure-math attribute license set
    /// (`speculatable willreturn nounwind memory(none)`). Only meaningful on
    /// `llvm.<fn>.fN` libm-intrinsic declarations; false elsewhere.
    libm_pure_math: bool,
}

fn strip_line(line: &str) -> String {
    // Drop everything starting with the `;` comment marker — but NOT a `;`
    // that occurs INSIDE a `"..."` string literal (a c-string constant such as
    // `c"; \00"` legitimately contains `;`, and a truncated string looks like an
    // "unterminated c-string" parse error). LLVM escapes an embedded quote as
    // `\22`, so the only raw `"` bytes on a line are string delimiters; a simple
    // in-quote toggle tracks them exactly (identifiers `@"..."` are balanced too).
    let bytes = line.as_bytes();
    let mut in_quote = false;
    let mut comment_at = None;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => in_quote = !in_quote,
            b';' if !in_quote => {
                comment_at = Some(i);
                break;
            }
            _ => {}
        }
        i += 1;
    }
    let no_comment = match comment_at {
        Some(i) => &line[..i],
        None => line,
    };
    // Drop metadata attachments like `, !dbg !12` or `, !tbaa !5` that appear at
    // the end of instruction lines — again only OUTSIDE a string literal.
    let trimmed = no_comment.trim_end();
    let mut s = trimmed.to_string();
    while let Some(idx) = rfind_outside_quotes(&s, ", !") {
        s.truncate(idx);
    }
    s
}

/// Rightmost byte index of `needle` in `s` that lies outside any `"..."` string
/// literal, or `None`. Used by `strip_line` so a `, !` (or `;`) inside a
/// c-string constant is never mistaken for a metadata attachment / comment.
fn rfind_outside_quotes(s: &str, needle: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let nb = needle.as_bytes();
    if nb.is_empty() {
        return None;
    }
    let mut in_quote = false;
    let mut last = None;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            in_quote = !in_quote;
            i += 1;
            continue;
        }
        if !in_quote && bytes[i..].starts_with(nb) {
            last = Some(i);
            i += nb.len();
            continue;
        }
        i += 1;
    }
    last
}

/// Extract the `@name` (with the leading `@` stripped) defined or declared by a
/// top-level line — a global definition `@name = ...`, or a function
/// `define ... @name(...)` / `declare ... @name(...)`. Returns the raw spelling
/// (still possibly `\01`-mangled / quoted); the caller canonicalizes. `None` for
/// any other line. Used only by the symbol-name pre-scan.
fn scan_defined_symbol_name(line: &str) -> Option<&str> {
    let after_at = if let Some(global) = line.strip_prefix('@') {
        // Global definition: `@name = ...`.
        let name = global.split('=').next()?.trim();
        (!name.is_empty()).then_some(name)?
    } else if line.starts_with("define") || line.starts_with("declare") {
        // Function: the callee `@name` precedes its `(` parameter list.
        let at = find_top_level_at(line)?;
        let paren = line[at..].find('(')?;
        line[at + 1..at + paren].trim()
    } else {
        return None;
    };
    // A quoted spelling `@"...."` keeps its quotes for `split_asm_label`; a bare
    // spelling ends at the first delimiter. Return the token verbatim.
    Some(after_at)
}

fn parse_attribute_group(line: &str) -> Option<(String, FunctionAttributeSet)> {
    let rest = line.strip_prefix("attributes")?.trim();
    let (group, attrs) = split_eq(rest)?;
    let group = group.trim();
    if !is_attribute_group_ref(group) {
        return None;
    }
    Some((
        group.to_string(),
        FunctionAttributeSet {
            stack_protector: attr_text_stack_protector_attr(attrs),
            allocsize: attr_text_has_token(attrs, "allocsize"),
            libm_pure_math: attr_text_is_libm_pure_math(attrs),
        },
    ))
}

fn function_stack_protector_attr(
    pre_at: &str,
    attrs_after: &str,
    attribute_groups: &HashMap<String, FunctionAttributeSet>,
) -> ImportedStackProtectorAttr {
    let mut attr = merge_stack_protector_attr(
        attr_text_stack_protector_attr(pre_at),
        attr_text_stack_protector_attr(attrs_after),
    );
    for group in attr_text_group_refs(pre_at).chain(attr_text_group_refs(attrs_after)) {
        if let Some(attrs) = attribute_groups.get(&group) {
            attr = merge_stack_protector_attr(attr, attrs.stack_protector);
        }
    }
    attr
}

fn attr_text_stack_protector_attr(text: &str) -> ImportedStackProtectorAttr {
    let mut attr = ImportedStackProtectorAttr::None;
    for token in attr_text_tokens(text) {
        match token.as_str() {
            "sspreq" => return ImportedStackProtectorAttr::Required,
            "ssp" | "sspstrong" => attr = ImportedStackProtectorAttr::Eligible,
            _ => {}
        }
    }
    attr
}

fn attr_text_has_token(text: &str, needle: &str) -> bool {
    attr_text_tokens(text)
        .iter()
        .any(|token| token.as_str() == needle)
}

/// True when this raw attribute text carries the exact pure-math license set
/// LLVM stamps on errno-free libm intrinsics (`llvm.sin.f64` and friends):
/// the `speculatable`, `willreturn` and `nounwind` tokens plus the literal
/// `memory(none)` memory effect. `memory(none)` is checked as raw text because
/// the tokenizer splits on parens and would conflate it with the NARROWER
/// `memory(argmem: readwrite)` forms — those must NOT license purity.
fn attr_text_is_libm_pure_math(text: &str) -> bool {
    attr_text_has_token(text, "speculatable")
        && attr_text_has_token(text, "willreturn")
        && attr_text_has_token(text, "nounwind")
        && text.contains("memory(none)")
}

/// Whether a `declare`/`define` header carries the libm pure-math license set,
/// either inline or via a referenced `attributes #N` group. Mirrors
/// `function_stack_protector_attr`'s inline+group merge.
fn function_libm_pure_math_attr(
    pre_at: &str,
    attrs_after: &str,
    attribute_groups: &HashMap<String, FunctionAttributeSet>,
) -> bool {
    attr_text_is_libm_pure_math(pre_at)
        || attr_text_is_libm_pure_math(attrs_after)
        || attr_text_group_refs(pre_at)
            .chain(attr_text_group_refs(attrs_after))
            .any(|group| {
                attribute_groups
                    .get(&group)
                    .is_some_and(|attrs| attrs.libm_pure_math)
            })
}

fn attr_text_or_group_has_allocsize(
    text: &str,
    attribute_groups: &HashMap<String, FunctionAttributeSet>,
) -> bool {
    attr_text_has_token(text, "allocsize")
        || attr_text_group_refs(text).any(|group| {
            attribute_groups
                .get(&group)
                .is_some_and(|attrs| attrs.allocsize)
        })
}

fn known_fresh_allocation_callee(name: &str) -> bool {
    matches!(name, "calloc" | "malloc" | "reallocarray" | "aligned_alloc")
}

fn imported_allocation_result_proofs(
    callee_name: &str,
    call_attrs: &str,
    attribute_groups: &HashMap<String, FunctionAttributeSet>,
) -> Vec<ProofAnnotation> {
    if !known_fresh_allocation_callee(callee_name)
        || !attr_text_or_group_has_allocsize(call_attrs, attribute_groups)
    {
        return Vec::new();
    }
    vec![ProofAnnotation::NoAlias, ProofAnnotation::Aligned(16)]
}

fn attr_text_group_refs(text: &str) -> impl Iterator<Item = String> {
    attr_text_tokens(text)
        .into_iter()
        .filter(|token| is_attribute_group_ref(token))
}

fn is_attribute_group_ref(token: &str) -> bool {
    token
        .strip_prefix('#')
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

fn attr_text_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut token = String::new();
    let mut in_quote = false;
    let mut escaped = false;

    for ch in text.chars() {
        if in_quote {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_quote = false;
            }
            continue;
        }

        if ch == '"' {
            push_attr_token(&mut tokens, &mut token);
            in_quote = true;
        } else if ch.is_whitespace() || matches!(ch, '{' | '}' | '=' | ',' | '(' | ')') {
            push_attr_token(&mut tokens, &mut token);
        } else {
            token.push(ch);
        }
    }
    push_attr_token(&mut tokens, &mut token);
    tokens
}

fn push_attr_token(tokens: &mut Vec<String>, token: &mut String) {
    if !token.is_empty() {
        tokens.push(std::mem::take(token));
    }
}

fn push_unique_proof(proofs: &mut Vec<ProofAnnotation>, proof: ProofAnnotation) {
    if !proofs.contains(&proof) {
        proofs.push(proof);
    }
}

fn add_inbounds_proof(mut node: InstrNode, is_inbounds: bool) -> InstrNode {
    if is_inbounds {
        push_unique_proof(&mut node.proofs, ProofAnnotation::InBounds);
    }
    node
}

fn collect_function_body(
    lines: &[(usize, String)],
    start: usize,
    _start_lineno: usize,
) -> Result<(usize, Vec<(usize, String)>)> {
    // The `define` line may or may not end with `{` — if not, the `{` is on
    // the next line.
    let mut body = Vec::new();
    let first = &lines[start].1;
    if !first.trim_end().ends_with('{') {
        // Skip until the `{`.
    }
    for (i, (ln, raw)) in lines.iter().enumerate().skip(start + 1) {
        let t = raw.trim();
        if t == "}" {
            return Ok((i, body));
        }
        body.push((*ln, raw.clone()));
    }
    Err(Error::Parse {
        line: lines[start].0,
        message: "unterminated function body (no closing `}`)".into(),
    })
}

fn parse_function_signature(
    line: &str,
    lineno: usize,
    is_define: bool,
    attribute_groups: &HashMap<String, FunctionAttributeSet>,
) -> Result<FuncSignature> {
    // Canonical shapes:
    //   define dso_local void @foo(i32 noundef %x) #0 {
    //   define internal i32 @bar(i8 %a, i8 %b) {
    //   declare i32 @printf(ptr noundef, ...) #1
    //
    // We chop leading keyword (`define` / `declare`), trailing attributes
    // (`#N`, `{`), then find the parenthesis boundaries to split ret-ty /
    // name / params.
    let head_kw = if is_define { "define" } else { "declare" };
    let mut s = line.trim_start_matches(head_kw).trim().to_string();
    if let Some(brace_idx) = s.rfind('{') {
        s.truncate(brace_idx);
    }
    let s = s.trim();

    // Locate the function name `@name`. We search for the first `@` at
    // nesting depth 0 so parenthesised return-value attributes — e.g.
    //   define range(i32 0, 65536) i32 @Rand() { ...
    //   define dereferenceable(8) ptr @g() { ...
    // — do not confuse the parameter-paren scan below. The function name
    // is always the first depth-0 `@`; return attributes never contain one.
    let at = find_top_level_at(s).ok_or(Error::Parse {
        line: lineno,
        message: "function header missing `@name`".into(),
    })?;
    let pre_at = s[..at].trim();
    let post_at = &s[at + 1..];
    // The name runs up to the first whitespace or `(`.
    let name_end = post_at
        .find(|c: char| c.is_whitespace() || c == '(')
        .unwrap_or(post_at.len());
    let name = post_at[..name_end].to_string();
    if name.is_empty() {
        return Err(Error::Parse {
            line: lineno,
            message: "function name is empty".into(),
        });
    }
    // Parameter list: the first `(` at or after the name, matched to its
    // closing `)`. Everything after is trailing attrs (`#0`, `nounwind`, …).
    let after_name = &post_at[name_end..];
    let paren_open_rel = after_name.find('(').ok_or(Error::Parse {
        line: lineno,
        message: "function header missing `(`".into(),
    })?;
    let paren_close_rel =
        find_matching_paren(&after_name[paren_open_rel..]).ok_or(Error::Parse {
            line: lineno,
            message: "function header missing `)`".into(),
        })?;
    let params_str = &after_name[paren_open_rel + 1..paren_open_rel + paren_close_rel];
    let attrs_after = after_name[paren_open_rel + paren_close_rel + 1..].trim();

    // Return type: last token before `@`, ignoring parameter/function
    // attributes like `dso_local` / `internal` / `noundef` etc. Clang emits
    // a predictable shape: the type is always the token immediately before
    // `@name`.
    // Tokenise pre_at; the last token with a leading type char is the type.
    // Bracket-aware, so `declare <4 x double> @llvm.fmuladd.v4f64(...)` sees
    // ONE return-type token instead of the three fragments `<4` / `x` /
    // `double>` — none of which `is_type_token` recognises, so the vector
    // return silently became `void`.
    let mut tokens: Vec<&str> = split_top_level_ws(pre_at);
    let mut ret_ty: Option<Ty> = None;
    while let Some(t) = tokens.pop() {
        if t == "void" {
            ret_ty = None;
            break;
        }
        if is_type_token(t) {
            ret_ty = Some(parse_ty(t)?);
            break;
        }
    }
    let internal = pre_at.contains("internal") || pre_at.contains("private");
    let stack_protector = function_stack_protector_attr(pre_at, attrs_after, attribute_groups);
    let libm_pure_math = function_libm_pure_math_attr(pre_at, attrs_after, attribute_groups);

    // Parameters.
    let mut params: Vec<(Option<String>, Ty)> = Vec::new();
    let mut is_vararg = false;
    if !params_str.trim().is_empty() {
        for p in split_call_args(params_str) {
            let p = p.trim();
            if p == "..." {
                is_vararg = true;
                continue;
            }
            // Each param is `<ty> [attrs...] [%name]`. Tokenize at bracket
            // depth 0 so a bracketed type — `<4 x double>`, `[8 x i32]`,
            // `{ i32, i32 }` — stays ONE token. Splitting on plain whitespace
            // cut `<4 x double>` into `<4` / `x` / `double>` and handed the
            // fragment `<4` to `parse_ty`, which reported the nonsense
            // diagnostic "aggregate / vector type `<4`".
            let toks: Vec<&str> = split_top_level_ws(p);
            if toks.is_empty() {
                continue;
            }
            let ty = parse_ty(toks[0])?;
            // Last token is the %name if it starts with %, else anonymous.
            let ssa = toks
                .iter()
                .rev()
                .find(|t| t.starts_with('%'))
                .map(|t| t.trim_start_matches('%').to_string());
            params.push((ssa, ty));
        }
    }

    Ok(FuncSignature {
        name,
        ret: ret_ty,
        params,
        is_vararg,
        internal,
        stack_protector,
        libm_pure_math,
    })
}

fn parse_block_label(line: &str) -> Option<String> {
    // `entry:` or `for.cond:  ; preds = %for.inc, %entry`.
    let first = line.split_whitespace().next()?;
    let colon = first.strip_suffix(':')?;
    if colon.is_empty() {
        return None;
    }
    // Reject things that also start with a keyword.
    if colon.contains('%') || colon.contains('@') {
        return None;
    }
    Some(colon.to_string())
}

fn body_starts_with_implicit_entry(body: &[(usize, String)]) -> bool {
    body.iter()
        .map(|(_, raw)| raw.trim())
        .find(|line| !line.is_empty() && *line != "{" && *line != "}")
        .is_some_and(|line| parse_block_label(line).is_none())
}

fn implicit_entry_block_label(sig: &FuncSignature) -> String {
    let mut next_unnamed = 0usize;
    for (name, _) in &sig.params {
        match name {
            Some(name) if is_decimal_name(name) => {
                if let Ok(value) = name.parse::<usize>() {
                    next_unnamed = next_unnamed.max(value + 1);
                }
            }
            None => next_unnamed += 1,
            _ => {}
        }
    }
    next_unnamed.to_string()
}

fn is_decimal_name(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

fn split_eq(s: &str) -> Option<(&str, &str)> {
    let i = s.find('=')?;
    Some((&s[..i], &s[i + 1..]))
}

/// Split `%r = ...` at the first `=` that is not part of `==` / `icmp eq`.
/// We look for an `=` that is followed by whitespace (standard LLVM syntax).
fn split_eq_not_icmp(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    for (i, b) in bytes.iter().enumerate() {
        if *b != b'=' {
            continue;
        }
        // Next char should be whitespace for this to be an assignment.
        let next = bytes.get(i + 1).copied().unwrap_or(b'\0');
        if next == b' ' || next == b'\t' {
            return Some((&s[..i], &s[i + 1..]));
        }
    }
    None
}

pub(crate) fn split_comma(s: &str) -> Option<(String, String)> {
    // Respect balanced brackets of every kind — `[` `(` `{` `<` — and `c"..."`
    // string literals, so a comma inside a struct initializer `{ i32 1, i32 2 }`
    // or a string does not split the operand.
    let bytes = s.as_bytes();
    let mut depth: i32 = 0;
    let mut in_string = false;
    for (i, b) in bytes.iter().enumerate() {
        if in_string {
            if *b == b'"' {
                in_string = false;
            }
            continue;
        }
        match *b {
            b'"' => in_string = true,
            b'[' | b'(' | b'{' | b'<' => depth += 1,
            b']' | b')' | b'}' | b'>' => depth -= 1,
            b',' if depth == 0 => {
                return Some((s[..i].trim().to_string(), s[i + 1..].trim().to_string()));
            }
            _ => {}
        }
    }
    None
}

/// Split `<ty> <operand>` where `<ty>` may contain `*`, `[`, etc.
/// Used for constructs like `ret i32 %x`, `icmp slt i32 %a, 0`.
fn split_ty_operand(s: &str) -> Result<(String, String)> {
    // Find the first top-level whitespace that separates ty from operand.
    let bytes = s.as_bytes();
    let mut depth: i32 = 0;
    for (i, b) in bytes.iter().enumerate() {
        match *b {
            b'[' | b'(' | b'<' => depth += 1,
            b']' | b')' | b'>' => depth -= 1,
            b if depth == 0 && (b == b' ' || b == b'\t') => {
                let left = s[..i].trim().to_string();
                let right = s[i + 1..].trim().to_string();
                if !left.is_empty() && !right.is_empty() {
                    return Ok((left, right));
                }
            }
            _ => {}
        }
    }
    Err(Error::Parse {
        line: 0,
        message: format!("expected `<ty> <operand>` in `{}`", s),
    })
}

fn split_two_labels(s: &str) -> Option<(String, String)> {
    // Expects "label %A, label %B"
    let (a, b) = split_comma(s)?;
    let a = a
        .trim_start_matches("label")
        .trim()
        .trim_start_matches('%')
        .to_string();
    let b = b
        .trim_start_matches("label")
        .trim()
        .trim_start_matches('%')
        .to_string();
    Some((a, b))
}

/// Strip the opcode word and any poison-refinement / fast-math flag tokens that
/// may follow it, leaving the operand text. Used by the native vector emitter,
/// which must see exactly the operand text the planner classified.
fn strip_native_vector_flags<'a>(rest: &'a str, opcode: &str) -> &'a str {
    let mut s = rest.trim_start_matches(opcode).trim_start();
    loop {
        let next = s.split_whitespace().next().unwrap_or("");
        let is_flag = matches!(
            next,
            "nsw"
                | "nuw"
                | "exact"
                | "disjoint"
                | "samesign"
                | "nneg"
                | "fast"
                | "nnan"
                | "ninf"
                | "nsz"
                | "arcp"
                | "contract"
                | "afn"
                | "reassoc"
        );
        if next.is_empty() || !is_flag {
            return s;
        }
        s = s[next.len()..].trim_start();
    }
}

/// Reduce a raw function body to the `(result_name, instruction_text)` pairs
/// [`crate::native_vector::plan_function`] expects.
///
/// This must apply the SAME normalization the emitter applies — the `=` split
/// and the tail-call marker strip — or the planner would key its decisions on
/// text the emitter never sees. Lines that are not instructions (labels,
/// braces, blank lines) map to an empty entry so nothing is misread as one.
fn native_vector_plan_input(body: &[(usize, String)]) -> Vec<(Option<String>, String)> {
    let mut out = Vec::with_capacity(body.len());
    for (_, raw) in body {
        let line = raw.trim();
        if line.is_empty() || line == "{" || line == "}" || parse_block_label(line).is_some() {
            out.push((None, String::new()));
            continue;
        }
        let (result, rest) = match split_eq_not_icmp(line) {
            Some((lhs, rhs)) => {
                let lhs = lhs.trim();
                if !lhs.starts_with('%') {
                    out.push((None, String::new()));
                    continue;
                }
                (Some(lhs.trim_start_matches('%').to_string()), rhs.trim())
            }
            None => (None, line),
        };
        let mut rest = rest;
        for prefix in ["tail ", "musttail ", "notail "] {
            if let Some(t) = rest.strip_prefix(prefix) {
                rest = t.trim_start();
                break;
            }
        }
        out.push((result, rest.to_string()));
    }
    out
}

fn strip_binop_flags<'a>(rest: &'a str, opcode: &str) -> &'a str {
    let mut s = rest.trim_start_matches(opcode).trim_start();
    loop {
        let next = s.split_whitespace().next().unwrap_or("");
        match next {
            "nsw" | "nuw" | "exact" | "disjoint" => {
                s = s[next.len()..].trim_start();
            }
            _ => return s,
        }
    }
}

/// Strip leading cast poison-refinement flags emitted by LLVM ≥ 18/19 between a
/// cast opcode and its source type: `nneg` (on `zext`), `nuw` / `nsw` (on
/// `trunc`). Dropping them is CONSERVATIVE: plain zext/trunc/sext semantics are a
/// sound over-approximation (defined on a superset of the flagged inputs, equal
/// wherever the flag's precondition holds), so a dropped flag can never introduce
/// a miscompile — it only forgoes optimization info the importer does not model.
fn strip_cast_flags(rest: &str) -> &str {
    let mut s = rest.trim_start();
    loop {
        let next = s.split_whitespace().next().unwrap_or("");
        match next {
            "nneg" | "nuw" | "nsw" => {
                s = s[next.len()..].trim_start();
            }
            _ => return s,
        }
    }
}

/// LLVM intrinsics that carry NO runtime effect — the call is a pure marker or
/// optimization hint. Dropping the call preserves observable behavior exactly
/// (a refinement, since these never read/write memory or return a used value):
///   * `llvm.lifetime.start/end` — stack-slot liveness for stack coloring.
///   * `llvm.dbg.*` — debug-info records.
///   * `llvm.assume` — a fact the optimizer may exploit; runtime no-op.
///   * `llvm.donothing` — literally nothing.
///   * `llvm.prefetch` — a cache hint.
///   * `llvm.invariant.start/end`, `llvm.experimental.noalias.scope.decl`,
///     `llvm.var.annotation`, `llvm.sideeffect` — analysis-only markers.
fn is_droppable_intrinsic(name: &str) -> bool {
    name.starts_with("llvm.lifetime.start")
        || name.starts_with("llvm.lifetime.end")
        || name.starts_with("llvm.dbg.")
        || name.starts_with("llvm.assume")
        || name.starts_with("llvm.donothing")
        || name.starts_with("llvm.prefetch")
        || name.starts_with("llvm.invariant.start")
        || name.starts_with("llvm.invariant.end")
        || name.starts_with("llvm.experimental.noalias.scope.decl")
        || name.starts_with("llvm.var.annotation")
        || name.starts_with("llvm.sideeffect")
}

/// LLVM intrinsics that `trust-cg-lower`'s adapter recognizes by callee name and
/// lowers to a specialized machine opcode (see `adapter.rs`: `is_memcpy_intrinsic`,
/// `is_memmove_intrinsic`, `is_memset_intrinsic`, `bitreverse_intrinsic_bitwidth`,
/// `objectsize_intrinsic_bitwidth`). The importer emits them as ordinary Calls to
/// the intrinsic symbol; the adapter rewrites them before any `_llvm.*` symbol
/// escapes. Names/widths MUST mirror the adapter's recognizers EXACTLY: an
/// intrinsic the adapter does not rewrite would survive as an unresolved symbol
/// and fail to link, so anything not listed here stays `unsupported`.
fn is_lowered_passthrough_intrinsic(name: &str) -> bool {
    name.starts_with("llvm.memcpy")
        || name.starts_with("llvm.memmove")
        || name.starts_with("llvm.memset")
        || name == "llvm.bitreverse.i32"
        || name == "llvm.bitreverse.i64"
        || name.starts_with("llvm.objectsize.")
        // Multiply-add intrinsics: the adapter preserves the rounding contract
        // as distinct `Opcode::Fmuladd` (fusion optional) and `Opcode::Fma`
        // (strict IEEE fused), both initially selected as AArch64 FMADD. MUST
        // mirror `adapter::fma_intrinsic_contract` exactly, else an un-rewritten
        // intrinsic would survive as an unresolved symbol and fail to link.
        || name == "llvm.fmuladd.f32"
        || name == "llvm.fmuladd.f64"
        || name == "llvm.fma.f32"
        || name == "llvm.fma.f64"
}

/// `@llvm.experimental.memset.pattern.*` — clang `-O1` emits this on Darwin for
/// pattern-fill loops. It has no native machine encoding; the importer lowers it
/// to a libSystem `memset_patternN` call (see `emit_memset_pattern`). Recognized
/// by family prefix; the element/count widths ride the mangled suffix but the
/// actual sizes are taken from the parsed argument types.
fn is_memset_pattern_intrinsic(name: &str) -> bool {
    name.starts_with("llvm.experimental.memset.pattern.")
}

/// Byte size of a `memset.pattern` element type. Only the scalar widths the
/// importer's `parse_ty` can produce are covered; anything else returns `None`
/// and the caller fails closed (a wrong size would corrupt the fill length).
fn memset_pattern_elem_bytes(ty: &Ty) -> Option<u64> {
    match ty {
        Ty::I8 => Some(1),
        Ty::I16 | Ty::F16 => Some(2),
        Ty::I32 | Ty::F32 => Some(4),
        Ty::I64 | Ty::F64 | Ty::Ptr => Some(8),
        Ty::I128 => Some(16),
        _ => None,
    }
}

/// LLVM intrinsics the importer rewrites to primitive trust_ir ops. These are
/// EXACT algebraic expansions (no library/ABI dependency), identical to LLVM's
/// own lowering: `{s,u}{max,min}` -> `select(icmp, a, b)`, `fabs` -> `FAbs`,
/// `sqrt/floor/ceil/trunc` -> native FP unary ops, `fshl/fshr` -> a branchless
/// shift/or funnel-shift expansion.
fn is_importer_lowered_intrinsic(name: &str) -> bool {
    minmax_intrinsic_predicate(name).is_some()
        || name.starts_with("llvm.fabs.")
        || name.starts_with("llvm.abs.")
        || fp_unary_intrinsic_op(name).is_some()
        || funnel_shift_is_left(name).is_some()
}

/// LLVM FP unary intrinsics that map 1:1 to a trust_ir native `UnOp` with a
/// mandatory AArch64 encoding (so no libm call is required, matching `clang
/// -O3`). `fabs` is handled separately (it is older and has its own call site),
/// so it is intentionally NOT listed here. The `.fN` width suffix is carried by
/// the operand type; only the family prefix is matched.
fn fp_unary_intrinsic_op(name: &str) -> Option<UnOp> {
    if name.starts_with("llvm.sqrt.") {
        Some(UnOp::FSqrt)
    } else if name.starts_with("llvm.floor.") {
        Some(UnOp::FFloor)
    } else if name.starts_with("llvm.ceil.") {
        Some(UnOp::FCeil)
    } else if name.starts_with("llvm.trunc.") {
        // `llvm.trunc` = round toward zero (RTZ) — the integral-valued
        // truncation, NOT the integer-narrowing `trunc` cast (which is an
        // opcode, never a `@llvm.*` call).
        Some(UnOp::FTrunc)
    } else {
        None
    }
}

/// Funnel-shift intrinsic recognizer. Returns `Some(true)` for `llvm.fshl.iN`
/// (shift left) and `Some(false)` for `llvm.fshr.iN` (shift right); `None`
/// otherwise. The `.iN` width suffix is carried by the operand type.
fn funnel_shift_is_left(name: &str) -> Option<bool> {
    if name.starts_with("llvm.fshl.") {
        Some(true)
    } else if name.starts_with("llvm.fshr.") {
        Some(false)
    } else {
        None
    }
}

/// Libm math intrinsics whose `-O1` lowering is a call to the C99 math library.
/// Maps `@llvm.<fn>.f64` -> `<fn>` and `@llvm.<fn>.f32` -> `<fn>f` (the
/// single-precision entry point), exactly as LLVM's own libcall lowering does.
/// The importer rewrites the callee to this symbol so an ordinary, linkable
/// external Call is emitted (no undefined `_llvm.*` symbol escapes). Both
/// trust-cg and the `clang -O3` reference resolve these out of the SAME
/// libSystem libm, so results are bit-exact.
///
/// Only transcendental / power functions that lack a native machine encoding go
/// here. Sign/rounding/sqrt intrinsics with an exact AArch64 instruction
/// (`fabs`, `sqrt`, `floor`, `ceil`, `trunc`) are lowered natively instead (see
/// `fp_unary_intrinsic_op`) and MUST NOT appear in this table.
fn libm_intrinsic_symbol(name: &str) -> Option<&'static str> {
    // (llvm family prefix, f64 symbol, f32 symbol)
    const TABLE: &[(&str, &str, &str)] = &[
        ("llvm.sin.", "sin", "sinf"),
        ("llvm.cos.", "cos", "cosf"),
        ("llvm.tan.", "tan", "tanf"),
        ("llvm.asin.", "asin", "asinf"),
        ("llvm.acos.", "acos", "acosf"),
        ("llvm.atan.", "atan", "atanf"),
        ("llvm.atan2.", "atan2", "atan2f"),
        ("llvm.sinh.", "sinh", "sinhf"),
        ("llvm.cosh.", "cosh", "coshf"),
        ("llvm.tanh.", "tanh", "tanhf"),
        ("llvm.exp.", "exp", "expf"),
        ("llvm.exp2.", "exp2", "exp2f"),
        ("llvm.log.", "log", "logf"),
        ("llvm.log2.", "log2", "log2f"),
        ("llvm.log10.", "log10", "log10f"),
        ("llvm.pow.", "pow", "powf"),
    ];
    for &(prefix, f64_sym, f32_sym) in TABLE {
        if let Some(suffix) = name.strip_prefix(prefix) {
            return match suffix {
                "f64" => Some(f64_sym),
                "f32" => Some(f32_sym),
                // Other widths (f16/f128/vector `vNf..`) have no matching libm
                // entry point here; fall through so the intrinsic classifier
                // fails closed rather than emitting a wrong-width call.
                _ => None,
            };
        }
    }
    None
}

/// Split a leading type token off `<type> <value>`, respecting nested
/// aggregate types: `[N x T]`, `{ ... }`, `<N x T>` return the whole bracketed
/// type; `%name` and scalars (`i32`, `double`, `ptr`) run to the next
/// whitespace. Returns `(type, value)` or `None` if either is empty.
pub(crate) fn split_leading_type(s: &str) -> Option<(&str, &str)> {
    let s = s.trim_start();
    let first = s.chars().next()?;
    let end = if matches!(first, '[' | '{' | '<') {
        let mut depth = 0i32;
        let mut found = None;
        for (i, c) in s.char_indices() {
            match c {
                '[' | '{' | '<' | '(' => depth += 1,
                ']' | '}' | '>' | ')' => {
                    depth -= 1;
                    if depth == 0 {
                        found = Some(i + c.len_utf8());
                        break;
                    }
                }
                _ => {}
            }
        }
        found?
    } else {
        s.find(char::is_whitespace)?
    };
    let ty = s[..end].trim();
    let value = s[end..].trim();
    if ty.is_empty() || value.is_empty() {
        return None;
    }
    Some((ty, value))
}

/// Split an aggregate-initializer body (the inside of `{...}` or `[...]`) into
/// its top-level comma-separated elements, respecting nested brackets of every
/// kind AND `c"..."` string literals (whose bytes may contain commas/brackets).
pub(crate) fn split_aggregate_elems(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut start = 0usize;
    let bytes = s.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        if in_string {
            // LLVM escapes a literal quote as `\22`, so a raw `"` always closes.
            if b == b'"' {
                in_string = false;
            }
            continue;
        }
        match b {
            b'"' => in_string = true,
            b'[' | b'{' | b'(' | b'<' => depth += 1,
            b']' | b'}' | b')' | b'>' => depth -= 1,
            b',' if depth == 0 => {
                out.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = s[start..].trim();
    if !last.is_empty() {
        out.push(last.to_string());
    }
    out
}

/// The signed/unsigned compare that selects the winner for an integer
/// `llvm.{s,u}{max,min}.iN` intrinsic: `max` keeps `a` when `a <cmp> b`.
fn minmax_intrinsic_predicate(name: &str) -> Option<ICmpOp> {
    if name.starts_with("llvm.smax.") {
        Some(ICmpOp::Sgt)
    } else if name.starts_with("llvm.smin.") {
        Some(ICmpOp::Slt)
    } else if name.starts_with("llvm.umax.") {
        Some(ICmpOp::Ugt)
    } else if name.starts_with("llvm.umin.") {
        Some(ICmpOp::Ult)
    } else {
        None
    }
}

/// Detect an LLVM *constant-expression* appearing in operand position — a keyword
/// followed by a parenthesised body, e.g. `inttoptr (i64 N to ptr)` or
/// `getelementptr inbounds ([N x T], ptr @g, i64 0, i64 1)`. trust_ir's importer
/// has no constant-folding evaluator, so recognising these lets us fail CLOSED
/// with a precise `unsupported:` reason (the importer doctrine) instead of
/// emitting a confusing `parse:` error on the mangled inner tokens (which the WS2
/// census would tally as a crash). Returns the matched keyword.
///
/// A bare const-expr keyword can only occur in operand position as part of such
/// an expression: ordinary SSA operands are `%v` / `@g` / a literal, and type
/// tokens are `i32`/`ptr`/…, so requiring both the keyword AND a `(` avoids any
/// false positive on a real operand.
fn constant_expr_operand_kind(s: &str) -> Option<&'static str> {
    const KEYWORDS: &[&str] = &[
        "getelementptr",
        "inttoptr",
        "ptrtoint",
        "bitcast",
        "addrspacecast",
        "trunc",
        "zext",
        "sext",
        "fptrunc",
        "fpext",
        "fptosi",
        "fptoui",
        "sitofp",
        "uitofp",
        "select",
    ];
    if !s.contains('(') {
        return None;
    }
    s.split_whitespace()
        .find_map(|w| KEYWORDS.iter().copied().find(|k| *k == w))
}

/// Strip leading opcode + any LLVM fast-math flag tokens that clang may
/// emit between the opcode and the type: `fast`, `nnan`, `ninf`, `nsz`,
/// `arcp`, `contract`, `reassoc`, `afn`. We silently drop them — Trust Codegen
/// does not yet model fast-math semantics and dropping matches the
/// existing `nsw`/`nuw` treatment on integer ops.
fn strip_fmath_flags<'a>(rest: &'a str, opcode: &str) -> &'a str {
    let mut s = rest.trim_start_matches(opcode).trim_start();
    loop {
        let next = s.split_whitespace().next().unwrap_or("");
        match next {
            "fast" | "nnan" | "ninf" | "nsz" | "arcp" | "contract" | "reassoc" | "afn" => {
                s = s[next.len()..].trim_start();
            }
            _ => return s,
        }
    }
}

/// Result of parsing a textual LLVM IR floating-point literal.
enum FpLit {
    /// A finite / infinite / NaN f64 value; sufficient for f32 after a
    /// narrowing cast because LLVM always round-trips f32 through a
    /// canonicalised 64-bit bit pattern in the textual IR.
    Double(f64),
    /// A binary16 literal decoded from LLVM's `0xH....` spelling.
    Half(f64),
    /// Extended-precision literal. LLVM uses a leading tag character
    /// after `0x`:
    ///
    /// * `0xK`  → x86 80-bit `long double`
    /// * `0xL`  → ppc_fp128 128-bit
    /// * `0xM`  → IEEE 128-bit
    /// * `0xR`  → bfloat16
    ///
    /// trust_ir has no F80 / F128 / BF16 so we surface these as a
    /// typed `Unsupported` rather than silently narrow.
    Extended(char),
}

/// Parse an LLVM IR textual float literal.
///
/// Accepted forms:
///   * Decimal with optional sign and exponent:
///     `1.5`, `-3.14`, `0.0`, `1.000000e+00`, `1e-9`, `-2.5E+10`
///   * Hex bit-pattern (f64):   `0x3FF8000000000000`  (16 hex digits)
///   * Named specials:          `inf`, `-inf`, `nan` (not emitted by
///     clang -O0 in practice but cheap to accept).
///   * Hex bit-pattern (f16):   `0xH3C00`  (half 1.0)
///   * Extended-precision tag:  `0xK...`, `0xL...`, `0xM...`, `0xR...`
///     — returned as `FpLit::Extended(tag)` so the caller can emit an
///     `Unsupported` error with a precise reason.
fn parse_fp_literal(s: &str) -> Option<FpLit> {
    let s = s.trim();
    // Named specials (rare in clang output but legal).
    if s.eq_ignore_ascii_case("inf") || s.eq_ignore_ascii_case("+inf") {
        return Some(FpLit::Double(f64::INFINITY));
    }
    if s.eq_ignore_ascii_case("-inf") {
        return Some(FpLit::Double(f64::NEG_INFINITY));
    }
    if s.eq_ignore_ascii_case("nan") {
        return Some(FpLit::Double(f64::NAN));
    }

    // Hex bit patterns. LLVM uses an optional type tag after `0x`:
    //   0x<16 hex>            → f64 bit pattern (IEEE double)
    //   0xK<hex>              → x86 80-bit
    //   0xL<hex>              → ppc_fp128
    //   0xM<hex>              → IEEE f128
    //   0xH<hex>              → half (f16)
    //   0xR<hex>              → bfloat16
    if let Some(rest) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        let first = rest.chars().next()?;
        if first.is_ascii_hexdigit() {
            // Plain 64-bit hex pattern.
            let bits = u64::from_str_radix(rest, 16).ok()?;
            return Some(FpLit::Double(f64::from_bits(bits)));
        } else if matches!(first, 'H' | 'h') {
            let bits = u16::from_str_radix(&rest[1..], 16).ok()?;
            return Some(FpLit::Half(f16_bits_to_f64(bits)));
        } else if matches!(first, 'K' | 'L' | 'M' | 'R' | 'k' | 'l' | 'm' | 'r') {
            return Some(FpLit::Extended(first.to_ascii_uppercase()));
        } else {
            return None;
        }
    }

    // Decimal.
    s.parse::<f64>().ok().map(FpLit::Double)
}

fn f16_bits_to_f64(bits: u16) -> f64 {
    let sign = if bits & 0x8000 == 0 { 1.0 } else { -1.0 };
    let exp = ((bits >> 10) & 0x1f) as i32;
    let frac = (bits & 0x03ff) as u32;
    match exp {
        0 if frac == 0 => sign * 0.0,
        0 => sign * f64::from(frac) * 2f64.powi(-24),
        0x1f if frac == 0 => sign * f64::INFINITY,
        0x1f => f64::NAN,
        _ => sign * (1.0 + f64::from(frac) / 1024.0) * 2f64.powi(exp - 15),
    }
}

fn parse_ty(s: &str) -> Result<Ty> {
    match s.trim() {
        "i1" => Ok(Ty::Bool),
        "i8" => Ok(Ty::I8),
        "i16" => Ok(Ty::I16),
        "i32" => Ok(Ty::I32),
        "i64" => Ok(Ty::I64),
        "i128" => Ok(Ty::I128),
        "ptr" => Ok(Ty::Ptr),
        "void" => Ok(Ty::Unit),
        // LLVM IR uses `float` / `double` as the textual spellings for
        // 32- and 64-bit IEEE-754 types. trust_ir has native `F32` and
        // `F64` so the mapping is direct.
        "half" | "f16" => Ok(Ty::F16),
        "float" | "f32" => Ok(Ty::F32),
        "double" | "f64" => Ok(Ty::F64),
        // `bfloat` and the extended-precision 80/128-bit types are legal
        // in LLVM IR but trust_ir only models f16 / f32 / f64 today. Reject
        // with a precise reason so the WS2 driver classifies the program
        // as `unsupported` (not a crash).
        "bfloat" => Err(Error::Unsupported(
            "bfloat16 (trust_ir has no bf16 type)".to_string(),
        )),
        "fp128" | "x86_fp80" | "ppc_fp128" => Err(Error::Unsupported(format!(
            "extended-precision float `{}` (trust_ir only has f16/f32/f64)",
            s.trim()
        ))),
        other if other.ends_with('*') => {
            // `i32*` or `i8*` legacy pointers — still occur occasionally.
            Ok(Ty::Ptr)
        }
        other if other.starts_with('[') || other.starts_with('<') => Err(Error::Unsupported(
            format!("aggregate / vector type `{}` (non-string context)", other),
        )),
        other => Err(Error::Unsupported(format!("type `{}`", other))),
    }
}

/// Kill switch for lane-scalarizing vector import (`TCG_NO_VECTOR_IMPORT=1`).
///
/// With it set, `parse_body_line` never consults [`crate::vector`], so every
/// vector construct falls back to the historical `parse_ty` rejection and the
/// importer produces byte-identical objects for every program that imported
/// before the expander existed.
fn vector_import_disabled() -> bool {
    std::env::var_os("TCG_NO_VECTOR_IMPORT").is_some_and(|v| v != "0")
}

fn align_up(value: u64, align: u64) -> u64 {
    if align <= 1 {
        value
    } else {
        value.div_ceil(align) * align
    }
}

fn scalar_layout(ty: &Ty) -> Option<(u64, u64)> {
    match ty {
        Ty::Bool | Ty::I8 => Some((1, 1)),
        Ty::I16 | Ty::F16 => Some((2, 2)),
        Ty::I32 | Ty::F32 => Some((4, 4)),
        Ty::I64 | Ty::F64 | Ty::Ptr => Some((8, 8)),
        Ty::I128 => Some((16, 16)),
        _ => None,
    }
}

fn explicit_integer_array_elem_bits(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::I8 => Some(8),
        Ty::I16 => Some(16),
        Ty::I32 => Some(32),
        Ty::I64 => Some(64),
        _ => None,
    }
}

fn format_ty_for_array_error(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "i8",
        Ty::I16 => "i16",
        Ty::I32 => "i32",
        Ty::I64 => "i64",
        _ => "unsupported",
    }
}

fn integer_literal_to_le_byte_constants(value: i128, bits: u32) -> Option<Vec<Constant>> {
    if !matches!(bits, 8 | 16 | 32 | 64) {
        return None;
    }
    let signed_min = -(1i128 << (bits - 1));
    let unsigned_max_exclusive = 1i128 << bits;
    if value < signed_min || value >= unsigned_max_exclusive {
        return None;
    }

    let mask = (1u128 << bits) - 1;
    let raw = (value as u128) & mask;
    let byte_count = (bits / 8) as usize;
    let mut out = Vec::with_capacity(byte_count);
    for byte_idx in 0..byte_count {
        let byte = ((raw >> (byte_idx * 8)) & 0xff) as i128;
        out.push(Constant::Int(byte));
    }
    Some(out)
}

fn scalar_integer_global_to_le_byte_constants(ty: &Ty, value: &Constant) -> Option<Vec<Constant>> {
    let value = match value {
        Constant::Int(v) => *v,
        // A Bool initializer (from `parse_scalar_global_initializer`) has the
        // same little-endian byte image as its 0/1 integer value.
        Constant::Bool(b) => *b as i128,
        _ => return None,
    };
    let bits = explicit_integer_array_elem_bits(ty)?;
    integer_literal_to_le_byte_constants(value, bits)
}

fn is_integer_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128
    )
}

fn is_scalar_global_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Ptr
    )
}

fn parse_linkage(lower: &str) -> Linkage {
    if lower.contains("private") {
        Linkage::Private
    } else if lower.contains("internal") {
        Linkage::Internal
    } else {
        Linkage::External
    }
}

fn split_global_storage(rest: &str) -> Option<(bool, &str)> {
    let trimmed = rest.trim_start();
    if let Some(tail) = trimmed.strip_prefix("global ") {
        return Some((true, tail));
    }
    if let Some(tail) = trimmed.strip_prefix("global[") {
        return Some((true, tail));
    }
    if let Some(tail) = trimmed.strip_prefix("constant ") {
        return Some((false, tail));
    }
    if let Some(tail) = trimmed.strip_prefix("constant[") {
        return Some((false, tail));
    }

    let lower = rest.to_lowercase();
    for (pat, mutable) in [
        (" global ", true),
        (" global[", true),
        (" constant ", false),
        (" constant[", false),
    ] {
        if let Some(idx) = lower.find(pat) {
            return Some((mutable, &rest[idx + pat.len()..]));
        }
    }
    None
}

fn parse_align_clause(s: &str) -> Option<u64> {
    s.trim().strip_prefix("align ")?.trim().parse::<u64>().ok()
}

fn is_type_token(s: &str) -> bool {
    matches!(
        s,
        "i1" | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "ptr"
            | "void"
            | "f16"
            | "f32"
            | "f64"
            | "half"
            | "float"
            | "double"
    ) || s.ends_with('*')
        // A `<...>` return type is a VECTOR (or a packed struct). Recognising
        // it routes the token into `parse_ty`, which fails closed. Without
        // this arm the token matched nothing and the return type silently
        // defaulted to `void`.
        || (s.starts_with('<') && s.ends_with('>'))
}

/// Split `s` on whitespace at BRACKET DEPTH ZERO, so a bracketed LLVM type
/// (`<4 x double>`, `[8 x i32]`, `{ i32, i32 }`, `range(i32 0, 65536)`) stays
/// a single token.
fn split_top_level_ws(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start: Option<usize> = None;
    for (i, c) in s.char_indices() {
        match c {
            '[' | '(' | '{' | '<' => depth += 1,
            ']' | ')' | '}' | '>' => depth -= 1,
            _ => {}
        }
        if depth == 0 && c.is_whitespace() {
            if let Some(st) = start.take() {
                out.push(s[st..i].trim());
            }
        } else if start.is_none() {
            start = Some(i);
        }
    }
    if let Some(st) = start {
        let tok = s[st..].trim();
        if !tok.is_empty() {
            out.push(tok);
        }
    }
    out.retain(|t| !t.is_empty());
    out
}

/// Find the byte offset of the first `@` at nesting depth 0, i.e. not
/// inside a `(...)` group. Used by `parse_call` so the explicit
/// function-type form `call i32 (ptr, ...) @printf(...)` is handled
/// correctly (we must not mistake the `,` inside `(ptr, ...)` for a
/// callee marker).
fn find_top_level_at(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' | '<' => depth += 1,
            ')' | ']' | '>' => depth -= 1,
            '@' if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// For an INDIRECT call `<ret-ty> %callee(<args>)`, return
/// `(callee_token_start, arg_paren_open)` — the byte offset where the `%callee`
/// token begins and the offset of the argument-list `(`. The argument-list `(`
/// is the first top-level `(` immediately preceded (modulo whitespace) by a
/// `%value` token; a leading explicit func-type group `(<params>, ...)` (whose
/// preceding token is a type, not a `%value`) is skipped. `None` if no such
/// `%callee(` shape is present.
fn find_indirect_callee(s: &str) -> Option<(usize, usize)> {
    let bytes = s.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'<' => {
                if bytes[i] == b'(' && depth == 0 {
                    // Trim whitespace immediately before the `(`, then walk back
                    // to the start of the preceding whitespace-delimited token.
                    let mut end = i;
                    while end > 0 && (bytes[end - 1] as char).is_whitespace() {
                        end -= 1;
                    }
                    let mut start = end;
                    while start > 0 && !(bytes[start - 1] as char).is_whitespace() {
                        start -= 1;
                    }
                    if end > start && bytes[start] == b'%' {
                        return Some((start, i));
                    }
                }
                depth += 1;
            }
            b')' | b']' | b'>' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    None
}

type ExplicitCallFuncType = (Vec<(Option<String>, Ty)>, bool);

fn parse_explicit_call_func_type(prefix: &str) -> Option<ExplicitCallFuncType> {
    let open = prefix.find('(')?;
    let close_rel = find_matching_paren(&prefix[open..])?;
    let params_str = &prefix[open + 1..open + close_rel];
    let mut params = Vec::new();
    let mut is_vararg = false;
    for raw in split_call_args(params_str) {
        let p = raw.trim();
        if p.is_empty() {
            continue;
        }
        if p == "..." {
            is_vararg = true;
            continue;
        }
        params.push((None, parse_ty(p).ok()?));
    }
    Some((params, is_vararg))
}

fn find_matching_paren(s: &str) -> Option<usize> {
    // s[0] must be '('. Find matching ')'.
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn split_call_args(s: &str) -> Vec<String> {
    // Split by top-level commas.
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    let bytes = s.as_bytes();
    for (i, b) in bytes.iter().enumerate() {
        match *b {
            b'[' | b'(' | b'<' => depth += 1,
            b']' | b')' | b'>' => depth -= 1,
            b',' if depth == 0 => {
                out.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < s.len() {
        let tail = s[start..].trim();
        if !tail.is_empty() {
            out.push(tail.to_string());
        }
    }
    out
}

fn find_ll_string_end(s: &str) -> Option<usize> {
    // LLVM strings terminate at an unescaped `"`. The only escape is
    // `\\xx` (hex) — `\\` and `\"` don't occur in clang-generated string
    // constants for our corpus. We just look for the first `"`.
    s.find('"')
}

fn decode_ll_string(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 2 < bytes.len() {
            let hi = (bytes[i + 1] as char).to_digit(16);
            let lo = (bytes[i + 2] as char).to_digit(16);
            if let (Some(h), Some(l)) = (hi, lo) {
                out.push(((h << 4) | l) as u8);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    out
}

pub(crate) fn parse_int_literal(s: &str) -> Option<i128> {
    let s = s.trim();
    if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        return i128::from_str_radix(hex, 16).ok();
    }
    s.parse::<i128>().ok()
}

// --------------------------------------------------------------------------
// Tests
// --------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::StackProtectorMode;

    fn lowered_stack_protector(src: &str, function_name: &str) -> StackProtectorMode {
        let module = import_text(src, "stack-protector").expect("parse");
        let lowered = trust_cg_lower::translate_module(&module).expect("lower");
        lowered
            .into_iter()
            .find_map(|(func, _)| (func.name == function_name).then_some(func.stack_protector))
            .unwrap_or_else(|| panic!("lowered function `{}` not found", function_name))
    }

    fn struct_gep_offsets(f: &Function) -> Vec<i128> {
        let mut offsets = Vec::new();
        for blk in &f.blocks {
            for pair in blk.body.windows(2) {
                let [const_node, gep_node] = pair else {
                    continue;
                };
                if let (
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(offset),
                    },
                    Inst::GEP {
                        pointee_ty: Ty::I8,
                        indices,
                        ..
                    },
                ) = (&const_node.inst, &gep_node.inst)
                    && indices.len() == 1
                    && const_node.results.len() == 1
                    && const_node.results[0] == indices[0]
                {
                    offsets.push(*offset);
                }
            }
        }
        offsets
    }

    fn gep_shapes(f: &Function) -> Vec<(Ty, usize)> {
        let mut shapes = Vec::new();
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::GEP {
                    pointee_ty,
                    indices,
                    ..
                } = &node.inst
                {
                    shapes.push((pointee_ty.clone(), indices.len()));
                }
            }
        }
        shapes
    }

    fn has_struct_alloca(f: &Function) -> bool {
        f.blocks.iter().any(|blk| {
            blk.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::Alloca {
                        ty: Ty::I8,
                        count: Some(_),
                        ..
                    }
                )
            })
        })
    }

    #[test]
    fn oversized_import_file_is_rejected_before_reading() {
        let suffix = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-llvm-import-oversized-{}-{}.ll",
            std::process::id(),
            suffix
        ));
        let file = std::fs::File::create(&path).unwrap();
        file.set_len(MAX_LLVM_IR_INPUT_BYTES + 1).unwrap();
        drop(file);

        let result = import_module(&path);
        let _ = std::fs::remove_file(&path);

        match result {
            Err(Error::Unsupported(message)) => {
                assert!(message.contains("over importer limit"), "{message}");
            }
            other => panic!("expected oversized Unsupported error, got {:?}", other),
        }
    }

    #[test]
    fn trivial_ret_0() {
        let src = r#"
define i32 @main() {
entry:
  ret i32 0
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
        assert_eq!(m.functions[0].name, "main");
        assert_eq!(m.functions[0].blocks.len(), 1);
        assert!(m.functions[0].blocks[0].terminator().is_some());
    }

    #[test]
    fn default_stack_protector_attribute_groups_without_alloca_lower_to_none() {
        for attr in ["ssp", "sspstrong"] {
            let src = format!(
                r#"
define i32 @leaf() #0 {{
entry:
  ret i32 0
}}

attributes #0 = {{ noinline nounwind {attr} uwtable "stack-protector-buffer-size"="8" }}
"#
            );

            assert_eq!(
                lowered_stack_protector(&src, "leaf"),
                StackProtectorMode::None,
                "attribute `{attr}` should not guard a leaf with no protected stack object"
            );
        }
    }

    #[test]
    fn required_stack_protector_attribute_lowers_to_stack_guard() {
        let src = r#"
define i32 @guarded() sspreq {
entry:
  ret i32 0
}
"#;

        assert_eq!(
            lowered_stack_protector(src, "guarded"),
            StackProtectorMode::StackGuard
        );
    }

    #[test]
    fn default_stack_protector_scalar_alloca_lowers_to_none() {
        let src = r#"
define i32 @scalar_tmp(i32 %x) ssp {
entry:
  %slot = alloca i32, align 4
  store i32 %x, ptr %slot, align 4
  %loaded = load i32, ptr %slot, align 4
  ret i32 %loaded
}
"#;

        assert_eq!(
            lowered_stack_protector(src, "scalar_tmp"),
            StackProtectorMode::None
        );
    }

    #[test]
    fn default_stack_protector_large_byte_buffer_lowers_to_stack_guard() {
        let src = r#"
define i32 @guarded_buffer() #0 {
entry:
  %buf = alloca i8, i64 16, align 1
  store i8 1, ptr %buf, align 1
  ret i32 0
}

attributes #0 = { noinline nounwind ssp uwtable "stack-protector-buffer-size"="8" }
"#;

        assert_eq!(
            lowered_stack_protector(src, "guarded_buffer"),
            StackProtectorMode::StackGuard
        );
    }

    #[test]
    fn default_stack_protector_scalar_alloca_escape_lowers_to_stack_guard() {
        let src = r#"
declare void @sink(ptr)

define void @escaped(i32 %x) sspstrong {
entry:
  %slot = alloca i32, align 4
  store i32 %x, ptr %slot, align 4
  call void @sink(ptr %slot)
  ret void
}
"#;

        assert_eq!(
            lowered_stack_protector(src, "escaped"),
            StackProtectorMode::StackGuard
        );
    }

    #[test]
    fn missing_stack_protector_attribute_lowers_to_none() {
        let src = r#"
define i32 @plain() #0 {
entry:
  ret i32 0
}

attributes #0 = { noinline nounwind uwtable "stack-protector-buffer-size"="8" }
"#;

        assert_eq!(
            lowered_stack_protector(src, "plain"),
            StackProtectorMode::None
        );
    }

    #[test]
    fn add_sub_mul() {
        let src = r#"
define i32 @f(i32 %a, i32 %b) {
entry:
  %s = add nsw i32 %a, %b
  %d = sub nsw i32 %s, 1
  %p = mul nsw i32 %d, 2
  ret i32 %p
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
        let f = &m.functions[0];
        // 3 binops + 2 const materializations (for literals 1 and 2) + ret
        assert!(!f.blocks.is_empty());
    }

    // --- O1 token-syntax + new-construct coverage --------------------------

    fn count_insts<P: Fn(&Inst) -> bool>(f: &Function, pred: P) -> usize {
        f.blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .filter(|n| pred(&n.inst))
            .count()
    }

    /// A `declare` registers a body-less `Function`, so `functions[0]` is not
    /// necessarily the defined function under test. Select it by name.
    fn func_named<'a>(m: &'a Module, name: &str) -> &'a Function {
        m.functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    #[test]
    fn tail_and_musttail_call_markers_are_stripped() {
        // At -O1 clang prefixes calls with `tail`/`musttail`. The marker is an
        // optimization hint; dispatch must still see the `call` opcode.
        let src = r#"
declare i32 @g(i32)
define i32 @f(i32 %a) {
entry:
  %r = tail call i32 @g(i32 %a)
  %s = musttail call i32 @g(i32 %r)
  ret i32 %s
}
"#;
        let m = import_text(src, "t").expect("tail/musttail call imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            2,
            "both tail-marked calls must lower to Call"
        );
    }

    #[test]
    fn range_return_attribute_in_header_parses() {
        // LLVM-21 emits a parenthesised `range(..)` return attribute before the
        // return type. The embedded parens must not confuse the header scan.
        let src = r#"
define range(i32 0, 65536) i32 @Rand() {
entry:
  ret i32 7
}
"#;
        let m = import_text(src, "t").expect("range() return attr header parses");
        // A correct parse recovers the name AFTER the parenthesised return
        // attribute (a naive first-`(` scan would mis-slice it).
        assert_eq!(m.functions[0].name, "Rand");
        let ft = &m.func_types[m.functions[0].ty.index() as usize];
        assert_eq!(
            ft.returns,
            vec![Ty::I32],
            "return type is i32, past the range attr"
        );
    }

    #[test]
    fn icmp_samesign_flag_is_dropped() {
        let src = r#"
define i1 @f(i32 %a, i32 %b) {
entry:
  %c = icmp samesign ult i32 %a, %b
  ret i1 %c
}
"#;
        let m = import_text(src, "t").expect("icmp samesign imports");
        let f = &m.functions[0];
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Ult,
                    ..
                }
            )),
            1,
            "samesign must be stripped, predicate preserved"
        );
    }

    #[test]
    fn freeze_lowers_to_copy() {
        let src = r#"
define i32 @f(i32 %x) {
entry:
  %y = freeze i32 %x
  ret i32 %y
}
"#;
        let m = import_text(src, "t").expect("freeze imports");
        let f = &m.functions[0];
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Copy { .. })),
            1,
            "freeze must lower to a Copy of its operand"
        );
    }

    #[test]
    fn lifetime_intrinsics_are_dropped() {
        // Stack lifetime markers carry no runtime effect; the importer drops them.
        let src = r#"
declare void @llvm.lifetime.start.p0(i64, ptr)
declare void @llvm.lifetime.end.p0(i64, ptr)
define i32 @f() {
entry:
  %p = alloca i32, align 4
  call void @llvm.lifetime.start.p0(i64 4, ptr %p)
  store i32 3, ptr %p, align 4
  call void @llvm.lifetime.end.p0(i64 4, ptr %p)
  ret i32 3
}
"#;
        let m = import_text(src, "t").expect("lifetime intrinsics import");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            0,
            "lifetime markers must not survive as Calls (would link-fail)"
        );
    }

    #[test]
    fn memset_intrinsic_passes_through_as_call() {
        // The adapter recognises `llvm.memset.*` by name and rewrites it; the
        // importer must emit it as an ordinary Call (not reject it).
        let src = r#"
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
define void @f(ptr %d, i64 %n) {
entry:
  call void @llvm.memset.p0.i64(ptr %d, i8 0, i64 %n, i1 false)
  ret void
}
"#;
        let m = import_text(src, "t").expect("memset intrinsic imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            1,
            "memset intrinsic must pass through as a Call for the adapter to lower"
        );
    }

    #[test]
    fn unrecognized_intrinsic_stays_unsupported() {
        // An intrinsic the backend cannot lower must fail closed (a plain Call
        // would leave an undefined `_llvm.*` symbol that never links).
        // `llvm.canonicalize` is not droppable, not a lowered pass-through, not
        // importer-lowered, and not a libm rewrite — the fail-closed default.
        let src = r#"
declare double @llvm.canonicalize.f64(double)
define double @f(double %x) {
entry:
  %r = call double @llvm.canonicalize.f64(double %x)
  ret double %r
}
"#;
        assert!(
            matches!(import_text(src, "t"), Err(Error::Unsupported(_))),
            "unrecognised llvm.* intrinsic must stay unsupported"
        );
    }

    /// Resolve a `Call`'s callee `FuncId` back to the module function name.
    fn call_callee_name<'a>(m: &'a Module, f: &Function) -> Option<&'a str> {
        f.blocks.iter().flat_map(|b| b.body.iter()).find_map(|n| {
            if let Inst::Call { callee, .. } = &n.inst {
                m.functions
                    .iter()
                    .find(|g| g.id == *callee)
                    .map(|g| g.name.as_str())
            } else {
                None
            }
        })
    }

    #[test]
    fn libm_f64_intrinsic_rewrites_to_libm_call() {
        // `@llvm.cos.f64` has no native encoding: LLVM's own lowering calls the
        // libm `cos` symbol. The importer rewrites the callee so an ordinary,
        // linkable Call is emitted (no `_llvm.cos.f64` escapes), and registers
        // the `cos` external in the module.
        let src = r#"
declare double @llvm.cos.f64(double)
define double @f(double %x) {
entry:
  %r = call double @llvm.cos.f64(double %x)
  ret double %r
}
"#;
        let m = import_text(src, "t").expect("cos.f64 imports as a libm call");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            1,
            "cos.f64 must survive as one ordinary Call"
        );
        assert_eq!(
            call_callee_name(&m, f),
            Some("cos"),
            "callee must be rewritten to the libm `cos` symbol"
        );
        let cos = func_named(&m, "cos");
        assert!(cos.blocks.is_empty(), "cos is a body-less external");
        assert!(matches!(cos.linkage, Linkage::External));
        // The `declare @llvm.cos.f64` line still registers a body-less stub in
        // the trust_ir module, but nothing references it, so codegen drops it
        // and the emitted object's only undefined symbol is `_cos` (verified in
        // the end-to-end differential — the object never carries `_llvm.cos.f64`).
    }

    #[test]
    fn libm_f32_intrinsic_rewrites_to_suffixed_call() {
        // The `.f32` width selects the `f`-suffixed single-precision entry point.
        let src = r#"
declare float @llvm.sin.f32(float)
define float @f(float %x) {
entry:
  %r = call float @llvm.sin.f32(float %x)
  ret float %r
}
"#;
        let m = import_text(src, "t").expect("sin.f32 imports as a libm call");
        let f = func_named(&m, "f");
        assert_eq!(
            call_callee_name(&m, f),
            Some("sinf"),
            "sin.f32 must call the single-precision `sinf`"
        );
    }

    #[test]
    fn libm_two_arg_pow_rewrites_to_pow_call() {
        let src = r#"
declare double @llvm.pow.f64(double, double)
define double @f(double %x, double %y) {
entry:
  %r = call double @llvm.pow.f64(double %x, double %y)
  ret double %r
}
"#;
        let m = import_text(src, "t").expect("pow.f64 imports");
        let f = func_named(&m, "f");
        assert_eq!(call_callee_name(&m, f), Some("pow"));
    }

    #[test]
    fn sqrt_intrinsic_lowers_to_native_fsqrt() {
        // `llvm.sqrt.fN` maps to the native `FSqrt` (AArch64 FSQRT), like
        // `clang -O3` — no libm call.
        let src = r#"
declare double @llvm.sqrt.f64(double)
define double @f(double %x) {
entry:
  %r = call double @llvm.sqrt.f64(double %x)
  ret double %r
}
"#;
        let m = import_text(src, "t").expect("sqrt imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::UnOp {
                    op: UnOp::FSqrt,
                    ..
                }
            )),
            1,
            "sqrt must lower to UnOp::FSqrt"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            0,
            "sqrt must NOT become a libm call"
        );
    }

    #[test]
    fn floor_ceil_trunc_intrinsics_lower_to_native_rounding() {
        for (fam, want) in [
            ("floor", UnOp::FFloor),
            ("ceil", UnOp::FCeil),
            ("trunc", UnOp::FTrunc),
        ] {
            let src = format!(
                r#"
declare double @llvm.{fam}.f64(double)
define double @f(double %x) {{
entry:
  %r = call double @llvm.{fam}.f64(double %x)
  ret double %r
}}
"#
            );
            let m = import_text(&src, "t").unwrap_or_else(|_| panic!("{fam} imports"));
            let f = func_named(&m, "f");
            assert_eq!(
                count_insts(f, |i| matches!(i, Inst::UnOp { op, .. } if *op == want)),
                1,
                "llvm.{fam}.f64 must lower to native {want:?}"
            );
            assert_eq!(count_insts(f, |i| matches!(i, Inst::Call { .. })), 0);
        }
    }

    #[test]
    fn fshl_intrinsic_expands_to_branchless_shifts() {
        // fshl(a,b,c) == (a << (c&M)) | ((b>>1) >> ((c&M)^M)), M = N-1.
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a, i32 %b, i32 %c) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %b, i32 %c)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        // No surviving intrinsic Call.
        assert_eq!(count_insts(f, |i| matches!(i, Inst::Call { .. })), 0);
        // Shift-amount masking (And), complement (Xor), both shift directions,
        // and the recombining Or must all be present.
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::And, .. })) >= 1);
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Xor, .. })) >= 1);
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Shl, .. })) >= 1);
        assert!(
            count_insts(f, |i| matches!(
                i,
                Inst::BinOp {
                    op: BinOp::LShr,
                    ..
                }
            )) >= 1
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Or, .. })),
            1,
            "funnel result recombines with exactly one Or"
        );
    }

    #[test]
    fn fshr_intrinsic_expands_to_branchless_shifts() {
        let src = r#"
declare i64 @llvm.fshr.i64(i64, i64, i64)
define i64 @f(i64 %a, i64 %b, i64 %c) {
entry:
  %r = call i64 @llvm.fshr.i64(i64 %a, i64 %b, i64 %c)
  ret i64 %r
}
"#;
        let m = import_text(src, "t").expect("fshr imports");
        let f = func_named(&m, "f");
        assert_eq!(count_insts(f, |i| matches!(i, Inst::Call { .. })), 0);
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Shl, .. })) >= 1);
        assert!(
            count_insts(f, |i| matches!(
                i,
                Inst::BinOp {
                    op: BinOp::LShr,
                    ..
                }
            )) >= 1
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Or, .. })),
            1
        );
    }

    // --- CONSTANT-ROTATE fast path -----------------------------------------

    /// The integer constant feeding SSA value `v`, if `v` is a `Const::Int`.
    fn const_int_of(f: &Function, v: ValueId) -> Option<i128> {
        f.blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .find(|n| n.results.first() == Some(&v))
            .and_then(|n| match &n.inst {
                Inst::Const {
                    value: Constant::Int(k),
                    ..
                } => Some(*k),
                _ => None,
            })
    }

    /// The constant right-hand shift distance of the (unique) `BinOp` with
    /// opcode `want`, resolving the amount operand through its `Const` def.
    fn shift_amount(f: &Function, want: BinOp) -> Option<i128> {
        f.blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .find_map(|n| match &n.inst {
                Inst::BinOp { op, rhs, .. } if *op == want => Some(*rhs),
                _ => None,
            })
            .and_then(|rhs| const_int_of(f, rhs))
    }

    #[test]
    fn fshl_const_rotate_uses_literal_shift_idiom() {
        // rotl(a, 7) on i32 == (a << 7) | (a >>u 25). A true rotate (a == a)
        // by a constant must emit the plain literal idiom with Iconst shift
        // amounts — NO And/Xor masking — so ISel folds the shifts to immediate
        // form and the machine rotate-idiom pass produces a single `ror`.
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a, i32 %c) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %a, i32 7)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        assert_eq!(count_insts(f, |i| matches!(i, Inst::Call { .. })), 0);
        // Literal idiom: exactly one Shl, one LShr, one Or; NO And, NO Xor.
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::And, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Xor, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Shl, .. })),
            1
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::BinOp {
                    op: BinOp::LShr,
                    ..
                }
            )),
            1
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Or, .. })),
            1
        );
        // Shift distances are the rotate constants k and N-k.
        assert_eq!(shift_amount(f, BinOp::Shl), Some(7));
        assert_eq!(shift_amount(f, BinOp::LShr), Some(25));
    }

    #[test]
    fn fshr_const_rotate_uses_literal_shift_idiom() {
        // rotr(a, 7) on i64 == (a >>u 7) | (a << 57).
        let src = r#"
declare i64 @llvm.fshr.i64(i64, i64, i64)
define i64 @f(i64 %a) {
entry:
  %r = call i64 @llvm.fshr.i64(i64 %a, i64 %a, i64 7)
  ret i64 %r
}
"#;
        let m = import_text(src, "t").expect("fshr imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::And, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Xor, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Shl, .. })),
            1
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::BinOp {
                    op: BinOp::LShr,
                    ..
                }
            )),
            1
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Or, .. })),
            1
        );
        assert_eq!(shift_amount(f, BinOp::LShr), Some(7));
        assert_eq!(shift_amount(f, BinOp::Shl), Some(57));
    }

    #[test]
    fn fshl_distinct_operands_uses_generic_fallback() {
        // a != b is a genuine two-input funnel; the generic And/Xor expansion
        // must still be used (the constant-rotate path must NOT fire).
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a, i32 %b) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %b, i32 7)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::And, .. })) >= 1);
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Xor, .. })) >= 1);
    }

    #[test]
    fn fshl_variable_amount_uses_generic_fallback() {
        // A variable (non-literal) amount cannot be folded; even a true rotate
        // (a == a) must fall through to the generic expansion.
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a, i32 %c) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %a, i32 %c)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::And, .. })) >= 1);
        assert!(count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Xor, .. })) >= 1);
    }

    #[test]
    fn fshl_const_rotate_zero_is_identity() {
        // rotl(a, 0) == a: no shift/or/mask ops; the result is `a` itself.
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %a, i32 0)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Shl, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::BinOp {
                    op: BinOp::LShr,
                    ..
                }
            )),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Or, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::And, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Xor, .. })),
            0
        );
        // The Return must carry `%a`'s value directly (the alias).
        let ret_val = f
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .find_map(|n| match &n.inst {
                Inst::Return { values } => values.first().copied(),
                _ => None,
            })
            .expect("has a return");
        assert!(
            const_int_of(f, ret_val).is_none(),
            "identity result must be the SSA parameter, not a fresh constant"
        );
    }

    #[test]
    fn fshl_const_rotate_masks_amount_modulo_width() {
        // i32 rotate by 39 == rotate by 39 & 31 == 7. Masking must match the
        // generic `c & (N-1)` semantics exactly.
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %a, i32 39)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        assert_eq!(shift_amount(f, BinOp::Shl), Some(7));
        assert_eq!(shift_amount(f, BinOp::LShr), Some(25));
    }

    #[test]
    fn fshl_const_rotate_amount_multiple_of_width_is_identity() {
        // i32 rotate by 32 == 32 & 31 == 0 == identity.
        let src = r#"
declare i32 @llvm.fshl.i32(i32, i32, i32)
define i32 @f(i32 %a) {
entry:
  %r = call i32 @llvm.fshl.i32(i32 %a, i32 %a, i32 32)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("fshl imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Shl, .. })),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::BinOp {
                    op: BinOp::LShr,
                    ..
                }
            )),
            0
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Or, .. })),
            0
        );
    }

    #[test]
    fn fshr_const_rotate_zero_is_identity() {
        let src = r#"
declare i64 @llvm.fshr.i64(i64, i64, i64)
define i64 @f(i64 %a) {
entry:
  %r = call i64 @llvm.fshr.i64(i64 %a, i64 %a, i64 0)
  ret i64 %r
}
"#;
        let m = import_text(src, "t").expect("fshr imports");
        let f = func_named(&m, "f");
        assert_eq!(count_insts(f, |i| matches!(i, Inst::BinOp { .. })), 0);
    }

    #[test]
    fn smax_intrinsic_lowers_to_icmp_select() {
        let src = r#"
declare i32 @llvm.smax.i32(i32, i32)
define i32 @f(i32 %a, i32 %b) {
entry:
  %m = call i32 @llvm.smax.i32(i32 %a, i32 %b)
  ret i32 %m
}
"#;
        let m = import_text(src, "t").expect("smax imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ..
                }
            )),
            1,
            "smax must compare with sgt"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Select { .. })),
            1,
            "smax must select the winner"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            0,
            "smax must not survive as a Call"
        );
    }

    #[test]
    fn abs_intrinsic_lowers_to_icmp_sub_select() {
        let src = r#"
declare i32 @llvm.abs.i32(i32, i1)
define i32 @f(i32 %a) {
entry:
  %m = call i32 @llvm.abs.i32(i32 %a, i1 false)
  ret i32 %m
}
"#;
        let m = import_text(src, "t").expect("abs imports");
        let f = func_named(&m, "f");
        // abs == select(icmp slt x, 0, sub 0 x, x)
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Slt,
                    ..
                }
            )),
            1,
            "abs must compare slt 0"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Sub, .. })),
            1,
            "abs must negate via sub 0"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Select { .. })),
            1,
            "abs must select the magnitude"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            0,
            "abs must not survive as a Call"
        );
    }

    #[test]
    fn fabs_intrinsic_lowers_to_unop_fabs() {
        let src = r#"
declare double @llvm.fabs.f64(double)
define double @f(double %x) {
entry:
  %r = call double @llvm.fabs.f64(double %x)
  ret double %r
}
"#;
        let m = import_text(src, "t").expect("fabs imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::UnOp { op: UnOp::FAbs, .. })),
            1,
            "fabs must lower to UnOp::FAbs"
        );
    }

    #[test]
    fn named_struct_zeroinitializer_global_is_byte_image() {
        // `%struct.foo = type { i32, i16 }` -> 8 bytes (4 + 2, padded to 4-align).
        let src = r#"
%struct.foo = type { i32, i16 }
@g = global %struct.foo zeroinitializer, align 4
"#;
        let m = import_text(src, "t").expect("named struct zero global imports");
        let g = m.globals.iter().find(|g| g.name == "g").expect("global g");
        match &g.initializer {
            Some(Constant::Aggregate(bytes)) => {
                assert_eq!(bytes.len(), 8, "{{i32,i16}} == 8 bytes (padded to align 4)");
                assert!(bytes.iter().all(|b| matches!(b, Constant::Int(0))));
            }
            other => panic!("expected zero byte aggregate, got {:?}", other),
        }
    }

    #[test]
    fn nested_aggregate_string_global_serializes_field_precise() {
        // An array-of-struct whose fields contain c"..." must be serialized
        // field-precise, NOT treated as a flat `[N x i8]` string (which would
        // decode the first embedded string as the entire image — a miscompile:
        // byte 0 would be 'l' = 0x6c instead of the i32 field value 1).
        // Each `{ i32, [6 x i8] }` is 4 + 6 = 10 bytes, padded to 12 (align 4).
        let src = r#"
@link = global [2 x { i32, [6 x i8] }] [{ i32, [6 x i8] } { i32 1, [6 x i8] c"link1\00" }, { i32, [6 x i8] } { i32 2, [6 x i8] c"link2\00" }], align 4
"#;
        let m = import_text(src, "t").expect("nested-aggregate string global imports");
        let bytes = global_bytes(&m, "link");
        assert_eq!(bytes.len(), 24, "2 x 12-byte padded structs");
        assert_eq!(bytes[0], 1, "field-precise: i32 1, NOT the string byte 'l'");
        assert_eq!(&bytes[4..10], b"link1\0");
        assert_eq!(bytes[12], 2, "second struct's i32 field");
    }

    #[test]
    fn plain_i8_string_global_still_imports() {
        // Guard against over-tightening: a genuine `[N x i8] c"..."` must still
        // decode to its byte image.
        let src = r#"
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
"#;
        let m = import_text(src, "t").expect("string global imports");
        match &m.globals[0].initializer {
            Some(Constant::Aggregate(bytes)) => assert_eq!(bytes.len(), 4),
            other => panic!("expected byte aggregate, got {:?}", other),
        }
    }

    #[test]
    fn volatile_load_and_store_preserve_the_flag() {
        // `volatile` is imported onto the trust_ir Load/Store (exact semantics),
        // not dropped and not rejected.
        let src = r#"
define i32 @f(ptr %p) {
entry:
  %v = load volatile i32, ptr %p, align 4
  store volatile i32 %v, ptr %p, align 4
  ret i32 %v
}
"#;
        let m = import_text(src, "t").expect("volatile load/store import");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Load { volatile: true, .. })),
            1,
            "volatile load must carry volatile: true"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Store { volatile: true, .. })),
            1,
            "volatile store must carry volatile: true"
        );
    }

    #[test]
    fn array_alloca_lowers_to_byte_slot() {
        // `alloca [4 x i32]` becomes a 16-byte i8 stack slot, like struct allocas.
        let src = r#"
define i32 @f() {
entry:
  %p = alloca [4 x i32], align 4
  ret i32 0
}
"#;
        let m = import_text(src, "t").expect("array alloca imports");
        let f = &m.functions[0];
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Alloca {
                    ty: Ty::I8,
                    count: Some(_),
                    ..
                }
            )),
            1,
            "array alloca must lower to a byte-sized i8 slot"
        );
    }

    #[test]
    fn load_store_alloca() {
        let src = r#"
define i32 @f(i32 %x) {
entry:
  %p = alloca i32, align 4
  store i32 %x, ptr %p, align 4
  %y = load i32, ptr %p, align 4
  ret i32 %y
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
    }

    #[test]
    fn icmp_and_condbr() {
        let src = r#"
define i32 @f(i32 %a) {
entry:
  %c = icmp slt i32 %a, 0
  br i1 %c, label %neg, label %pos
neg:
  ret i32 -1
pos:
  ret i32 1
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        assert_eq!(f.blocks.len(), 3);
    }

    #[test]
    fn imports_phi_as_block_param_and_branch_args() {
        let src = r#"
define i32 @f(i1 %c) {
entry:
  br i1 %c, label %t, label %f
t:
  br label %m
f:
  br label %m
m:
  %v = phi i32 [ 1, %t ], [ 2, %f ]
  ret i32 %v
}
"#;
        let m = import_text(src, "t").expect("parse phi");
        let f = &m.functions[0];
        let merge = &f.blocks[3];
        assert_eq!(merge.params.len(), 1, "merge block should get phi param");
        let phi_value = merge.params[0].0;
        assert_eq!(merge.params[0].1, Ty::I32);

        match &f.blocks[1].terminator().unwrap().inst {
            Inst::Br { args, .. } => assert_eq!(args.len(), 1, "true edge args"),
            other => panic!("expected true predecessor Br, got {:?}", other),
        }
        match &f.blocks[2].terminator().unwrap().inst {
            Inst::Br { args, .. } => assert_eq!(args.len(), 1, "false edge args"),
            other => panic!("expected false predecessor Br, got {:?}", other),
        }
        match &merge.terminator().unwrap().inst {
            Inst::Return { values } => assert_eq!(values.as_slice(), &[phi_value]),
            other => panic!("expected return from merge block, got {:?}", other),
        }
    }

    #[test]
    fn imports_phi_args_on_condbr_edge() {
        let src = r#"
define i32 @f(i1 %c) {
entry:
  br i1 %c, label %m, label %m
m:
  %v = phi i32 [ 7, %entry ]
  ret i32 %v
}
"#;
        let m = import_text(src, "t").expect("parse phi on condbr");
        let f = &m.functions[0];
        assert_eq!(f.blocks[1].params.len(), 1, "merge block phi param");
        match &f.blocks[0].terminator().unwrap().inst {
            Inst::CondBr {
                then_args,
                else_args,
                ..
            } => {
                assert_eq!(then_args.len(), 1, "then edge phi args");
                assert_eq!(else_args.len(), 1, "else edge phi args");
                assert_eq!(then_args, else_args, "same predecessor feeds both edges");
            }
            other => panic!("expected CondBr, got {:?}", other),
        }
    }

    #[test]
    fn switch_parallel_edges_to_one_target_dedup_phi_args() {
        // Minimal repro of the richards_benchmark import failure: a `switch`
        // routes MULTIPLE case values to the SAME target label, so LLVM emits
        // one phi entry per parallel edge — `[ 10, %entry ], [ 10, %entry ]`.
        // The switch block-param lowering must collapse those duplicate edges to
        // ONE branch-arg per case; otherwise the merge block (1 param) receives
        // 2 args per case and the adapter rejects it ("branch-arg count (2) does
        // not match target params (1)").
        let src = r#"
define i32 @f(i32 %s) {
entry:
  switch i32 %s, label %def [
    i32 0, label %merge
    i32 1, label %merge
  ]
merge:
  %v = phi i32 [ 10, %entry ], [ 10, %entry ]
  ret i32 %v
def:
  ret i32 99
}
"#;
        let m = import_text(src, "dup-edge").expect("parallel-edge switch phi imports");
        let f = func_named(&m, "f");

        // Exactly one merge phi param survives — a single logical incoming after
        // collapsing the parallel edges.
        let merge = f
            .blocks
            .iter()
            .find(|b| !b.params.is_empty())
            .expect("a block carries the phi param");
        assert_eq!(
            merge.params.len(),
            1,
            "merge block has exactly one phi param"
        );
        assert_eq!(merge.params[0].1, Ty::I32);

        // The switch keeps BOTH case values (per-case dispatch is preserved).
        let cases = f
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .find_map(|n| match &n.inst {
                Inst::Switch { cases, .. } => Some(cases.clone()),
                _ => None,
            })
            .expect("switch present");
        assert_eq!(cases.len(), 2, "both case values 0 and 1 keep their edges");

        // Both case values route to the SAME target (the parallel-edge shape).
        assert_eq!(
            cases[0].target, cases[1].target,
            "cases 0 and 1 dispatch to the same block"
        );

        // The crux: each parallel case edge carries EXACTLY ONE branch-arg after
        // dedup (before the fix each carried 2 — one per duplicate phi entry —
        // which trips the adapter's branch-arg arity check against merge's 1
        // param). Both edges pass the SAME value (identical phi entry).
        for case in &cases {
            assert_eq!(
                case.args.len(),
                1,
                "each parallel case edge carries exactly one branch-arg (deduped), got {}",
                case.args.len()
            );
        }
        assert_eq!(
            cases[0].args, cases[1].args,
            "parallel edges pass identical values"
        );
    }

    #[test]
    fn phi_conflicting_parallel_edge_values_fail_closed() {
        // Negative / fail-closed: a phi that gives DIFFERENT values for two
        // entries of the SAME predecessor is ill-formed (the LLVM verifier
        // forbids it — a phi can only distinguish by predecessor block, never by
        // individual parallel edge). The importer must REJECT it rather than
        // silently pick one, which would be a miscompile.
        let src = r#"
define i32 @f(i32 %s) {
entry:
  switch i32 %s, label %def [
    i32 0, label %merge
    i32 1, label %merge
  ]
merge:
  %v = phi i32 [ 10, %entry ], [ 20, %entry ]
  ret i32 %v
def:
  ret i32 99
}
"#;
        let err = import_text(src, "conflict").expect_err("conflicting phi edges must be rejected");
        match err {
            Error::Parse { message, .. } => assert!(
                message.contains("conflicting"),
                "expected a conflicting-incoming-values diagnostic, got: {message}"
            ),
            other => panic!("expected Error::Parse, got {other:?}"),
        }
    }

    #[test]
    fn imports_phi_from_implicit_numeric_entry_block() {
        let src = r#"
define i32 @f(i32 %0) {
  %2 = icmp sgt i32 %0, 0
  br i1 %2, label %3, label %5

3:
  %4 = icmp slt i32 %0, 10
  br label %5

5:
  %6 = phi i1 [ false, %1 ], [ %4, %3 ]
  %7 = zext i1 %6 to i32
  ret i32 %7
}
"#;
        let m = import_text(src, "implicit-entry").expect("parse implicit-entry phi");
        let f = &m.functions[0];
        assert_eq!(
            f.blocks.len(),
            3,
            "implicit entry must not create a synthetic block"
        );
        assert_eq!(f.blocks[2].params.len(), 1, "merge block phi param");
        match &f.blocks[0].terminator().unwrap().inst {
            Inst::CondBr {
                then_args,
                else_args,
                ..
            } => {
                assert!(then_args.is_empty(), "entry-to-then edge has no phi arg");
                assert_eq!(
                    else_args.len(),
                    1,
                    "entry-to-merge edge gets the constant phi arg"
                );
            }
            other => panic!("expected entry CondBr, got {:?}", other),
        }
    }

    #[test]
    fn imports_loop_phi_with_forward_backedge_pred() {
        let src = r#"
define i32 @f(i32 %n) {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %body ]
  %done = icmp sge i32 %i, %n
  br i1 %done, label %exit, label %body
body:
  %next = add i32 %i, 1
  br label %loop
exit:
  ret i32 %i
}
"#;
        let m = import_text(src, "t").expect("parse loop phi");
        let f = &m.functions[0];
        let loop_block = &f.blocks[1];
        assert_eq!(loop_block.params.len(), 1, "loop header phi param");

        match &f.blocks[0].terminator().unwrap().inst {
            Inst::Br { args, .. } => assert_eq!(args.len(), 1, "entry edge arg"),
            other => panic!("expected entry Br, got {:?}", other),
        }
        let loop_id = loop_block.id;
        let backedge_args = f
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator()?.inst {
                Inst::Br { target, args } if *target == loop_id && block.id != f.entry => {
                    Some(args.len())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(backedge_args, vec![1], "backedge arg");
    }

    /// f32 `fadd` with a decimal FP immediate on the right-hand side.
    #[test]
    fn fadd_f32_const_rhs() {
        let src = r#"
define float @f(float %a) {
entry:
  %b = fadd float %a, 1.5
  ret float %b
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        // Body must contain a BinOp { op: FAdd, ty: F32, .. }.
        let mut saw_fadd = false;
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F32,
                    ..
                } = &node.inst
                {
                    saw_fadd = true;
                }
            }
        }
        assert!(saw_fadd, "expected Inst::BinOp {{ FAdd, F32 }}");
    }

    /// f64 arithmetic covering fadd / fsub / fmul / fdiv in a single
    /// function. Confirms the dispatcher, flag-stripping, and decimal
    /// FP literal parsing all hold together.
    #[test]
    fn fbinop_f64_all_four() {
        let src = r#"
define double @f(double %a, double %b) {
entry:
  %s = fadd fast double %a, %b
  %d = fsub double %s, 1.0
  %p = fmul nnan nsz double %d, 2.0
  %q = fdiv double %p, 4.0
  ret double %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        let mut seen = std::collections::HashSet::new();
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::BinOp {
                    op, ty: Ty::F64, ..
                } = &node.inst
                {
                    seen.insert(*op);
                }
            }
        }
        for want in [BinOp::FAdd, BinOp::FSub, BinOp::FMul, BinOp::FDiv] {
            assert!(seen.contains(&want), "missing {:?} in {:?}", want, seen);
        }
    }

    /// `fneg` must map to `UnOp::FNeg` (not to a subtract-from-zero idiom).
    #[test]
    fn fneg_maps_to_unop() {
        let src = r#"
define double @f(double %a) {
entry:
  %b = fneg double %a
  ret double %b
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        let mut saw = false;
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::UnOp {
                    op: UnOp::FNeg,
                    ty: Ty::F64,
                    ..
                } = &node.inst
                {
                    saw = true;
                }
            }
        }
        assert!(saw, "expected Inst::UnOp {{ FNeg, F64 }}");
    }

    /// fcmp olt must map to FCmpOp::OLt on F64, and the result must be
    /// usable as a CondBr selector (i.e. typed Bool).
    #[test]
    fn fcmp_olt_drives_condbr() {
        let src = r#"
define i32 @f(double %x, double %y) {
entry:
  %c = fcmp olt double %x, %y
  br i1 %c, label %lt, label %ge
lt:
  ret i32 1
ge:
  ret i32 2
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        assert_eq!(f.blocks.len(), 3, "expected entry / lt / ge");
        let mut saw_fcmp = false;
        let mut saw_condbr = false;
        for blk in &f.blocks {
            for node in &blk.body {
                match &node.inst {
                    Inst::FCmp {
                        op: FCmpOp::OLt,
                        ty: Ty::F64,
                        ..
                    } => saw_fcmp = true,
                    Inst::CondBr { .. } => saw_condbr = true,
                    _ => {}
                }
            }
        }
        assert!(saw_fcmp, "expected FCmp OLt F64");
        assert!(saw_condbr, "expected CondBr terminator");
    }

    /// All 12 ordered / unordered FCmp predicates round-trip through
    /// `parse_fcmp`. `ord` / `uno` / `true` / `false` are covered by
    /// their own tests since they lower differently.
    #[test]
    fn fcmp_all_twelve_predicates() {
        for (ll, want) in [
            ("oeq", FCmpOp::OEq),
            ("one", FCmpOp::ONe),
            ("olt", FCmpOp::OLt),
            ("ole", FCmpOp::OLe),
            ("ogt", FCmpOp::OGt),
            ("oge", FCmpOp::OGe),
            ("ueq", FCmpOp::UEq),
            ("une", FCmpOp::UNe),
            ("ult", FCmpOp::ULt),
            ("ule", FCmpOp::ULe),
            ("ugt", FCmpOp::UGt),
            ("uge", FCmpOp::UGe),
        ] {
            let src = format!(
                "define i1 @f(double %a, double %b) {{\nentry:\n  %c = fcmp {} double %a, %b\n  ret i1 %c\n}}\n",
                ll
            );
            let m = import_text(&src, "t").expect("parse");
            let f = &m.functions[0];
            let mut got = None;
            for blk in &f.blocks {
                for node in &blk.body {
                    if let Inst::FCmp { op, .. } = &node.inst {
                        got = Some(*op);
                    }
                }
            }
            assert_eq!(got, Some(want), "fcmp {} mapped wrong", ll);
        }
    }

    /// `fcmp ord`/`uno` are synthesized as two self-comparisons combined
    /// with AND/OR because trust_ir's FCmpOp enum does not include
    /// Ord/Uno. Verify we emit the expected shape.
    #[test]
    fn fcmp_ord_uno_are_synthesized() {
        let src = r#"
define i1 @f(double %a, double %b) {
entry:
  %c = fcmp ord double %a, %b
  ret i1 %c
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        let mut fcmps = 0usize;
        let mut ands = 0usize;
        for blk in &f.blocks {
            for node in &blk.body {
                match &node.inst {
                    Inst::FCmp {
                        op: FCmpOp::OEq, ..
                    } => fcmps += 1,
                    Inst::BinOp {
                        op: BinOp::And,
                        ty: Ty::Bool,
                        ..
                    } => ands += 1,
                    _ => {}
                }
            }
        }
        assert_eq!(fcmps, 2, "expected 2 self-comparisons for `ord`");
        assert_eq!(ands, 1, "expected 1 i1-And for `ord`");

        let src2 = r#"
define i1 @g(double %a, double %b) {
entry:
  %c = fcmp uno double %a, %b
  ret i1 %c
}
"#;
        let m = import_text(src2, "g").expect("parse");
        let f = &m.functions[0];
        let mut fcmps = 0usize;
        let mut ors = 0usize;
        for blk in &f.blocks {
            for node in &blk.body {
                match &node.inst {
                    Inst::FCmp {
                        op: FCmpOp::UNe, ..
                    } => fcmps += 1,
                    Inst::BinOp {
                        op: BinOp::Or,
                        ty: Ty::Bool,
                        ..
                    } => ors += 1,
                    _ => {}
                }
            }
        }
        assert_eq!(fcmps, 2, "expected 2 self-comparisons for `uno`");
        assert_eq!(ors, 1, "expected 1 i1-Or for `uno`");
    }

    /// `fcmp true`/`false` fold to constant i1 without consuming the
    /// operands at runtime.
    #[test]
    fn fcmp_true_false_fold_to_const() {
        for (ll, want) in [("true", true), ("false", false)] {
            let src = format!(
                "define i1 @f(double %a, double %b) {{\nentry:\n  %c = fcmp {} double %a, %b\n  ret i1 %c\n}}\n",
                ll
            );
            let m = import_text(&src, "t").expect("parse");
            let f = &m.functions[0];
            let mut saw = false;
            for blk in &f.blocks {
                for node in &blk.body {
                    if let Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(b),
                    } = &node.inst
                        && *b == want
                    {
                        saw = true;
                    }
                }
            }
            assert!(saw, "fcmp {} did not fold to Bool({})", ll, want);
        }
    }

    /// Hex-encoded f64 literals (`0x3FF8000000000000` == 1.5) round-trip
    /// through parse_fp_literal.
    #[test]
    fn fp_hex_literal_roundtrips() {
        let src = r#"
define double @f(double %a) {
entry:
  %b = fadd double %a, 0x3FF8000000000000
  ret double %b
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        let mut saw_const = false;
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::Const {
                    ty: Ty::F64,
                    value: Constant::Float(v),
                } = &node.inst
                    && (*v - 1.5).abs() < 1e-12
                {
                    saw_const = true;
                }
            }
        }
        assert!(saw_const, "expected Float(1.5) materialization");
    }

    /// Extended-precision literal tags (`0xK...`) surface as a typed
    /// `Unsupported` rather than a crash.
    #[test]
    fn fp_extended_hex_literal_unsupported() {
        let src = r#"
define double @f(double %a) {
entry:
  %b = fadd double %a, 0xK3FFF8000000000000000
  ret double %b
}
"#;
        let r = import_text(src, "t");
        assert!(
            matches!(r, Err(Error::Unsupported(_))),
            "extended fp literal should be unsupported, got {:?}",
            r
        );
    }

    /// LLVM ≥ 18/19 cast poison-refinement flags (`zext nneg`, `trunc nuw`,
    /// `trunc nsw`) are dropped (conservative) and the cast still parses/lowers.
    #[test]
    fn cast_refinement_flags_are_dropped() {
        let src = r#"
define i64 @f(i32 %x, i64 %p) {
entry:
  %a = zext nneg i32 %x to i64
  %b = trunc nuw i64 %p to i32
  %c = trunc nsw i64 %p to i16
  %d = zext i32 %b to i64
  %e = add i64 %a, %d
  ret i64 %e
}
"#;
        let m = import_text(src, "t").expect("cast flags must parse");
        // The zext/trunc must have lowered to Cast instructions (flags dropped,
        // plain semantics retained).
        let casts = m.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::Cast { .. }))
            .count();
        assert!(casts >= 4, "expected >=4 casts, got {casts}");
    }

    /// LLVM ≥ 19 GEP pointer-arithmetic flags (`inbounds nuw` / `nusw`) are
    /// dropped and the GEP still parses.
    #[test]
    fn gep_nuw_flag_is_dropped() {
        let src = r#"
define ptr @g(ptr %p, i64 %i) {
entry:
  %q = getelementptr inbounds nuw i32, ptr %p, i64 %i
  ret ptr %q
}
"#;
        assert!(
            import_text(src, "t").is_ok(),
            "getelementptr inbounds nuw must parse"
        );
    }

    /// An inline `getelementptr` constant-expression used as a load pointer is
    /// unsupported (no constant-folding evaluator) — a clean fail-closed, not a
    /// parse crash on the mangled inner tokens.
    #[test]
    fn constant_expr_global_gep_operand_folds_to_stub_address() {
        // `getelementptr ([3 x i32], ptr @arr, i64 0, i64 1)` == &arr + 4 bytes.
        // @arr is global index 0, so the stub is 0xFADE_0000_0000_0004.
        let src = r#"
@arr = global [3 x i32] zeroinitializer
define i32 @f() {
entry:
  %v = load i32, ptr getelementptr inbounds ([3 x i32], ptr @arr, i64 0, i64 1), align 4
  ret i32 %v
}
"#;
        let m = import_text(src, "t").expect("constexpr global GEP folds");
        let f = func_named(&m, "f");
        // @arr base stub (offset 0) so codegen can remap it to a real reloc...
        let base_stub = (0xFADEu64 << 48) as i128;
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::Ptr,
                    value: Constant::Int(v),
                } if *v == base_stub
            )),
            1,
            "constexpr GEP must materialise @arr's base stub at offset 0"
        );
        // ...then a byte GEP applies the +4 at runtime on the real address.
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::GEP {
                    pointee_ty: Ty::I8,
                    ..
                }
            )),
            1,
            "constexpr GEP must add the byte offset via a runtime i8 GEP"
        );
    }

    fn global_bytes(m: &Module, name: &str) -> Vec<u8> {
        match &m
            .globals
            .iter()
            .find(|g| g.name == name)
            .expect("global")
            .initializer
        {
            Some(Constant::Aggregate(cs)) => cs
                .iter()
                .map(|c| match c {
                    Constant::Int(v) => *v as u8,
                    other => panic!("non-byte constant {:?}", other),
                })
                .collect(),
            other => panic!("expected byte aggregate, got {:?}", other),
        }
    }

    #[test]
    fn explicit_struct_global_serializes_to_exact_le_bytes() {
        // `{ i32 1, i32 2 }` -> 8 little-endian bytes.
        let src = r#"
%struct.S1 = type { i32, i32 }
@gs1 = global %struct.S1 { i32 1, i32 2 }, align 4
"#;
        let m = import_text(src, "t").expect("explicit struct global imports");
        assert_eq!(global_bytes(&m, "gs1"), vec![1, 0, 0, 0, 2, 0, 0, 0]);
    }

    #[test]
    fn explicit_struct_global_pads_between_fields() {
        // `{ i8 123, i32 4 }` -> i8 at 0, 3 pad bytes, i32 at offset 4. size 8.
        let src = r#"
%struct.P = type { i8, i32 }
@p = global %struct.P { i8 123, i32 4 }, align 4
"#;
        let m = import_text(src, "t").expect("padded struct global imports");
        assert_eq!(global_bytes(&m, "p"), vec![123, 0, 0, 0, 4, 0, 0, 0]);
    }

    #[test]
    fn explicit_array_of_struct_global_with_string_and_zeroinit_field() {
        // `[1 x { i32, [4 x i8], i32 }]` with a c-string and a zeroinit field —
        // exercises nested arrays, strings, and tail padding in one image.
        let src = r#"
@v = global [1 x { i32, [4 x i8], i32 }] [{ i32, [4 x i8], i32 } { i32 7, [4 x i8] c"ab\00\00", i32 9 }], align 4
"#;
        let m = import_text(src, "t").expect("array-of-struct global imports");
        // i32 7 | 'a' 'b' 0 0 | i32 9  => 12 bytes
        assert_eq!(
            global_bytes(&m, "v"),
            vec![7, 0, 0, 0, b'a', b'b', 0, 0, 9, 0, 0, 0]
        );
    }

    #[test]
    fn explicit_double_array_global_serializes_ieee_bytes() {
        let src = r#"
@d = global [2 x double] [double 1.0, double 2.0], align 8
"#;
        let m = import_text(src, "t").expect("double array global imports");
        let mut want = 1.0f64.to_le_bytes().to_vec();
        want.extend_from_slice(&2.0f64.to_le_bytes());
        assert_eq!(global_bytes(&m, "d"), want);
    }

    #[test]
    fn forward_referenced_struct_types_resolve() {
        // `%struct.Globals` (line 1) has a by-value field of `%struct.min_info`
        // (line 2) — a forward reference LLVM does not topologically order. The
        // fixpoint pre-pass must still lay out Globals: i8(0) + pad + min_info
        // {i32,i32}=8 at offset 4 + ptr at 16 => size 24, align 8.
        let src = r#"
%struct.Globals = type { i8, %struct.min_info, ptr }
%struct.min_info = type { i32, i32 }
@g = global %struct.Globals zeroinitializer, align 8
"#;
        let m = import_text(src, "t").expect("forward-referenced struct resolves");
        let g = m.globals.iter().find(|g| g.name == "g").expect("global g");
        match &g.initializer {
            Some(Constant::Aggregate(bytes)) => assert_eq!(bytes.len(), 24),
            other => panic!("expected 24 zero bytes, got {:?}", other),
        }
    }

    #[test]
    fn null_pointer_global_lowers_to_pointer_sized_zero_bytes() {
        // `@g = common global ptr null` -> 8 zero bytes (Ptr-typed), the form
        // the codegen global tree accepts (an Int initializer on Ptr is rejected).
        let src = r#"
@g = common local_unnamed_addr global ptr null, align 8
"#;
        let m = import_text(src, "t").expect("ptr null global imports");
        let g = m.globals.iter().find(|g| g.name == "g").expect("global g");
        assert_eq!(g.ty, Ty::Ptr);
        match &g.initializer {
            Some(Constant::Aggregate(bytes)) => {
                assert_eq!(bytes.len(), 8, "pointer == 8 bytes");
                assert!(bytes.iter().all(|b| matches!(b, Constant::Int(0))));
            }
            other => panic!("expected 8 zero bytes, got {:?}", other),
        }
    }

    #[test]
    fn array_gep_non_i32_element_lowers_to_byte_offset() {
        // GEP into `[28 x i64]` scales by 8; the element kind (not just
        // i8/i32/f32) is irrelevant — only its size matters.
        let src = r#"
@t = global [28 x i64] zeroinitializer, align 8
define i64 @f(i64 %i) {
entry:
  %p = getelementptr inbounds [28 x i64], ptr @t, i64 0, i64 %i
  %v = load i64, ptr %p, align 8
  ret i64 %v
}
"#;
        let m = import_text(src, "t").expect("i64-array GEP imports");
        let f = func_named(&m, "f");
        assert!(
            count_insts(f, |i| matches!(i, Inst::GEP { .. })) >= 1,
            "i64-array GEP must lower to a byte GEP"
        );
    }

    #[test]
    fn global_address_phi_operand_materializes_stub() {
        // A `@g` incoming value on a phi edge materialises the global's base
        // stub in the predecessor block instead of failing closed.
        let src = r#"
@a = global i32 0, align 4
@b = global i32 0, align 4
define ptr @f(i1 %c) {
entry:
  br i1 %c, label %t, label %e
t:
  br label %m
e:
  br label %m
m:
  %p = phi ptr [ @a, %t ], [ @b, %e ]
  ret ptr %p
}
"#;
        let m = import_text(src, "t").expect("global phi operand imports");
        let f = func_named(&m, "f");
        // Two @a/@b base stubs materialise on the two predecessor edges.
        assert!(
            count_insts(f, |i| matches!(i, Inst::Const { ty: Ty::Ptr, .. })) >= 2,
            "global phi operands must materialise stub pointers on the edges"
        );
    }

    #[test]
    fn constant_expr_gep_byte_form_folds() {
        // The clang -O1 canonical byte form: `(i8, ptr @g, i64 8)` == &g + 8.
        let src = r#"
@g = global [4 x i64] zeroinitializer
define i64 @f() {
entry:
  store i64 -6, ptr getelementptr inbounds nuw (i8, ptr @g, i64 8), align 8
  %v = load i64, ptr getelementptr inbounds nuw (i8, ptr @g, i64 8), align 8
  ret i64 %v
}
"#;
        let m = import_text(src, "t").expect("byte-form constexpr GEP folds");
        let f = func_named(&m, "f");
        // Two uses (store + load), each a base stub + i8 GEP for +8.
        assert!(
            count_insts(f, |i| matches!(
                i,
                Inst::GEP {
                    pointee_ty: Ty::I8,
                    ..
                }
            )) >= 2,
            "byte-form constexpr GEP must add +8 via runtime i8 GEPs"
        );
    }

    #[test]
    fn constant_expr_non_global_gep_operand_stays_unsupported() {
        // A const-expr GEP on a non-global base has no evaluator; fail closed.
        let src = r#"
define i32 @f(ptr %p) {
entry:
  %v = load i32, ptr getelementptr inbounds (i8, ptr %p, i64 4), align 4
  ret i32 %v
}
"#;
        assert!(
            matches!(import_text(src, "t"), Err(Error::Unsupported(_))),
            "const-expr GEP on a non-global base must stay unsupported"
        );
    }

    /// An inline `inttoptr` constant-expression call argument is unsupported
    /// (was a `parse:` crash on the `to ptr)` tail before the fix).
    #[test]
    fn constant_expr_call_arg_is_unsupported() {
        let src = r#"
define void @f() {
entry:
  call void @sink(ptr noundef inttoptr (i64 123456 to ptr))
  ret void
}
declare void @sink(ptr)
"#;
        let r = import_text(src, "t");
        assert!(
            matches!(r, Err(Error::Unsupported(_))),
            "constant-expression call argument should be unsupported, got {:?}",
            r
        );
    }

    /// Calls to LLVM intrinsics (`@llvm.ctpop.*`, `@llvm.memcpy.*`, …) fail
    /// closed as unsupported rather than emitting an undefined `_llvm.*` symbol
    /// that would fail to link.
    #[test]
    fn llvm_intrinsic_call_is_unsupported() {
        let src = r#"
define i32 @f(i32 %x) {
entry:
  %c = call i32 @llvm.ctpop.i32(i32 %x)
  ret i32 %c
}
declare i32 @llvm.ctpop.i32(i32)
"#;
        let r = import_text(src, "t");
        assert!(
            matches!(r, Err(Error::Unsupported(_))),
            "llvm intrinsic call should be unsupported, got {:?}",
            r
        );
    }

    /// `bfloat` / `fp128` / `x86_fp80` / `ppc_fp128` stay Unsupported —
    /// trust_ir has no matching type.
    #[test]
    fn other_float_widths_are_unsupported() {
        for ty in ["bfloat", "fp128", "x86_fp80", "ppc_fp128"] {
            let src = format!(
                "define {} @f({} %a) {{\nentry:\n  ret {} %a\n}}\n",
                ty, ty, ty
            );
            let r = import_text(&src, "t");
            assert!(
                matches!(r, Err(Error::Unsupported(_))),
                "type {} should be unsupported, got {:?}",
                ty,
                r
            );
        }
    }

    #[test]
    fn half_import_maps_to_trust_ir_f16() {
        let src = "define half @f(half %a) {\nentry:\n  ret half %a\n}\n";
        let m = import_text(src, "t").expect("half import");
        let f = &m.functions[0];
        let func_ty = &m.func_types[f.ty.index() as usize];
        assert_eq!(func_ty.params, vec![Ty::F16]);
        assert_eq!(func_ty.returns, vec![Ty::F16]);
        assert_eq!(f.blocks[0].params, vec![(ValueId::new(0), Ty::F16)]);
    }

    #[test]
    fn half_hex_literal_maps_to_trust_ir_f16_const() {
        let src = r#"
define half @f(half %a) {
entry:
  %b = fadd half %a, 0xH3C00
  ret half %b
}
"#;
        let m = import_text(src, "t").expect("half hex import");
        let f = &m.functions[0];
        let mut saw_const = false;
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::Const {
                    ty: Ty::F16,
                    value: Constant::Float(v),
                } = &node.inst
                    && (*v - 1.0).abs() < f64::EPSILON
                {
                    saw_const = true;
                }
            }
        }
        assert!(saw_const, "expected F16 Float(1.0) materialization");
    }

    /// FP casts: sitofp / fptosi / uitofp / fptoui / fpext / fptrunc.
    #[test]
    fn fp_casts_all_six() {
        let src = r#"
define double @f(i32 %a, double %b, float %c) {
entry:
  %x = sitofp i32 %a to double
  %y = uitofp i32 %a to double
  %z = fpext float %c to double
  %t = fptrunc double %b to float
  %u = fptosi double %b to i32
  %v = fptoui double %b to i32
  ret double %x
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        let mut ops = std::collections::HashSet::new();
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::Cast { op, .. } = &node.inst {
                    ops.insert(*op);
                }
            }
        }
        for want in [
            CastOp::SIToFP,
            CastOp::UIToFP,
            CastOp::FPExt,
            CastOp::FPTrunc,
            CastOp::FPToSI,
            CastOp::FPToUI,
        ] {
            assert!(ops.contains(&want), "missing {:?} in {:?}", want, ops);
        }
    }

    /// The body form clang -O0 actually emits for
    /// `float add(float a, float b) { return a + b; }` on Apple
    /// Silicon, with anonymous-register SSA, must round-trip through
    /// the importer into a trust_ir::Module that has exactly one function
    /// with one block containing a `BinOp { FAdd, F32, .. }`.
    #[test]
    fn clang_style_f32_add_roundtrip() {
        let src = r#"
define float @add_f(float noundef %0, float noundef %1) {
  %3 = alloca float, align 4
  %4 = alloca float, align 4
  store float %0, ptr %3, align 4
  store float %1, ptr %4, align 4
  %5 = load float, ptr %3, align 4
  %6 = load float, ptr %4, align 4
  %7 = fadd float %5, %6
  ret float %7
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
        let f = &m.functions[0];
        assert_eq!(f.name, "add_f");
        let mut saw_fadd = false;
        for blk in &f.blocks {
            for node in &blk.body {
                if let Inst::BinOp {
                    op: BinOp::FAdd,
                    ty: Ty::F32,
                    ..
                } = &node.inst
                {
                    saw_fadd = true;
                }
            }
        }
        assert!(saw_fadd);
    }

    #[test]
    fn switch_single_line_is_parsed() {
        // Regression for expansion item #4: simple inline switch.
        let src = r#"
define i32 @f(i32 %a) {
entry:
  switch i32 %a, label %d [ i32 1, label %one ]
one:
  ret i32 1
d:
  ret i32 0
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        // entry + one + d = 3 blocks.
        assert_eq!(f.blocks.len(), 3);
        // The entry-block terminator should be a Switch.
        let term = f.blocks[0]
            .terminator()
            .expect("entry block has a terminator");
        match &term.inst {
            Inst::Switch { cases, .. } => {
                assert_eq!(cases.len(), 1);
                assert_eq!(cases[0].value, Constant::Int(1));
            }
            other => panic!("expected Switch, got {:?}", other),
        }
    }

    #[test]
    fn switch_multiline_clang_shape() {
        // Matches what clang -O0 actually emits: header with `[`, one
        // case per line, closing `]` on its own line, numeric block
        // labels.
        let src = r#"
define i32 @dispatch(i32 %x) {
entry:
  switch i32 %x, label %d [
    i32 0, label %c0
    i32 1, label %c1
    i32 42, label %c42
  ]
c0:
  ret i32 10
c1:
  ret i32 20
c42:
  ret i32 30
d:
  ret i32 -1
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        // 1 entry + 4 targets = 5 blocks.
        assert_eq!(f.blocks.len(), 5);
        match &f.blocks[0].terminator().unwrap().inst {
            Inst::Switch {
                cases,
                default_args,
                ..
            } => {
                assert_eq!(cases.len(), 3);
                assert!(default_args.is_empty());
                let vals: Vec<i128> = cases
                    .iter()
                    .map(|c| match c.value {
                        Constant::Int(n) => n,
                        _ => panic!("non-int case"),
                    })
                    .collect();
                assert_eq!(vals, vec![0, 1, 42]);
                for c in cases {
                    assert!(c.args.is_empty(), "importer produces no edge args");
                }
            }
            other => panic!("expected Switch, got {:?}", other),
        }
    }

    #[test]
    fn switch_i8_widths() {
        // Exercise an i8 selector to confirm narrow-width support.
        let src = r#"
define i8 @f(i8 %x) {
entry:
  switch i8 %x, label %d [
    i8 0, label %z
    i8 1, label %o
  ]
z:
  ret i8 100
o:
  ret i8 101
d:
  ret i8 -1
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
    }

    #[test]
    fn switch_i64_widths() {
        let src = r#"
define i64 @f(i64 %x) {
entry:
  switch i64 %x, label %d [
    i64 9999999999, label %big
    i64 -1, label %neg
  ]
big:
  ret i64 1
neg:
  ret i64 2
d:
  ret i64 0
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
    }

    #[test]
    fn switch_empty_case_list_is_just_a_jump() {
        // `switch i32 %x, label %d []` is legal LLVM — equivalent to
        // `br label %d`. We lower it as a Switch with no cases; the
        // codegen side is responsible for turning that into a direct
        // jump.
        let src = r#"
define i32 @f(i32 %x) {
entry:
  switch i32 %x, label %d [ ]
d:
  ret i32 0
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        match &f.blocks[0].terminator().unwrap().inst {
            Inst::Switch { cases, .. } => assert!(cases.is_empty()),
            other => panic!("expected Switch, got {:?}", other),
        }
    }

    #[test]
    fn switch_case_type_mismatch_is_unsupported() {
        let src = r#"
define i32 @f(i32 %x) {
entry:
  switch i32 %x, label %d [
    i8 1, label %o
  ]
o:
  ret i32 1
d:
  ret i32 0
}
"#;
        let r = import_text(src, "t");
        assert!(
            matches!(r, Err(Error::Unsupported(_))),
            "mismatched case type should be unsupported, got {:?}",
            r
        );
    }

    #[test]
    fn struct_type_is_parsed() {
        let src = r#"
%struct.Pair = type { i32, i32 }

define void @f() {
entry:
  ret void
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert!(m.structs.is_empty(), "layouts stay parser-internal");
        assert_eq!(m.functions.len(), 1);
    }

    #[test]
    fn alloca_struct_yields_i8_count() {
        let src = r#"
%struct.Pair = type { i32, i32 }

define void @f() {
entry:
  %p = alloca %struct.Pair, align 8
  ret void
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert!(has_struct_alloca(&m.functions[0]));
    }

    #[test]
    fn struct_gep_field_0_offset_is_zero() {
        let src = r#"
%struct.Pair = type { i32, i32 }

define ptr @f(ptr %p) {
entry:
  %q = getelementptr inbounds %struct.Pair, ptr %p, i32 0, i32 0
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(struct_gep_offsets(&m.functions[0]), vec![0]);
    }

    #[test]
    fn struct_gep_field_1_offset_is_field_offset() {
        let src = r#"
%struct.Pair = type { i32, i32 }
%struct.Misaligned = type { i8, i64 }

define ptr @pair(ptr %p) {
entry:
  %q = getelementptr inbounds %struct.Pair, ptr %p, i32 0, i32 1
  ret ptr %q
}

define ptr @mis(ptr %p) {
entry:
  %q = getelementptr inbounds %struct.Misaligned, ptr %p, i32 0, i32 1
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(struct_gep_offsets(&m.functions[0]), vec![4]);
        assert_eq!(struct_gep_offsets(&m.functions[1]), vec![8]);
    }

    #[test]
    fn struct_gep_field_2_byte_offset_honors_align() {
        let src = r#"
%struct.Triple = type { i8, i32, i64 }

define ptr @f(ptr %p) {
entry:
  %field = getelementptr inbounds %struct.Triple, ptr %p, i32 0, i32 2
  %next = getelementptr inbounds %struct.Triple, ptr %p, i32 1
  ret ptr %next
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(struct_gep_offsets(&m.functions[0]), vec![8, 16]);
    }

    #[test]
    fn scalar_pointer_gep_ary3_argv_shape_is_parsed() {
        let src = r#"
define ptr @f(ptr %argv) {
entry:
  %arg1 = getelementptr inbounds ptr, ptr %argv, i64 1
  ret ptr %arg1
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(gep_shapes(&m.functions[0]), vec![(Ty::Ptr, 1)]);
    }

    #[test]
    fn scalar_pointer_gep_supported_pointee_types_are_parsed() {
        for (ll_ty, want_ty) in [
            ("ptr", Ty::Ptr),
            ("i8", Ty::I8),
            ("i16", Ty::I16),
            ("i32", Ty::I32),
            ("i64", Ty::I64),
            ("float", Ty::F32),
            ("double", Ty::F64),
        ] {
            let src = format!(
                r#"
define ptr @f(ptr %p, i64 %idx) {{
entry:
  %q = getelementptr inbounds {}, ptr %p, i64 %idx
  ret ptr %q
}}
"#,
                ll_ty
            );
            let m = import_text(&src, "t").expect("parse");
            assert_eq!(
                gep_shapes(&m.functions[0]),
                vec![(want_ty, 1)],
                "pointee type {ll_ty}"
            );
        }
    }

    #[test]
    fn scalar_pointer_gep_i32_index_is_widened() {
        let src = r#"
define ptr @f(ptr %p, i32 %idx) {
entry:
  %q = getelementptr inbounds i32, ptr %p, i32 %idx
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        assert_eq!(gep_shapes(f), vec![(Ty::I32, 1)]);
        assert!(f.blocks.iter().any(|blk| {
            blk.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::Cast {
                        op: CastOp::SExt,
                        src_ty: Ty::I32,
                        dst_ty: Ty::I64,
                        ..
                    }
                )
            })
        }));
    }

    #[test]
    fn scalar_pointer_gep_multi_index_stays_unsupported() {
        let src = r#"
define ptr @f(ptr %p) {
entry:
  %q = getelementptr inbounds ptr, ptr %p, i64 1, i64 2
  ret ptr %q
}
"#;
        let r = import_text(src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("scalar pointer GEP requires exactly one index"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!(
                "multi-index scalar GEP should be unsupported, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn byte_array_global_gep_sieve_shape_is_parsed() {
        let src = r#"
@main.flags = internal global [8193 x i8] zeroinitializer, align 1

define ptr @f(i64 %idx) {
entry:
  %q = getelementptr inbounds [8193 x i8], ptr @main.flags, i64 0, i64 %idx
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(gep_shapes(&m.functions[0]), vec![(Ty::I8, 1)]);
    }

    #[test]
    fn byte_array_global_gep_i32_index_is_widened() {
        let src = r#"
@main.flags = internal global [8193 x i8] zeroinitializer, align 1

define ptr @f(i32 %idx) {
entry:
  %q = getelementptr inbounds [8193 x i8], ptr @main.flags, i64 0, i32 %idx
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        assert_eq!(gep_shapes(f), vec![(Ty::I8, 1)]);
        assert!(f.blocks.iter().any(|blk| {
            blk.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::Cast {
                        op: CastOp::SExt,
                        src_ty: Ty::I32,
                        dst_ty: Ty::I64,
                        ..
                    }
                )
            })
        }));
    }

    #[test]
    fn byte_array_global_gep_nonzero_outer_index_stays_unsupported() {
        let src = r#"
@main.flags = internal global [8193 x i8] zeroinitializer, align 1

define ptr @f(i64 %idx) {
entry:
  %q = getelementptr inbounds [8193 x i8], ptr @main.flags, i64 1, i64 %idx
  ret ptr %q
}
"#;
        let r = import_text(src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("requires zero leading index"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!(
                "nonzero leading array index should be unsupported, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn byte_array_global_gep_extra_index_stays_unsupported() {
        let src = r#"
@main.flags = internal global [8193 x i8] zeroinitializer, align 1

define ptr @f(i64 %idx) {
entry:
  %q = getelementptr inbounds [8193 x i8], ptr @main.flags, i64 0, i64 %idx, i64 1
  ret ptr %q
}
"#;
        let r = import_text(src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("requires leading zero and one element index"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!("extra array index should be unsupported, got {:?}", other),
        }
    }

    #[test]
    fn fixed_array_nested_i32_zero_global_is_parsed_as_byte_storage() {
        let src = r#"
@ima = common global [41 x [41 x i32]] zeroinitializer, align 4
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals.len(), 1);
        let global = &m.globals[0];
        assert_eq!(global.name, "ima");
        assert_eq!(global.ty, Ty::Ptr);
        assert!(global.mutable);
        let Some(Constant::Aggregate(elems)) = &global.initializer else {
            panic!("expected byte aggregate initializer");
        };
        assert_eq!(elems.len(), 41 * 41 * 4);
        assert!(elems.iter().all(|elem| *elem == Constant::Int(0)));
    }

    #[test]
    fn fixed_array_matrix_gep_uses_byte_scaled_gep_not_copy() {
        let src = r#"
@imr = common global [41 x [41 x i32]] zeroinitializer, align 4

define ptr @f(i64 %row) {
entry:
  %q = getelementptr inbounds [41 x [41 x i32]], ptr @imr, i64 0, i64 %row
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("parse");
        let f = &m.functions[0];
        assert_eq!(gep_shapes(f), vec![(Ty::I8, 1)]);
        assert!(f.blocks.iter().all(|blk| {
            blk.body
                .iter()
                .all(|node| !matches!(node.inst, Inst::Copy { .. }))
        }));
        assert!(f.blocks.iter().any(|blk| {
            blk.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(164),
                    }
                )
            })
        }));
        assert!(f.blocks.iter().any(|blk| {
            blk.body.iter().any(|node| {
                matches!(
                    &node.inst,
                    Inst::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I64,
                        ..
                    }
                )
            })
        }));
    }

    #[test]
    fn struct_e2e_roundtrip() {
        let src = r#"
%struct.Pair = type { i32, i32 }

define i32 @f() {
entry:
  %p = alloca %struct.Pair, align 8
  %a = getelementptr inbounds %struct.Pair, ptr %p, i32 0, i32 0
  %b = getelementptr inbounds %struct.Pair, ptr %p, i32 0, i32 1
  store i32 1, ptr %a, align 4
  store i32 2, ptr %b, align 4
  %x = load i32, ptr %a, align 4
  %y = load i32, ptr %b, align 4
  %z = add i32 %x, %y
  ret i32 %z
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
    }

    #[test]
    fn scalar_global_i32_is_parsed() {
        let src = r#"
@x = global i32 42
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals.len(), 1);
        assert_eq!(m.globals[0].name, "x");
        assert_eq!(m.globals[0].ty, Ty::I32);
        assert!(m.globals[0].mutable);
        assert_eq!(m.globals[0].initializer, Some(Constant::Int(42)));
    }

    #[test]
    fn scalar_global_i64_zeroinitializer() {
        let src = r#"
@y = global i64 zeroinitializer
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals[0].initializer, Some(Constant::Int(0)));
    }

    #[test]
    fn zero_i8_array_global_is_parsed_as_mutable_byte_storage() {
        let src = r#"
@main.flags = internal global [8193 x i8] zeroinitializer, align 1
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals.len(), 1);
        let global = &m.globals[0];
        assert_eq!(global.name, "main.flags");
        assert_eq!(global.ty, Ty::Ptr);
        assert!(global.mutable);
        assert!(matches!(global.linkage, Linkage::Internal));
        let Some(Constant::Aggregate(elems)) = &global.initializer else {
            panic!("expected byte aggregate initializer");
        };
        assert_eq!(elems.len(), 8193);
        assert!(elems.iter().all(|elem| *elem == Constant::Int(0)));
    }

    #[test]
    fn oversized_zero_i8_array_global_stays_unsupported_without_allocation() {
        let src = format!(
            "@huge = internal global [{} x i8] zeroinitializer, align 1\n",
            MAX_IMPORTED_GLOBAL_INIT_BYTES + 1
        );
        let r = import_text(&src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("over importer limit"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!(
                "oversized array global should be unsupported, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn explicit_i16_array_global_is_parsed_as_little_endian_byte_storage() {
        let src = r#"
@staticData = internal global [16 x i16] [i16 0, i16 1, i16 2, i16 3, i16 4, i16 5, i16 6, i16 7, i16 8, i16 9, i16 10, i16 11, i16 12, i16 13, i16 14, i16 15], align 2
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals.len(), 1);
        let global = &m.globals[0];
        assert_eq!(global.name, "staticData");
        assert_eq!(global.ty, Ty::Ptr);
        assert!(global.mutable);
        assert!(matches!(global.linkage, Linkage::Internal));
        let Some(Constant::Aggregate(elems)) = &global.initializer else {
            panic!("expected byte aggregate initializer");
        };
        let bytes: Vec<i128> = elems
            .iter()
            .map(|elem| match elem {
                Constant::Int(byte) => *byte,
                other => panic!("expected byte int, got {:?}", other),
            })
            .collect();
        assert_eq!(bytes.len(), 32);
        assert_eq!(&bytes[..8], &[0, 0, 1, 0, 2, 0, 3, 0]);
        assert_eq!(&bytes[28..], &[14, 0, 15, 0]);
    }

    #[test]
    fn explicit_integer_array_global_length_mismatch_stays_unsupported() {
        let src = r#"
@staticData = internal global [2 x i16] [i16 0], align 2
"#;
        let r = import_text(src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("length mismatch"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!("length mismatch should be unsupported, got {:?}", other),
        }
    }

    #[test]
    fn explicit_integer_array_global_element_type_mismatch_stays_unsupported() {
        let src = r#"
@staticData = internal global [2 x i16] [i16 0, i32 1], align 2
"#;
        let r = import_text(src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("does not match `i16`"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!(
                "element type mismatch should be unsupported, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn explicit_integer_array_global_unsupported_width_stays_unsupported() {
        let src = r#"
@wide = internal global [1 x i128] [i128 0], align 16
"#;
        let r = import_text(src, "t");
        match r {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("element type `I128`"),
                    "unexpected unsupported reason: {msg}"
                );
            }
            other => panic!(
                "unsupported integer width should be unsupported, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn zero_non_i8_array_global_lowers_to_byte_image() {
        // A `zeroinitializer` of any element type is `size()` zero bytes — the
        // byte image is layout-independent, so `[16 x i16]` == 32 zero bytes.
        let src = r#"
@words = internal global [16 x i16] zeroinitializer, align 2
"#;
        let m = import_text(src, "t").expect("non-i8 zero array global imports");
        assert_eq!(m.globals.len(), 1);
        assert_eq!(m.globals[0].name, "words");
        match &m.globals[0].initializer {
            Some(Constant::Aggregate(bytes)) => {
                assert_eq!(bytes.len(), 32, "16 x i16 == 32 bytes");
                assert!(
                    bytes.iter().all(|b| matches!(b, Constant::Int(0))),
                    "zeroinitializer must be all zero bytes"
                );
            }
            other => panic!("expected zero byte aggregate, got {:?}", other),
        }
    }

    #[test]
    fn scalar_global_float() {
        let src = r#"
@z = global float 3.14
"#;
        let m = import_text(src, "t").expect("parse");
        match &m.globals[0].initializer {
            Some(Constant::Float(v)) => assert!((*v - (314.0 / 100.0)).abs() < 1e-9),
            other => panic!("expected float initializer, got {:?}", other),
        }
    }

    #[test]
    fn external_scalar_global_declaration_has_no_initializer() {
        let src = r#"
@var_13 = external global i8, align 1
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals.len(), 1);
        assert_eq!(m.globals[0].name, "var_13");
        assert_eq!(m.globals[0].ty, Ty::I8);
        assert!(m.globals[0].mutable);
        assert_eq!(m.globals[0].initializer, None);
    }

    #[test]
    fn yarpgen_external_globals_are_unsupported_not_parse_errors() {
        let src = r#"
@var_13 = external global i8, align 1
@arr_9 = external global [24 x [24 x [24 x i64]]], align 8
"#;
        let r = import_text(src, "t");
        assert!(
            matches!(r, Err(Error::Unsupported(_))),
            "YARPGen external aggregate should be unsupported, got {:?}",
            r
        );
    }

    #[test]
    fn global_with_constant_keyword_is_immutable() {
        let src = r#"
@k = constant i32 99
"#;
        let m = import_text(src, "t").expect("parse");
        assert!(!m.globals[0].mutable);
        assert_eq!(m.globals[0].initializer, Some(Constant::Int(99)));
        assert_eq!(m.globals[0].align, None);
    }

    #[test]
    fn string_global_is_parsed() {
        let src = r#"
@.str = private unnamed_addr constant [8 x i8] c"success\00", align 1

define void @f() {
entry:
  ret void
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.globals.len(), 1);
        assert_eq!(m.globals[0].name, ".str");
        assert_eq!(m.globals[0].align, Some(1));
        if let Some(Constant::Aggregate(elems)) = &m.globals[0].initializer {
            assert_eq!(elems.len(), 8);
            // "success\0" = 8 bytes.
        } else {
            panic!("expected Aggregate initializer");
        }
    }

    #[test]
    fn explicit_global_alignment_survives_scalar_and_flattened_array_import() {
        let src = r#"
@scalar = global i32 7, align 4
@bytes = internal global [4 x i8] [i8 1, i8 2, i8 3, i8 4], align 1
"#;
        let m = import_text(src, "global_alignment").expect("parse aligned globals");
        assert_eq!(m.globals[0].align, Some(4));
        assert_eq!(m.globals[1].align, Some(1));
    }

    #[test]
    fn malformed_and_duplicate_global_alignment_fail_closed() {
        for raw in ["0", "3", "4294967296"] {
            let src = format!("@g = global i32 0, align {raw}\n");
            assert!(
                matches!(
                    import_text(&src, "bad_global_alignment"),
                    Err(Error::Unsupported(_))
                ),
                "alignment {raw} must fail closed"
            );
        }
        let duplicate = "@g = global i32 0, align 4, align 8\n";
        assert!(
            matches!(
                import_text(duplicate, "duplicate_global_alignment"),
                Err(Error::Unsupported(_))
            ),
            "duplicate alignment attributes must fail closed"
        );
    }

    #[test]
    fn cast_sext_zext() {
        let src = r#"
define i32 @f(i8 %a, i16 %b) {
entry:
  %x = sext i8 %a to i32
  %y = zext i16 %b to i32
  %s = add i32 %x, %y
  ret i32 %s
}
"#;
        let m = import_text(src, "t").expect("parse");
        assert_eq!(m.functions.len(), 1);
    }

    #[test]
    fn printf_call_signature_is_tolerated() {
        let src = r#"
declare i32 @printf(ptr noundef, ...)

define i32 @main() {
entry:
  ret i32 0
}
"#;
        let m = import_text(src, "t").expect("parse");
        // We register the printf declaration but do not require calls.
        assert!(!m.func_types.is_empty());
    }

    #[test]
    fn global_address_in_call_is_materialized() {
        let src = r#"
@.str = private unnamed_addr constant [6 x i8] c"hi!\0A\00", align 1

declare i32 @printf(ptr noundef, ...)

define i32 @main() {
entry:
  %r = call i32 (ptr, ...) @printf(ptr noundef @.str)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("parse");
        let printf = m
            .functions
            .iter()
            .find(|f| f.name == "printf")
            .expect("printf declaration should be preserved in the module");
        assert!(printf.blocks.is_empty());
        assert!(matches!(printf.linkage, Linkage::External));
        let main = m
            .functions
            .iter()
            .find(|f| f.name == "main")
            .expect("main function");
        let entry = &main.blocks[0];
        assert!(
            entry.body.iter().any(|n| {
                matches!(
                    &n.inst,
                    Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::Int(_)
                    }
                )
            }),
            "expected a pointer const materializing @.str, body={:?}",
            entry.body
        );
        assert!(
            entry
                .body
                .iter()
                .any(|n| matches!(&n.inst, Inst::Call { .. })),
            "expected a Call to @printf"
        );
    }

    #[test]
    fn forward_vararg_call_preserves_fixed_param_count() {
        let src = r#"
@.str = private unnamed_addr constant [8 x i8] c"%d %d\0A\00", align 1

define i32 @main() {
entry:
  %r = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef 1, i32 noundef 2)
  ret i32 0
}

declare i32 @printf(ptr noundef, ...)
"#;
        let m = import_text(src, "t").expect("parse");
        let printf = m
            .functions
            .iter()
            .find(|f| f.name == "printf")
            .expect("printf declaration should be preserved");
        let func_ty = &m.func_types[printf.ty.index() as usize];
        assert!(func_ty.is_vararg);
        assert_eq!(func_ty.params, vec![Ty::Ptr]);
    }

    #[test]
    fn forward_call_without_explicit_func_type_uses_argument_types() {
        let src = r#"
define i32 @main(ptr %p, i64 %n) {
entry:
  %r = call i64 @callee(ptr noundef %p, i64 noundef %n, ptr noundef %p)
  %t = trunc i64 %r to i32
  ret i32 %t
}

define internal i64 @callee(ptr noundef %p, i64 noundef %n, ptr noundef %q) {
entry:
  ret i64 %n
}
"#;
        let m = import_text(src, "t").expect("parse");
        let callee = m
            .functions
            .iter()
            .find(|f| f.name == "callee")
            .expect("callee definition should be preserved");
        assert_eq!(
            m.functions
                .iter()
                .filter(|function| function.name == "callee")
                .count(),
            1,
            "the definition must replace its forward-call placeholder"
        );
        assert!(
            !callee.blocks.is_empty(),
            "the preserved callee must be the real definition"
        );
        assert!(matches!(callee.linkage, Linkage::Internal));
        let func_ty = &m.func_types[callee.ty.index() as usize];
        assert!(!func_ty.is_vararg);
        assert_eq!(func_ty.params, vec![Ty::Ptr, Ty::I64, Ty::Ptr]);
        assert_eq!(func_ty.returns, vec![Ty::I64]);
    }

    #[test]
    fn duplicate_function_definitions_fail_closed() {
        let src = r#"
define i32 @f() {
entry:
  ret i32 1
}

define i32 @f() {
entry:
  ret i32 2
}
"#;
        let err = import_text(src, "duplicate_definition")
            .expect_err("a second body for one FuncId must fail closed");
        assert!(
            err.to_string()
                .contains("multiple definitions of function `@f`"),
            "unexpected diagnostic: {err}"
        );
    }

    #[test]
    fn forward_call_signature_mismatch_fails_closed() {
        let src = r#"
define i32 @main(i64 %x) {
entry:
  %r = call i64 @callee(i64 %x)
  %t = trunc i64 %r to i32
  ret i32 %t
}

define internal i32 @callee(i32 %x) {
entry:
  ret i32 %x
}
"#;
        let err = import_text(src, "forward_signature_mismatch")
            .expect_err("a later definition must match its forward-call signature");
        assert!(
            err.to_string()
                .contains("conflicting signatures for function `@callee`"),
            "unexpected diagnostic: {err}"
        );
    }

    #[test]
    fn calloc_o0_pointer_slot_loads_preserve_noalias_for_inbounds_gep() {
        let src = r#"
declare ptr @calloc(i64 noundef, i64 noundef) #0

define void @main(i64 %n) {
entry:
  %slot = alloca ptr, align 8
  %p = call ptr @calloc(i64 noundef %n, i64 noundef 4) #0
  store ptr %p, ptr %slot, align 8
  br label %loop

loop:
  %q = load ptr, ptr %slot, align 8
  %addr = getelementptr inbounds i32, ptr %q, i64 0
  ret void
}

attributes #0 = { allocsize(0,1) }
"#;
        let m = import_text(src, "calloc_o0").expect("parse calloc fixture");
        let main = m
            .functions
            .iter()
            .find(|func| func.name == "main")
            .expect("main function");

        let mut call_has_allocator_facts = false;
        let mut load_has_allocator_facts = false;
        let mut gep_has_inbounds_and_noalias = false;

        for block in &main.blocks {
            for node in &block.body {
                match &node.inst {
                    Inst::Call { .. } => {
                        call_has_allocator_facts = node.proofs.contains(&ProofAnnotation::NoAlias)
                            && node.proofs.contains(&ProofAnnotation::Aligned(16));
                    }
                    Inst::Load { ty: Ty::Ptr, .. } => {
                        load_has_allocator_facts = node.proofs.contains(&ProofAnnotation::NoAlias)
                            && node.proofs.contains(&ProofAnnotation::Aligned(16));
                    }
                    Inst::GEP { .. } => {
                        gep_has_inbounds_and_noalias =
                            node.proofs.contains(&ProofAnnotation::InBounds)
                                && node.proofs.contains(&ProofAnnotation::NoAlias);
                    }
                    _ => {}
                }
            }
        }

        assert!(call_has_allocator_facts);
        assert!(load_has_allocator_facts);
        assert!(gep_has_inbounds_and_noalias);
    }

    // ---- Cluster 1: `\01` asm-label (verbatim, no-mangle) symbols ----------

    #[test]
    fn asm_label_call_strips_escape_and_one_underscore() {
        // `@"\01_clock"` is the Darwin verbatim symbol `_clock`; codegen prepends
        // `_`, so the importer must yield `clock` (strip `\01`, strip one `_`).
        let src = r#"
declare i64 @"\01_clock"()
define i64 @second() {
entry:
  %t = call i64 @"\01_clock"()
  ret i64 %t
}
"#;
        let m = import_text(src, "t").expect("asm-label call imports");
        assert!(
            m.functions.iter().any(|f| f.name == "clock"),
            "callee must de-mangle to the verbatim symbol `clock`, got {:?}",
            m.functions.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
        assert!(
            !m.functions.iter().any(|f| f.name.contains("\\01")),
            "no function name may retain the raw `\\01` escape"
        );
    }

    #[test]
    fn asm_label_global_strips_escape_and_one_underscore() {
        let src = r#"
@"\01_myvar" = global i32 0, align 4
"#;
        let m = import_text(src, "t").expect("asm-label global imports");
        assert!(
            m.globals.iter().any(|g| g.name == "myvar"),
            "global must de-mangle to `myvar`, got {:?}",
            m.globals.iter().map(|g| &g.name).collect::<Vec<_>>()
        );
    }

    #[test]
    fn asm_label_without_leading_underscore_fails_closed() {
        // A `\01` label not starting with `_` cannot be represented on Mach-O
        // without a dedicated no-mangle flag: fail closed, never emit a wrong sym.
        let src = r#"
declare void @"\01foo"()
define void @f() {
entry:
  call void @"\01foo"()
  ret void
}
"#;
        assert!(
            matches!(import_text(src, "t"), Err(Error::Unsupported(_))),
            "`\\01` label without leading `_` must be unsupported, not miscompiled"
        );
    }

    #[test]
    fn asm_label_colliding_with_plain_symbol_fails_closed() {
        // `@"\01_dup"` de-mangles to `dup`, which also names the plain `@dup`;
        // two source-distinct symbols would silently merge — fail closed.
        let src = r#"
declare void @"\01_dup"()
declare void @dup()
"#;
        assert!(
            matches!(import_text(src, "t"), Err(Error::Unsupported(_))),
            "asm-label / plain-symbol collision must be unsupported"
        );
    }

    // ---- Cluster 2: struct GEP with a dynamic outer index ------------------

    #[test]
    fn struct_gep_dynamic_outer_index_scales_by_struct_size() {
        // `%struct.S` is { i32, i32 } => size 8. A dynamic outer index must emit
        // `outer * 8` at run time (no static folded offset).
        let src = r#"
%struct.S = type { i32, i32 }
define ptr @f(ptr %p, i64 %i) {
entry:
  %q = getelementptr inbounds %struct.S, ptr %p, i64 %i
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("dynamic struct GEP imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(8)
                }
            )),
            1,
            "stride constant sizeof(S)=8 must be materialised"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Mul, .. })),
            1,
            "outer index must be multiplied by the struct stride"
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::GEP {
                    pointee_ty: Ty::I8,
                    ..
                }
            )),
            1,
            "the byte offset feeds a single i8 GEP"
        );
        // A dynamic index is NOT a statically folded const->GEP offset.
        assert!(struct_gep_offsets(f).is_empty());
    }

    #[test]
    fn struct_gep_dynamic_outer_with_field_adds_field_offset() {
        // { i32, i32 }: field 1 at byte 4. Dynamic outer -> outer*8 + 4.
        let src = r#"
%struct.S = type { i32, i32 }
define ptr @f(ptr %p, i64 %i) {
entry:
  %q = getelementptr inbounds %struct.S, ptr %p, i64 %i, i32 1
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("dynamic struct GEP + field imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(8)
                }
            )),
            1,
            "struct stride 8 constant"
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(4)
                }
            )),
            1,
            "field-1 byte offset 4 constant"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Mul, .. })),
            1
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::BinOp { op: BinOp::Add, .. })),
            1
        );
    }

    #[test]
    fn struct_gep_dynamic_outer_on_global_base_materializes_stub() {
        // `%struct.C` is { double, double } => size 16, and the base is a module
        // global @z: materialise @z's offset-0 stub, then outer*16 at run time.
        let src = r#"
%struct.C = type { double, double }
@z = global %struct.C zeroinitializer, align 8
define ptr @f(i64 %i) {
entry:
  %q = getelementptr inbounds %struct.C, ptr @z, i64 %i
  ret ptr %q
}
"#;
        let m = import_text(src, "t").expect("dynamic struct GEP on global base imports");
        let f = func_named(&m, "f");
        let base_stub = (0xFADEu64 << 48) as i128;
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const { ty: Ty::Ptr, value: Constant::Int(v) } if *v == base_stub
            )),
            1,
            "@z base stub at offset 0 must be materialised"
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(16)
                }
            )),
            1,
            "struct stride sizeof(C)=16 constant"
        );
    }

    #[test]
    fn struct_gep_dynamic_field_index_still_fails_closed() {
        // Struct field indices are constants in valid LLVM; a dynamic field index
        // has no meaning and must stay unsupported.
        let src = r#"
%struct.S = type { i32, i32 }
define ptr @f(ptr %p, i64 %i, i32 %j) {
entry:
  %q = getelementptr inbounds %struct.S, ptr %p, i64 %i, i32 %j
  ret ptr %q
}
"#;
        assert!(matches!(import_text(src, "t"), Err(Error::Unsupported(_))));
    }

    // ---- Cluster 3: constant-expression GEP as a call argument -------------

    #[test]
    fn constexpr_gep_call_arg_folds_to_global_stub_plus_offset() {
        // `&arr[5]` for `[10 x i32] @arr` is +20 bytes on @arr's base stub.
        let src = r#"
@arr = global [10 x i32] zeroinitializer, align 4
declare void @use(ptr)
define void @f() {
entry:
  call void @use(ptr getelementptr inbounds ([10 x i32], ptr @arr, i64 0, i64 5))
  ret void
}
"#;
        let m = import_text(src, "t").expect("constexpr GEP call arg imports");
        let f = func_named(&m, "f");
        let base_stub = (0xFADEu64 << 48) as i128;
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const { ty: Ty::Ptr, value: Constant::Int(v) } if *v == base_stub
            )),
            1,
            "constexpr call-arg GEP must materialise @arr's base stub"
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(20)
                }
            )),
            1,
            "5 * sizeof(i32) = 20 byte offset"
        );
        assert_eq!(
            count_insts(f, |i| matches!(i, Inst::Call { .. })),
            1,
            "the folded pointer feeds the call"
        );
    }

    #[test]
    fn constexpr_gep_call_arg_byte_form_into_global() {
        // The clang byte form `getelementptr (i8, ptr @g, i64 16)` == @g + 16.
        let src = r#"
@g = global [64 x i8] zeroinitializer, align 1
declare void @use(ptr)
define void @f() {
entry:
  call void @use(ptr getelementptr inbounds (i8, ptr @g, i64 16))
  ret void
}
"#;
        let m = import_text(src, "t").expect("byte-form constexpr GEP call arg imports");
        let f = func_named(&m, "f");
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(16)
                }
            )),
            1,
            "byte offset 16 constant"
        );
        assert_eq!(
            count_insts(f, |i| matches!(
                i,
                Inst::GEP {
                    pointee_ty: Ty::I8,
                    ..
                }
            )),
            1
        );
    }

    #[test]
    fn constexpr_inttoptr_call_arg_stays_unsupported() {
        // Only the global-GEP const-expr is evaluable; other const-exprs as call
        // args (here `inttoptr`) must still fail closed.
        let src = r#"
declare void @use(ptr)
define void @f() {
entry:
  call void @use(ptr inttoptr (i64 4096 to ptr))
  ret void
}
"#;
        assert!(
            matches!(import_text(src, "t"), Err(Error::Unsupported(_))),
            "non-GEP const-expr call arg must be unsupported"
        );
    }

    // ---- Bool global initializer (unblocked ReedSolomon) -------------------

    #[test]
    fn bool_global_carries_a_bool_initializer_not_an_int() {
        // Codegen's global tree rejects an integer initializer on an i1 global;
        // the importer must emit `Constant::Bool`.
        let src = r#"
@inited = internal global i1 false, align 4
@ready = global i1 true, align 4
"#;
        let m = import_text(src, "t").expect("bool globals import");
        let init = |name: &str| {
            m.globals
                .iter()
                .find(|g| g.name == name)
                .and_then(|g| g.initializer.clone())
        };
        assert!(
            matches!(init("inited"), Some(Constant::Bool(false))),
            "i1 false global must carry Constant::Bool(false), got {:?}",
            init("inited")
        );
        assert!(
            matches!(init("ready"), Some(Constant::Bool(true))),
            "i1 true global must carry Constant::Bool(true), got {:?}",
            init("ready")
        );
    }

    // ---- closing-the-tail clusters ----------------------------------------

    /// Flatten every instruction of a named function (for structural asserts).
    fn all_insts(m: &Module, func: &str) -> Vec<Inst> {
        m.functions
            .iter()
            .find(|f| f.name == func)
            .map(|f| {
                f.blocks
                    .iter()
                    .flat_map(|b| b.body.iter().map(|n| n.inst.clone()))
                    .collect()
            })
            .unwrap_or_default()
    }

    // cluster 1: @llvm.experimental.memset.pattern -> libSystem memset_patternN

    #[test]
    fn memset_pattern_i32_lowers_to_memset_pattern4_call() {
        let src = r#"
@file = internal global [100 x i32] zeroinitializer, align 4
declare void @llvm.experimental.memset.pattern.p0.i32.i64(ptr, i32, i64, i1)
define void @f() {
entry:
  call void @llvm.experimental.memset.pattern.p0.i32.i64(ptr @file, i32 101, i64 100, i1 false)
  ret void
}
"#;
        let m = import_text(src, "t").expect("memset.pattern imports");
        let mp4 = m
            .functions
            .iter()
            .find(|f| f.name == "memset_pattern4")
            .expect("memset_pattern4 external declared")
            .id;
        let insts = all_insts(&m, "f");
        assert!(
            insts.iter().any(|i| matches!(i, Inst::Alloca { .. })),
            "pattern-value stack slot expected"
        );
        assert!(
            insts.iter().any(|i| matches!(i, Inst::Store { .. })),
            "store of the pattern value expected"
        );
        assert!(
            insts
                .iter()
                .any(|i| matches!(i, Inst::Call { callee, .. } if *callee == mp4)),
            "call to memset_pattern4 expected, insts={insts:?}"
        );
    }

    #[test]
    fn memset_pattern_unsupported_element_size_fails_closed() {
        // An i16 pattern is 2 bytes; libSystem has no `memset_pattern2`, so it
        // must fail closed rather than emit a wrong byte count.
        let src = r#"
@h = internal global [8 x i16] zeroinitializer, align 2
declare void @llvm.experimental.memset.pattern.p0.i16.i64(ptr, i16, i64, i1)
define void @f() {
entry:
  call void @llvm.experimental.memset.pattern.p0.i16.i64(ptr @h, i16 7, i64 8, i1 false)
  ret void
}
"#;
        match import_text(src, "t") {
            Err(Error::Unsupported(msg)) => assert!(
                msg.contains("memset.pattern") && msg.contains("4/8/16"),
                "unexpected reason: {msg}"
            ),
            other => panic!("2-byte memset.pattern should fail closed, got {other:?}"),
        }
    }

    // cluster 2: c-string scanner survives a `;`/`, !` inside the literal

    #[test]
    fn cstring_with_semicolon_and_equals_is_not_comment_truncated() {
        let src = r#"
@s = private unnamed_addr constant [30 x i8] c"Register too long; Max. = %d\0A\00", align 1
"#;
        let m = import_text(src, "t").expect("c-string with ; imports");
        let bytes = global_bytes(&m, "s");
        assert_eq!(bytes.len(), 30, "byte image length");
        assert_eq!(
            &bytes[..17],
            b"Register too long",
            "prefix survives the `;`"
        );
        assert_eq!(*bytes.last().unwrap(), 0, "NUL terminator preserved");
    }

    // cluster 3: address-of a function -> Constant::SymbolAddr

    #[test]
    fn address_of_function_materializes_symbol_addr() {
        let src = r#"
define signext i8 @toggle(ptr %p) {
entry:
  ret i8 0
}
define void @use(ptr %slot) {
entry:
  store ptr @toggle, ptr %slot, align 8
  ret void
}
"#;
        let m = import_text(src, "t").expect("address-of-function imports");
        let insts = all_insts(&m, "use");
        assert!(
            insts.iter().any(|i| matches!(
                i,
                Inst::Const { value: Constant::SymbolAddr { symbol, addend: 0 }, .. } if symbol == "toggle"
            )),
            "expected SymbolAddr(toggle) const, insts={insts:?}"
        );
    }

    #[test]
    fn address_of_undeclared_symbol_fails_closed() {
        let src = r#"
define void @use(ptr %slot) {
entry:
  store ptr @nonexistent, ptr %slot, align 8
  ret void
}
"#;
        match import_text(src, "t") {
            Err(Error::Unsupported(msg)) => assert!(
                msg.contains("address-of undeclared global") && msg.contains("nonexistent"),
                "unexpected reason: {msg}"
            ),
            other => panic!("undeclared symbol address should fail closed, got {other:?}"),
        }
    }

    // cluster 4: [N x ptr] pointer-table global -> SymbolAddr relocations

    #[test]
    fn pointer_array_global_forward_ref_lowers_to_symbol_addrs() {
        // @tab references @a/@b that are DEFINED LATER — resolved by the
        // symbol-name pre-scan; each element is a relocatable SymbolAddr.
        let src = r#"
@tab = internal constant [2 x ptr] [ptr @a, ptr @b], align 8
@a = private constant [2 x i8] c"x\00", align 1
@b = private constant [2 x i8] c"y\00", align 1
"#;
        let m = import_text(src, "t").expect("pointer array global imports");
        let init = m
            .globals
            .iter()
            .find(|g| g.name == "tab")
            .and_then(|g| g.initializer.clone());
        match init {
            Some(Constant::Aggregate(elems)) => {
                assert_eq!(elems.len(), 2, "two pointer slots");
                assert!(
                    matches!(&elems[0], Constant::SymbolAddr { symbol, addend: 0 } if symbol == "a")
                );
                assert!(
                    matches!(&elems[1], Constant::SymbolAddr { symbol, addend: 0 } if symbol == "b")
                );
            }
            other => panic!("expected SymbolAddr aggregate, got {other:?}"),
        }
    }

    #[test]
    fn pointer_array_global_null_element_is_zero_pointer_slot() {
        let src = r#"
@tab = internal constant [2 x ptr] [ptr @a, ptr null], align 8
@a = private constant [2 x i8] c"x\00", align 1
"#;
        let m = import_text(src, "t").expect("pointer array with null imports");
        let init = m
            .globals
            .iter()
            .find(|g| g.name == "tab")
            .and_then(|g| g.initializer.clone());
        match init {
            Some(Constant::Aggregate(elems)) => {
                // One SymbolAddr + eight zero bytes for the null pointer = 8 bytes.
                assert!(matches!(&elems[0], Constant::SymbolAddr { symbol, .. } if symbol == "a"));
                assert_eq!(elems.len(), 1 + 8, "SymbolAddr + 8 null bytes");
                assert!(elems[1..].iter().all(|c| matches!(c, Constant::Int(0))));
            }
            other => panic!("expected aggregate, got {other:?}"),
        }
    }

    /// A pointer-INDUCTION-VARIABLE loop starting inside a global array
    /// (`p = &g[k]; while (...) { ... p++; }`) makes clang emit the initial
    /// pointer as a CONST-EXPR GEP in the loop-header phi:
    ///
    ///   %p = phi ptr [ %next, %body ], [ getelementptr inbounds nuw (i8, ptr @g, i64 K), %entry ]
    ///
    /// `lookup_phi_operand` handled `%local` and bare `@g` but fell through to
    /// `parse_constant_operand` for this, which has no const-expr evaluator, so
    /// the WHOLE MODULE failed to import with "unknown operand token". Found on
    /// Stanford/Puzzle rewritten to pointer-IV form (2026-08-15).
    #[test]
    fn phi_incoming_may_be_a_constexpr_gep_on_a_global() {
        let src = r#"
@g = internal global [512 x i32] zeroinitializer, align 4

define i32 @f(i32 %n) {
entry:
  br label %loop

loop:
  %p = phi ptr [ %next, %loop ], [ getelementptr inbounds nuw (i8, ptr @g, i64 292), %entry ]
  %i = phi i32 [ %i1, %loop ], [ 0, %entry ]
  %v = load i32, ptr %p, align 4
  %next = getelementptr inbounds nuw i8, ptr %p, i64 4
  %i1 = add i32 %i, 1
  %c = icmp slt i32 %i1, %n
  br i1 %c, label %loop, label %out

out:
  ret i32 %v
}
"#;
        let m = import_text(src, "t").expect("const-expr GEP phi incoming must import");
        assert!(
            m.functions.iter().any(|f| f.name == "f"),
            "function f must be present"
        );
    }

    /// The same shape with a byte offset that is NOT a valid stub offset must
    /// still FAIL CLOSED rather than silently import a wrong address.
    #[test]
    fn phi_constexpr_gep_on_undeclared_global_fails_closed() {
        let src = r#"
define i32 @f() {
entry:
  br label %loop

loop:
  %p = phi ptr [ %p, %loop ], [ getelementptr inbounds nuw (i8, ptr @nope, i64 8), %entry ]
  %v = load i32, ptr %p, align 4
  br label %loop
}
"#;
        assert!(
            import_text(src, "t").is_err(),
            "const-expr GEP on an undeclared global must fail closed"
        );
    }

    #[test]
    fn pointer_array_global_undeclared_element_fails_closed() {
        let src = r#"
@tab = internal constant [1 x ptr] [ptr @missing], align 8
"#;
        match import_text(src, "t") {
            Err(Error::Unsupported(msg)) => assert!(
                msg.contains("undeclared symbol") && msg.contains("missing"),
                "unexpected reason: {msg}"
            ),
            other => panic!("undeclared pointer-array element should fail closed, got {other:?}"),
        }
    }

    // cluster 5: indirect call -> Inst::CallIndirect

    #[test]
    fn indirect_call_lowers_to_call_indirect() {
        let src = r#"
define i32 @caller(ptr %fp, i32 %x) {
entry:
  %r = call i32 %fp(i32 %x)
  ret i32 %r
}
"#;
        let m = import_text(src, "t").expect("indirect call imports");
        let insts = all_insts(&m, "caller");
        assert!(
            insts.iter().any(|i| matches!(i, Inst::CallIndirect { .. })),
            "expected CallIndirect, insts={insts:?}"
        );
    }

    #[test]
    fn indirect_variadic_call_fails_closed() {
        let src = r#"
define void @caller(ptr %fp, i32 %x) {
entry:
  call void (i32, ...) %fp(i32 %x)
  ret void
}
"#;
        match import_text(src, "t") {
            Err(Error::Unsupported(msg)) => {
                assert!(
                    msg.contains("indirect variadic call"),
                    "unexpected reason: {msg}"
                )
            }
            other => panic!("indirect variadic call should fail closed, got {other:?}"),
        }
    }

    // cluster 6: `zext i1 to i8` (Bool->I8) lowers end-to-end through the adapter

    #[test]
    fn zext_bool_to_i8_lowers_through_adapter() {
        let src = r#"
define i8 @f(i32 %a, i32 %b) {
entry:
  %c = icmp eq i32 %a, %b
  %z = zext i1 %c to i8
  ret i8 %z
}
"#;
        let m = import_text(src, "t").expect("zext i1 to i8 imports");
        let lowered = trust_cg_lower::translate_module(&m);
        assert!(
            lowered.is_ok(),
            "zext Bool->I8 must lower through the adapter, got {:?}",
            lowered.err()
        );
    }
}
