//! Rustc's CGU-local function namespace, preserved across split object emission.
//!
//! A rustc CGU can become several TrustIR modules/objects (statics, batching
//! exclusions, or the legacy per-function path). Giving each definition IR
//! `Internal` linkage would prevent sibling objects from calling it. On
//! AArch64 Linux (ELF) and on Apple AArch64 and x86-64 (Mach-O), represent it
//! instead by a distinct CGU-qualified, hidden symbol. The symbol is strong within that CGU
//! and cannot be preempted or collide with another CGU's local copy. Never
//! substitute weak/link-once for local identity.
//!
//! The collision this prevents is not hypothetical: rustc instantiates an
//! `#[inline]` item (e.g. `<u64 as PartialOrd>::le`, `<i64 as From<i8>>::from`)
//! as a `LocalCopy` with `Internal` linkage in EVERY CGU that uses it, all
//! under the same mangled name. Emitted under that name as an ordinary global
//! definition, two CGUs' copies are two strong definitions of one symbol, and
//! the static link fails with `duplicate symbol` (measured on
//! aarch64-apple-darwin and x86_64-apple-darwin at `-Ccodegen-units=4`, O0 and
//! O1, before Mach-O used this namespace). The same holds across crates: an
//! rlib's copy and its downstream binary's copy meet in one link.
//!
//! The object formats differ in what they can spell ([`PrivateSymbolFormat`]):
//! ELF carries rustc's linkage and visibility for every function and a hidden
//! visibility on the undefined reference too; Mach-O spells hidden only on a
//! definition (`N_EXT | N_PEXT`), so a sibling object references the private
//! name by a plain undefined symbol, and the private name keeps rustc's symbol
//! as a readable suffix. Every non-`Internal` function keeps its name and gets
//! rustc's linkage and, on a definition, its visibility (ledger L06-P7: a
//! weak or link-once definition is `N_WEAK_DEF`, an `External` + hidden one
//! `N_PEXT`, as LLVM spells them, except that LLVM also marks a
//! `linkonce_odr` function automatically hidden, which this plan does not;
//! what the Mach-O adapter path cannot spell, such as a hidden weak
//! definition, is refused there by name).
//!
//! [`function_definition_linkage`] and [`static_definition_linkage`] are the
//! one map from rustc's mono-item linkage to the trust-ir linkage a definition
//! is emitted with: every rustc linkage is carried, emits no definition
//! (`available_externally`, as in LLVM) or is refused by name
//! ([`LINKAGE_REFUSAL`]), never collapsed onto another one.
use std::collections::{HashMap, HashSet};

use trust_ir::{Constant, Inst, Linkage, Module, Visibility};

pub(crate) const REFUSAL_PREFIX: &str = "function linkage refused: ";

/// The diagnostic code of a definition linkage this backend does not emit.
pub(crate) const LINKAGE_REFUSAL: &str = "[TCG-LINKAGE]";

/// rustc's mono-item linkage (`rustc_hir::attrs::Linkage`), mirrored so the
/// definition policy is unit-tested without rustc (`tests/function_linkage.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RustcLinkage {
    AvailableExternally,
    Common,
    ExternalWeak,
    External,
    Internal,
    LinkOnceAny,
    LinkOnceOdr,
    WeakAny,
    WeakOdr,
}

/// The rustc linkage forms carried 1:1 onto a trust-ir definition linkage.
/// Mach-O spells the weak and link-once forms `N_WEAK_DEF` (ld64 keeps one
/// definition; a strong one wins), ELF `STB_WEAK` (COMDAT for the ODR forms).
fn carried_definition_linkage(linkage: RustcLinkage) -> Option<Linkage> {
    Some(match linkage {
        RustcLinkage::External => Linkage::External,
        RustcLinkage::Internal => Linkage::Internal,
        RustcLinkage::LinkOnceAny => Linkage::LinkOnce,
        RustcLinkage::LinkOnceOdr => Linkage::LinkOnceOdr,
        RustcLinkage::WeakAny => Linkage::Weak,
        RustcLinkage::WeakOdr => Linkage::WeakOdr,
        RustcLinkage::AvailableExternally | RustcLinkage::Common | RustcLinkage::ExternalWeak => {
            return None;
        }
    })
}

/// Why a definition with `linkage` is refused (`None` when it is carried).
fn definition_linkage_refusal(linkage: RustcLinkage) -> Option<&'static str> {
    match linkage {
        RustcLinkage::AvailableExternally => Some(
            "`available_externally` marks an inline-only copy whose definition lives in another \
             object; this backend emits every body it lowers as a definition, so it would add a \
             second one",
        ),
        RustcLinkage::Common => Some(
            "`common` is a tentative zero-filled data definition the linker merges; no object \
             writer of this backend spells a common symbol",
        ),
        RustcLinkage::ExternalWeak => Some(
            "`extern_weak` is a weak declaration (null when no definition is linked), never a \
             definition",
        ),
        _ => None,
    }
}

/// The trust-ir linkage a FUNCTION definition with rustc `linkage` is emitted
/// with, `None` when no definition is emitted at all, or the named refusal.
/// `Internal` is further renamed to a hidden CGU-qualified symbol by
/// [`CguSymbols`]. An `available_externally` function is an inline-only copy
/// of a body another object defines: as in LLVM, no code is emitted for it,
/// and this crate's callers bind to the symbol.
pub(crate) fn function_definition_linkage(
    symbol: &str,
    linkage: RustcLinkage,
) -> Result<Option<Linkage>, String> {
    if linkage == RustcLinkage::AvailableExternally {
        return Ok(None);
    }
    carried_definition_linkage(linkage)
        .map(Some)
        .ok_or_else(|| {
            format!(
                "{LINKAGE_REFUSAL} function `{symbol}` has rustc linkage {linkage:?}: {}; refusing \
                 instead of emitting it with another linkage",
                definition_linkage_refusal(linkage).unwrap_or("unsupported")
            )
        })
}

/// The trust-ir linkage a STATIC definition with rustc `linkage` is emitted
/// with, before the static's own export policy (`compile_static_data_object`),
/// or the named refusal.
pub(crate) fn static_definition_linkage(
    symbol: &str,
    linkage: RustcLinkage,
) -> Result<Linkage, String> {
    carried_definition_linkage(linkage).ok_or_else(|| {
        format!(
            "{LINKAGE_REFUSAL} static `{symbol}` has rustc linkage {linkage:?}: {}; refusing \
             instead of emitting it with another linkage",
            definition_linkage_refusal(linkage).unwrap_or("unsupported")
        )
    })
}

/// Whether a definition with trust-ir `linkage` may be replaced, or merged
/// with another object's copy, at link time (the weak and link-once forms).
pub(crate) fn is_weak_definition(linkage: Linkage) -> bool {
    matches!(
        linkage,
        Linkage::Weak | Linkage::WeakOdr | Linkage::LinkOnce | Linkage::LinkOnceOdr
    )
}

/// The diagnostic code of a function visibility the session's function
/// emission cannot spell.
pub(crate) const VISIBILITY_REFUSAL: &str = "[TCG-VISIBILITY]";

/// How the session's function emission spells rustc's function symbol facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionSymbolRoute {
    /// A target with a CGU-private namespace ([`PrivateSymbolFormat::for_target`]):
    /// every function definition carries rustc's linkage and visibility as
    /// that format spells them.
    Private(PrivateSymbolFormat),
    /// The wasm32 object lane, which places rustc's function linkage through
    /// its own table (`wasm32_linkage`) and writes `WASM_SYM_VISIBILITY_HIDDEN`
    /// on a hidden definition or undefined symbol.
    Wasm32,
    /// Every other native target (x86-64 ELF and COFF): each function
    /// definition is emitted under rustc's name as a strong, default-visible
    /// global symbol, and no function visibility is written.
    Unspelled,
}

impl FunctionSymbolRoute {
    /// The route of a session targeting `arch` (rustc's `Arch::desc()`).
    pub(crate) fn for_target(arch: &str, is_linux: bool, is_like_darwin: bool) -> Self {
        if arch == "wasm32" {
            return Self::Wasm32;
        }
        PrivateSymbolFormat::for_target(arch, is_linux, is_like_darwin)
            .map_or(Self::Unspelled, Self::Private)
    }
}

/// Why a FUNCTION definition that rustc binds with `rustc_linkage` (carried as
/// trust-ir `linkage` by [`function_definition_linkage`]) and `visibility` is
/// refused on the [`FunctionSymbolRoute::Unspelled`] route of `triple`, or
/// `None` for the one form that route emits as rustc asked: a strong
/// (`External`), default-visible definition.
///
/// A weak or link-once definition would be emitted strong. A module-local
/// (`Internal`) definition, and a hidden or protected one, would be emitted as
/// a default-visible global: exported from any shared object its object is
/// linked into (a staticlib under a C link, for one) and preemptible there,
/// where rustc's LLVM backend keeps it out of the dynamic symbol table.
/// rustc binds most functions of an ordinary crate `Internal` (one codegen
/// unit) or hidden (an item another codegen unit calls), so on this route
/// almost every crate is refused (ruling OD-BRIDGE-UNSPELLED-BINDING-20261024).
pub(crate) fn unspelled_function_definition_refusal(
    triple: &str,
    symbol: &str,
    rustc_linkage: RustcLinkage,
    linkage: Linkage,
    visibility: Visibility,
) -> Option<String> {
    if is_weak_definition(linkage) {
        return Some(format!(
            "{LINKAGE_REFUSAL} function `{symbol}` has rustc linkage {rustc_linkage:?}, which \
             the {triple} function emission does not carry (every definition is strong); \
             refusing instead of emitting a strong symbol"
        ));
    }
    if linkage == Linkage::Internal {
        return Some(format!(
            "{LINKAGE_REFUSAL} function `{symbol}` has rustc linkage Internal (local to its \
             codegen unit), which the {triple} function emission does not carry: every \
             function definition there is a default-visible global symbol, so the body would \
             be exported from a shared object it is linked into and preemptible there; \
             refusing instead of exporting it (ruling OD-BRIDGE-UNSPELLED-BINDING-20261024)"
        ));
    }
    if visibility != Visibility::Default {
        return Some(format!(
            "{VISIBILITY_REFUSAL} function `{symbol}` has rustc visibility {visibility} \
             (linkage {rustc_linkage:?}), which the {triple} function emission does not carry: \
             every function definition there is default-visible, so it would be exported from \
             a shared object it is linked into and preemptible there; refusing instead of \
             exporting it (ruling OD-BRIDGE-UNSPELLED-BINDING-20261024)"
        ));
    }
    None
}

/// The visibility of a function DEFINITION the bridge synthesizes with no
/// rustc mono item behind it (the allocator shim's `__rust_*` wrappers and its
/// `__rust_no_alloc_shim_is_unstable_v2` marker, the C `main` entry):
/// `requested`, the session's default visibility, which rustc's LLVM backend
/// gives each of them (`create_wrapper_function`, `declare_entry_fn`).
///
/// The private-namespace and wasm32 routes carry it to the object writer,
/// which spells it or refuses it by name (Mach-O has no protected visibility).
/// The [`FunctionSymbolRoute::Unspelled`] route writes no function visibility,
/// so a hidden or protected request is refused here by name.
pub(crate) fn synthesized_definition_visibility(
    route: FunctionSymbolRoute,
    triple: &str,
    function: &str,
    requested: Visibility,
) -> Result<Visibility, String> {
    match route {
        FunctionSymbolRoute::Private(_) | FunctionSymbolRoute::Wasm32 => Ok(requested),
        FunctionSymbolRoute::Unspelled if requested == Visibility::Default => Ok(requested),
        FunctionSymbolRoute::Unspelled => Err(format!(
            "{VISIBILITY_REFUSAL} synthesized function `{function}`: the session's default \
             visibility is {requested} (`-Zdefault-visibility`), which rustc's LLVM backend \
             gives this function, and the {triple} function emission writes no function \
             visibility; refusing instead of emitting it default-visible \
             (ruling OD-BRIDGE-SYNTHESIZED-VISIBILITY-20261024)"
        )),
    }
}

/// The visibility of the allocator shim's DECLARATION of the `__rdl_*`
/// default-allocator function it forwards to. rustc's LLVM backend declares
/// it hidden on every target, so the reference must resolve inside the image
/// the shim is linked into and the callee is neither exported from a shared
/// object nor interposable there (an ELF undefined symbol's visibility binds
/// the definition: the most constraining one wins).
///
/// * ELF and wasm32: hidden, written on the undefined symbol.
/// * Mach-O: default. A Mach-O undefined symbol carries no visibility, so
///   LLVM's hidden declaration is written exactly as a default one.
/// * [`FunctionSymbolRoute::Unspelled`]: refused by name (no visibility is
///   written on an undefined function symbol there).
pub(crate) fn allocator_callee_declaration_visibility(
    route: FunctionSymbolRoute,
    triple: &str,
    callee: &str,
) -> Result<Visibility, String> {
    match route {
        FunctionSymbolRoute::Private(PrivateSymbolFormat::Elf) | FunctionSymbolRoute::Wasm32 => {
            Ok(Visibility::Hidden)
        }
        FunctionSymbolRoute::Private(PrivateSymbolFormat::MachO) => Ok(Visibility::Default),
        FunctionSymbolRoute::Unspelled => Err(format!(
            "{VISIBILITY_REFUSAL} the allocator shim's callee `{callee}` is a hidden declaration \
             in rustc's LLVM backend (it must bind inside the image the shim is linked into, \
             never be exported or interposed), and the {triple} function emission writes no \
             visibility on an undefined function symbol; refusing instead of declaring it \
             default-visible (ruling OD-BRIDGE-SYNTHESIZED-VISIBILITY-20261024)"
        )),
    }
}

/// How the target object format spells a CGU-private function symbol.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum PrivateSymbolFormat {
    /// ELF (AArch64 and x86-64 Linux): the private definition is `STB_GLOBAL` +
    /// `STV_HIDDEN`, a sibling object's reference to it is a hidden undefined
    /// symbol, and every other function is re-bound with rustc's own linkage
    /// and visibility.
    #[default]
    Elf,
    /// Mach-O (Apple AArch64 and x86-64): the private definition is `N_SECT |
    /// N_EXT | N_PEXT` (private extern: resolved across the objects of one static
    /// link, demoted to a local in the linked image). Mach-O has no visibility
    /// on an UNDEFINED symbol (LLVM drops a hidden declaration's visibility
    /// there too), so a sibling object's reference is a plain undefined
    /// symbol; the reserved CGU-qualified name, checked against every
    /// collected mono item ([`CguSymbols::check_collected_names`]), is what
    /// binds it to this CGU's definition. The name ends in rustc's own symbol
    /// (`__trust_cg_private.<cgu>.<index>.<symbol>`): the `<cgu>.<index>`
    /// prefix alone makes it unique (a rustc symbol never starts with a
    /// digit), and the suffix keeps the item readable to every tool that sees
    /// the linked image (disassemblers, profilers, backtraces), where every
    /// `Internal` function of a Darwin build would otherwise carry an opaque
    /// name. Every non-`Internal` function keeps the name the producer
    /// emitted it except its linkage and visibility: rustc's linkage, and on
    /// a definition rustc's visibility (`N_WEAK_DEF`, `N_PEXT`; ledger
    /// L06-P7). Mach-O has no visibility on a declaration.
    MachO,
}

impl PrivateSymbolFormat {
    /// The format whose CGU-private namespace a target with architecture
    /// `arch` (rustc's `Arch::desc()`) uses, given whether its OS is Linux or
    /// Darwin-like; `None` where no object path spells a hidden function
    /// definition, so every function keeps its rustc name there.
    ///
    /// * AArch64 Linux: [`Self::Elf`] (the AArch64 ELF module emitters spell
    ///   every v45 function fact).
    /// * x86-64 Linux: [`Self::Elf`] since ruling
    ///   OD-X86-BRIDGE-ELF-PRIVATE-ROUTE-20261106. That emitter spells a
    ///   definition's visibility and an undefined symbol's, which is what this
    ///   route's hidden definitions and hidden DECLARATIONS need; it spells no
    ///   function SECTION, so the adapter admits it through
    ///   `FunctionSymbolFactPolicy::AdmitElfSymbolVisibility` rather than the
    ///   wider `AdmitElfSymbolFacts`.
    /// * Apple AArch64 and x86-64: [`Self::MachO`] (both Mach-O module
    ///   emitters write a hidden `External` definition as `N_EXT | N_PEXT`,
    ///   trust-cg-codegen `aot_object_symbol_policy`).
    /// * Everything else, COFF and the remaining ELF targets (RISC-V Linux
    ///   among them) included: `None`. Those objects bind every function
    ///   definition global and admit no function visibility, so a rustc
    ///   `Internal` function in two CGUs there is still two global definitions
    ///   of one name.
    pub(crate) fn for_target(arch: &str, is_linux: bool, is_like_darwin: bool) -> Option<Self> {
        match arch {
            "aarch64" | "x86_64" if is_linux => Some(Self::Elf),
            "aarch64" | "x86_64" if is_like_darwin => Some(Self::MachO),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
struct Binding {
    emitted: String,
    linkage: Linkage,
    /// Visibility of a DEFINITION (a function with a body).
    visibility: Visibility,
    /// Visibility of a bodyless DECLARATION (a sibling object's reference).
    declaration_visibility: Visibility,
}

#[derive(Default)]
pub(crate) struct CguSymbols {
    enabled: bool,
    format: PrivateSymbolFormat,
    /// Functions whose emitted name, linkage or visibility is rewritten.
    functions: HashMap<String, Binding>,
    /// Every planned rustc function symbol, rewritten or not.
    planned: HashSet<String>,
    private_names: HashSet<String>,
}

impl CguSymbols {
    /// The ELF namespace (the tests' shorthand for
    /// `enabled_for(PrivateSymbolFormat::Elf)`).
    #[cfg(test)]
    pub(crate) fn enabled() -> Self {
        Self::enabled_for(PrivateSymbolFormat::Elf)
    }

    pub(crate) fn enabled_for(format: PrivateSymbolFormat) -> Self {
        Self {
            enabled: true,
            format,
            ..Self::default()
        }
    }

    pub(crate) fn insert(
        &mut self,
        cgu: &str,
        index: usize,
        symbol: String,
        linkage: Linkage,
        visibility: Visibility,
    ) -> Result<(), String> {
        self.enabled = true;
        if symbol.starts_with("__trust_cg_private.") {
            return Err(format!(
                "symbol `{symbol}` uses the reserved private function namespace"
            ));
        }
        let local = linkage == Linkage::Internal;
        let emitted = if local {
            if trust_cg_lower::EH_PERSONALITY_CANDIDATES.contains(&symbol.as_str()) {
                return Err(format!("cannot rename private EH personality `{symbol}`"));
            }
            match self.format {
                PrivateSymbolFormat::Elf => format!("__trust_cg_private.{cgu}.{index}"),
                PrivateSymbolFormat::MachO => format!("__trust_cg_private.{cgu}.{index}.{symbol}"),
            }
        } else {
            symbol.clone()
        };
        if local && !self.private_names.insert(emitted.clone()) {
            return Err(format!("duplicate private function name `{emitted}`"));
        }
        if !self.planned.insert(symbol.clone()) {
            return Err(format!(
                "duplicate rustc function symbol `{symbol}` in CGU `{cgu}`"
            ));
        }
        let binding = match (local, self.format) {
            (true, format) => Binding {
                emitted,
                linkage: Linkage::External,
                visibility: Visibility::Hidden,
                declaration_visibility: match format {
                    PrivateSymbolFormat::Elf => Visibility::Hidden,
                    PrivateSymbolFormat::MachO => Visibility::Default,
                },
            },
            (false, PrivateSymbolFormat::Elf) => Binding {
                emitted,
                linkage,
                visibility,
                declaration_visibility: visibility,
            },
            // Mach-O: a non-private function keeps its symbol and gets
            // rustc's linkage and definition visibility (L06-P7); a Mach-O
            // undefined symbol carries no visibility.
            (false, PrivateSymbolFormat::MachO) => Binding {
                emitted,
                linkage,
                visibility,
                declaration_visibility: Visibility::Default,
            },
        };
        self.functions.insert(symbol, binding);
        Ok(())
    }

    /// A generated private name must not alias any collected function/static,
    /// including a user-specified export name in a different CGU.
    pub(crate) fn check_collected_names(&self, names: &HashSet<String>) -> Result<(), String> {
        if let Some(name) = self.private_names.iter().find(|name| names.contains(*name)) {
            return Err(format!(
                "private function name `{name}` collides with a mono item"
            ));
        }
        Ok(())
    }

    pub(crate) fn emitted<'a>(&'a self, symbol: &'a str) -> &'a str {
        self.functions
            .get(symbol)
            .map_or(symbol, |binding| binding.emitted.as_str())
    }

    /// Run AFTER collecting canonical reachability edges and BEFORE object
    /// compilation/merging. FuncIds, instructions, signatures, and all data
    /// offsets are unchanged. Rewrite declarations as well as definitions and
    /// every SymbolAddr (including nested vtables and static initializers).
    pub(crate) fn apply(&self, module: &mut Module) -> Result<(), String> {
        self.apply_checked(module)
            .map_err(|err| format!("{REFUSAL_PREFIX}{err}"))
    }

    fn apply_checked(&self, module: &mut Module) -> Result<(), String> {
        if !self.enabled {
            return Ok(());
        }
        // Proofs/contracts can bind names or the module's exact content. The
        // bridge drains refinement obligations before this pass; machine proof
        // generation happens afterward. Refuse any opaque evidence in between.
        if !module.proof_obligations.is_empty()
            || !module.proof_certificates.is_empty()
            || !module.obligation_diagnostics.is_empty()
            || !module.spec_modules.is_empty()
            || !module.universes.is_empty()
            || !module.predicates.is_empty()
            || !module.imports.is_empty()
            || !module.global_asm.is_empty()
            || module.completeness.is_some()
            || module.functions.iter().any(|f| {
                !f.proofs.is_empty()
                    || f.summary.as_ref().is_some_and(|s| s != &Default::default())
                    || f.source_provenance.is_some()
                    || f.body_gate.is_some()
                    || f.blocks
                        .iter()
                        .flat_map(|b| &b.body)
                        .any(|n| n.proof_context.is_some())
            })
        {
            return Err("function linkage cannot rewrite a module carrying opaque proof or contract evidence".into());
        }
        for name in module
            .functions
            .iter()
            .map(|f| &f.name)
            .chain(module.globals.iter().map(|g| &g.name))
        {
            if name.starts_with("__trust_cg_private.") {
                return Err(format!(
                    "private function name `{name}` collides with an existing module symbol"
                ));
            }
        }
        // Check stored symbol operands too: an import expressed only as an
        // address must not accidentally resolve to our generated definition.
        let mut collision = None;
        visit_constants(module, |c| {
            if let Constant::SymbolAddr { symbol, .. } = c {
                if symbol.starts_with("__trust_cg_private.") {
                    collision = Some(symbol.clone());
                }
            }
        });
        if let Some(name) = collision {
            return Err(format!(
                "private function name `{name}` collides with an existing address operand"
            ));
        }
        // A data object is not a function, even if an upstream producer gave
        // it the same name. Do not silently retarget its address to a function.
        if let Some(global) = module
            .globals
            .iter()
            .find(|g| self.emitted(&g.name) != g.name)
        {
            return Err(format!(
                "private function `{}` collides with a data symbol",
                global.name
            ));
        }
        for function in &mut module.functions {
            if let Some(binding) = self.functions.get(&function.name) {
                function.name.clone_from(&binding.emitted);
                (function.linkage, function.visibility) = if function.blocks.is_empty() {
                    (Linkage::External, binding.declaration_visibility)
                } else {
                    (binding.linkage, binding.visibility)
                };
            }
            for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
                match &mut node.inst {
                    Inst::Const { value, .. } => self.rename_constant(value),
                    Inst::Switch { cases, .. } => {
                        for case in cases {
                            self.rename_constant(&mut case.value);
                        }
                    }
                    _ => {}
                }
            }
        }
        for global in &mut module.globals {
            if let Some(initializer) = &mut global.initializer {
                self.rename_constant(initializer);
            }
        }
        // Read independently through TrustIR's constant visitor to fail closed
        // if the writer ever misses a newly added constant storage location.
        let mut stale = None;
        visit_constants(module, |c| {
            if let Constant::SymbolAddr { symbol, .. } = c {
                if self.emitted(symbol) != symbol {
                    stale = Some(symbol.clone());
                }
            }
        });
        if let Some(name) = stale {
            return Err(format!("private function address `{name}` was not renamed"));
        }
        Ok(())
    }

    fn rename_constant(&self, constant: &mut Constant) {
        match constant {
            Constant::Ext(e) => e.unreachable(),
            Constant::SymbolAddr { symbol, .. } => {
                if let Some(binding) = self.functions.get(symbol) {
                    symbol.clone_from(&binding.emitted);
                }
            }
            Constant::Splat { elem, .. } => self.rename_constant(elem),
            Constant::Closure { captures, .. } => {
                for c in captures {
                    self.rename_constant(c);
                }
            }
            Constant::Aggregate(v)
            | Constant::Array(v)
            | Constant::Vector(v)
            | Constant::Sequence(v)
            | Constant::Set(v) => {
                for c in v {
                    self.rename_constant(c);
                }
            }
            Constant::Record(fields) => {
                for (_, c) in fields {
                    self.rename_constant(c);
                }
            }
            // Function identities are module-local IDs, not symbol spellings;
            // the function definition itself is renamed above. `FnItem` is
            // also nominal/ZST and never materializes an address here.
            Constant::FnDef(_)
            | Constant::FnItem(_)
            | Constant::Int(_)
            | Constant::U128(_)
            | Constant::Bytes { .. }
            | Constant::Float(_)
            | Constant::Bool(_)
            | Constant::PhantomData
            | Constant::Uninit
            // A tensor weight blob names its bytes by digest: no symbol.
            | Constant::TensorBlob { .. } => {}
        }
    }
}

fn visit_constants(module: &Module, mut visit: impl FnMut(&Constant)) {
    for f in &module.functions {
        for node in f.blocks.iter().flat_map(|b| &b.body) {
            match &node.inst {
                Inst::Const { value, .. } => value.visit_constants(&mut visit),
                Inst::Switch { cases, .. } => {
                    for case in cases {
                        case.value.visit_constants(&mut visit);
                    }
                }
                _ => {}
            }
        }
    }
    for global in &module.globals {
        if let Some(init) = &global.initializer {
            init.visit_constants(&mut visit);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repeated_constants_preserve_private_symbol_identity_and_addends() {
        let mut symbols = CguSymbols::enabled();
        symbols
            .insert(
                "cgu",
                7,
                "local_fn".into(),
                Linkage::Internal,
                Visibility::Default,
            )
            .unwrap();
        let mut value = Constant::Splat {
            elem: Box::new(Constant::Aggregate(vec![
                Constant::Splat {
                    elem: Box::new(Constant::SymbolAddr {
                        symbol: "local_fn".into(),
                        addend: 16,
                    }),
                    len: 3,
                },
                Constant::SymbolAddr {
                    symbol: "external_fn".into(),
                    addend: -8,
                },
            ])),
            len: 5,
        };
        symbols.rename_constant(&mut value);
        let mut addresses = Vec::new();
        value.visit_constants(&mut |constant: &Constant| {
            if let Constant::SymbolAddr { symbol, addend } = constant {
                addresses.push((symbol.clone(), *addend));
            }
        });
        assert_eq!(
            addresses,
            [
                ("__trust_cg_private.cgu.7".to_owned(), 16),
                ("external_fn".to_owned(), -8),
            ]
        );
        let Constant::Splat { elem, len: 5 } = value else {
            panic!("outer repeat changed")
        };
        let Constant::Aggregate(fields) = *elem else {
            panic!("aggregate changed")
        };
        assert!(matches!(fields[0], Constant::Splat { len: 3, .. }));
    }
}
