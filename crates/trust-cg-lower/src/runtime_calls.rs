// trust-cg-lower/runtime_calls.rs - Runtime symbols the backend names on its own
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The runtime routines and data the backend references, or interprets, BY
//! NAME on its own, without the source naming them.
//!
//! This is the one list those sites draw their names from:
//!
//! * the target-independent lowering (`frem`, the i128 <-> float
//!   conversions, heap allocation and deallocation, the Clean RC entries);
//! * the AArch64 instruction selector (memory intrinsics, i128 division,
//!   i128 -> float, `_Unwind_Resume`) and AArch64 frame lowering (the stack
//!   protector);
//! * the x86-64 instruction selector (memory intrinsics, i128 division,
//!   `_Unwind_Resume`);
//! * the machine passes of `trust-cg-opt`: the Darwin sin/cos merge emits
//!   `__sincos_stret`, SROA reads a `memcpy` call's semantics from its name
//!   and the vectorizer reads `calloc`'s.
//!
//! Every object writer and the JIT resolve such a name through the module's
//! own symbols first, so a definition of the module named like one would
//! receive the reference: [`backend_symbol_shadow`] finds it, and the
//! compiler refuses the module on every target and in the JIT. The RISC-V
//! selector names no runtime routine of its own.
//!
//! A module DECLARATION named like one keeps its own ABI facts for the
//! module's calls, but the AArch64 selector keys a callee's hidden return
//! buffer by name, which the backend's own call of the routine shares: it
//! refuses a hidden-buffer callee named like any listed symbol
//! (`InstructionSelector::direct_callee_passes_sret`, LD-100 rule 11).

use trust_ir::{Global, Linkage, Module};

use crate::adapter::{
    EH_PERSONALITY_CANDIDATES, eh_personality_for_function_names, eh_personality_override,
};
use crate::static_call_devirtualization::{
    is_module_local_data_definition, is_module_local_function_definition,
};

/// One runtime symbol the backend references by name on its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RuntimeSymbol {
    /// `memcpy`: aggregate copies and the memcpy intrinsic (AArch64 ISel).
    Memcpy,
    /// `memmove`: the memmove intrinsic (AArch64 ISel).
    Memmove,
    /// `memset`: fills and the memset intrinsic (AArch64 ISel).
    Memset,
    /// `fmod`: `frem` on `f64` (lowering).
    Fmod,
    /// `fmodf`: `frem` on `f32` and `f16` (lowering).
    Fmodf,
    /// `__fixsfti`: `f32`/`f16` -> `i128` (lowering).
    Fixsfti,
    /// `__fixdfti`: `f64` -> `i128` (lowering).
    Fixdfti,
    /// `__fixunssfti`: `f32`/`f16` -> `u128` (lowering).
    Fixunssfti,
    /// `__fixunsdfti`: `f64` -> `u128` (lowering).
    Fixunsdfti,
    /// `__floattisf`: `i128` -> `f32` (lowering and AArch64 ISel).
    Floattisf,
    /// `__floattidf`: `i128` -> `f64` (lowering and AArch64 ISel).
    Floattidf,
    /// `__floatuntisf`: `u128` -> `f32` (lowering and AArch64 ISel).
    Floatuntisf,
    /// `__floatuntidf`: `u128` -> `f64` (lowering and AArch64 ISel).
    Floatuntidf,
    /// `__divti3`: signed `i128` division (AArch64 ISel).
    Divti3,
    /// `__udivti3`: unsigned `i128` division (AArch64 ISel).
    Udivti3,
    /// `__modti3`: signed `i128` remainder (AArch64 ISel).
    Modti3,
    /// `__umodti3`: unsigned `i128` remainder (AArch64 ISel).
    Umodti3,
    /// `_Unwind_Resume`: `resume` after a cleanup pad (AArch64 ISel).
    UnwindResume,
    /// `__stack_chk_fail`: the stack protector's failure call (frame lowering).
    StackChkFail,
    /// `__stack_chk_guard`: the stack protector's canary (frame lowering).
    StackChkGuard,
    /// `malloc`: a C-origin heap allocation (lowering).
    Malloc,
    /// `free`: a C-origin heap deallocation (lowering).
    Free,
    /// `__rust_alloc`: a Rust-origin heap allocation (lowering).
    RustAlloc,
    /// `__rust_dealloc`: a Rust-origin heap deallocation (lowering).
    RustDealloc,
    /// `clean_inc`: Clean RC retain (lowering).
    CleanInc,
    /// `clean_dec`: Clean RC release (lowering).
    CleanDec,
    /// `clean_is_exclusive`: Clean RC uniqueness test (lowering).
    CleanIsExclusive,
    /// `__sincos_stret`: the Darwin sin/cos merge (`trust-cg-opt`) rewrites a
    /// same-argument `sin` + `cos` pair into one call of it.
    SincosStret,
    /// `calloc`: the vectorizer (`trust-cg-opt`) takes two distinct `calloc`
    /// results for non-aliasing fresh allocations.
    Calloc,
}

impl RuntimeSymbol {
    /// Every runtime symbol, each exactly once.
    pub const ALL: [Self; 29] = [
        Self::Memcpy,
        Self::Memmove,
        Self::Memset,
        Self::Fmod,
        Self::Fmodf,
        Self::Fixsfti,
        Self::Fixdfti,
        Self::Fixunssfti,
        Self::Fixunsdfti,
        Self::Floattisf,
        Self::Floattidf,
        Self::Floatuntisf,
        Self::Floatuntidf,
        Self::Divti3,
        Self::Udivti3,
        Self::Modti3,
        Self::Umodti3,
        Self::UnwindResume,
        Self::StackChkFail,
        Self::StackChkGuard,
        Self::Malloc,
        Self::Free,
        Self::RustAlloc,
        Self::RustDealloc,
        Self::CleanInc,
        Self::CleanDec,
        Self::CleanIsExclusive,
        Self::SincosStret,
        Self::Calloc,
    ];

    /// The symbol name as the object spells it (ELF; Mach-O adds one
    /// leading underscore).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Memcpy => "memcpy",
            Self::Memmove => "memmove",
            Self::Memset => "memset",
            Self::Fmod => "fmod",
            Self::Fmodf => "fmodf",
            Self::Fixsfti => "__fixsfti",
            Self::Fixdfti => "__fixdfti",
            Self::Fixunssfti => "__fixunssfti",
            Self::Fixunsdfti => "__fixunsdfti",
            Self::Floattisf => "__floattisf",
            Self::Floattidf => "__floattidf",
            Self::Floatuntisf => "__floatuntisf",
            Self::Floatuntidf => "__floatuntidf",
            Self::Divti3 => "__divti3",
            Self::Udivti3 => "__udivti3",
            Self::Modti3 => "__modti3",
            Self::Umodti3 => "__umodti3",
            Self::UnwindResume => "_Unwind_Resume",
            Self::StackChkFail => "__stack_chk_fail",
            Self::StackChkGuard => "__stack_chk_guard",
            Self::Malloc => "malloc",
            Self::Free => "free",
            Self::RustAlloc => "__rust_alloc",
            Self::RustDealloc => "__rust_dealloc",
            Self::CleanInc => "clean_inc",
            Self::CleanDec => "clean_dec",
            Self::CleanIsExclusive => "clean_is_exclusive",
            Self::SincosStret => "__sincos_stret",
            Self::Calloc => "calloc",
        }
    }

    /// Whether the symbol is data the backend loads (the stack protector's
    /// canary) rather than a routine it calls.
    #[must_use]
    pub const fn is_data(self) -> bool {
        matches!(self, Self::StackChkGuard)
    }

    /// The runtime symbol spelled `name`, if the backend references one.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|symbol| symbol.name() == name)
    }
}

/// Whether `global` is a data definition the object emits (not an import):
/// never an `available_externally` or `extern_weak` global; a module-local
/// one unless it is an initializer-less thread-local; any other one only
/// with an initializer. This agrees with the compiler's object-global mapping
/// (the codegen drift test pins that agreement).
#[must_use]
pub fn is_data_definition(global: &Global) -> bool {
    match global.linkage {
        Linkage::AvailableExternally | Linkage::ExternalWeak => false,
        Linkage::Internal | Linkage::Private => {
            global.initializer.is_some() || global.tls.is_none()
        }
        Linkage::External
        | Linkage::Weak
        | Linkage::LinkOnce
        | Linkage::WeakOdr
        | Linkage::LinkOnceOdr => global.initializer.is_some(),
    }
}

/// A definition of a module that a reference the backend makes by name on
/// its own would reach ([`backend_symbol_shadow`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackendSymbolShadow<'m> {
    /// A bodied Internal/Private function named like a listed symbol.
    ModuleLocalFunction {
        /// The function's name.
        name: &'m str,
        /// The listed symbol it is named like.
        symbol: RuntimeSymbol,
    },
    /// A data definition that a backend call or personality would reach.
    Data {
        /// The global's name.
        name: &'m str,
    },
}

/// The first definition of `module` that a reference the backend makes by
/// name on its own would reach, on any object path or in the JIT:
///
/// * a bodied Internal/Private function
///   ([`is_module_local_function_definition`]) named like any listed symbol:
///   the object resolves the backend's call to the local body (the module
///   inliner may even splice it in). An External definition of such a name
///   is the program's own routine, which the linker would pick for every
///   object anyway, and is not refused;
/// * Internal/Private data ([`is_module_local_data_definition`]) named like
///   any listed symbol, or like a personality some function of the module
///   selects: the module default its function names select
///   ([`eh_personality_for_function_names`]) or a function's own provenance
///   override ([`eh_personality_override`]);
/// * any other data DEFINITION ([`is_data_definition`]) named like a listed
///   ROUTINE or like either EH personality: every object of the program would
///   branch into it, or use it as the personality;
/// * any such data definition named like either personality's `DW.ref`
///   slot ([`is_eh_personality_slot_name`]): the AArch64 ELF unwind emitter,
///   GCC and LLVM name the weak hidden cell holding the personality's address
///   so, and the linker resolves every object's slot of that name (this
///   object's own included) to the one definition. GNU ld 2.42 and gold then
///   give the frames the module's word as the personality pointer, and a
///   throw through them dies with `SIGBUS`; LLD 22 resolves the module's
///   word to a slot instead, or refuses the link when another object's slot
///   group comes first. A module-local global of that name is a separate
///   `STB_LOCAL` symbol and is not reported.
///
/// A module-local FUNCTION named like the selected personality is not
/// reported: on AArch64 ELF it is the module's own personality, reached
/// through an object-local slot.
#[must_use]
pub fn backend_symbol_shadow(module: &Module) -> Option<BackendSymbolShadow<'_>> {
    if let Some((name, symbol)) = module
        .functions
        .iter()
        .filter(|function| is_module_local_function_definition(function))
        .find_map(|function| {
            RuntimeSymbol::from_name(&function.name).map(|symbol| (function.name.as_str(), symbol))
        })
    {
        return Some(BackendSymbolShadow::ModuleLocalFunction { name, symbol });
    }
    let mut selected_personalities = vec![eh_personality_for_function_names(
        module
            .functions
            .iter()
            .map(|function| function.name.as_str()),
    )];
    for personality in module.functions.iter().filter_map(eh_personality_override) {
        if !selected_personalities.contains(&personality) {
            selected_personalities.push(personality);
        }
    }
    module
        .globals
        .iter()
        .find(|global| {
            let listed = RuntimeSymbol::from_name(&global.name);
            if is_module_local_data_definition(global) {
                listed.is_some() || selected_personalities.contains(&global.name.as_str())
            } else {
                is_data_definition(global)
                    && (listed.is_some_and(|symbol| !symbol.is_data())
                        || EH_PERSONALITY_CANDIDATES.contains(&global.name.as_str())
                        || is_eh_personality_slot_name(&global.name))
            }
        })
        .map(|global| BackendSymbolShadow::Data {
            name: global.name.as_str(),
        })
}

/// Whether `name` is `DW.ref.<personality>` for either EH personality this
/// backend selects ([`EH_PERSONALITY_CANDIDATES`]): the name of the indirect
/// personality slot an ELF unwind table reaches the personality through.
#[must_use]
pub fn is_eh_personality_slot_name(name: &str) -> bool {
    name.strip_prefix("DW.ref.")
        .is_some_and(|personality| EH_PERSONALITY_CANDIDATES.contains(&personality))
}

#[cfg(test)]
mod tests {
    use super::{BackendSymbolShadow, RuntimeSymbol, backend_symbol_shadow};

    /// `ALL` lists each variant once and the names are distinct. The
    /// exhaustive `match` below stops compiling when a variant is added,
    /// which is the prompt to add it to `ALL` (and to this count).
    #[test]
    fn all_lists_every_runtime_symbol_once() {
        let mut seen = std::collections::BTreeSet::new();
        for symbol in RuntimeSymbol::ALL {
            let ordinal = match symbol {
                RuntimeSymbol::Memcpy
                | RuntimeSymbol::Memmove
                | RuntimeSymbol::Memset
                | RuntimeSymbol::Fmod
                | RuntimeSymbol::Fmodf
                | RuntimeSymbol::Fixsfti
                | RuntimeSymbol::Fixdfti
                | RuntimeSymbol::Fixunssfti
                | RuntimeSymbol::Fixunsdfti
                | RuntimeSymbol::Floattisf
                | RuntimeSymbol::Floattidf
                | RuntimeSymbol::Floatuntisf
                | RuntimeSymbol::Floatuntidf
                | RuntimeSymbol::Divti3
                | RuntimeSymbol::Udivti3
                | RuntimeSymbol::Modti3
                | RuntimeSymbol::Umodti3
                | RuntimeSymbol::UnwindResume
                | RuntimeSymbol::StackChkFail
                | RuntimeSymbol::StackChkGuard
                | RuntimeSymbol::Malloc
                | RuntimeSymbol::Free
                | RuntimeSymbol::RustAlloc
                | RuntimeSymbol::RustDealloc
                | RuntimeSymbol::CleanInc
                | RuntimeSymbol::CleanDec
                | RuntimeSymbol::CleanIsExclusive
                | RuntimeSymbol::SincosStret
                | RuntimeSymbol::Calloc => symbol,
            };
            assert!(seen.insert(ordinal), "{symbol:?} listed twice");
            assert_eq!(RuntimeSymbol::from_name(symbol.name()), Some(symbol));
        }
        let names: std::collections::BTreeSet<&str> =
            RuntimeSymbol::ALL.iter().map(|s| s.name()).collect();
        assert_eq!(names.len(), RuntimeSymbol::ALL.len());
        assert_eq!(RuntimeSymbol::ALL.len(), 29);
        let data: Vec<RuntimeSymbol> = RuntimeSymbol::ALL
            .into_iter()
            .filter(|symbol| symbol.is_data())
            .collect();
        assert_eq!(data, [RuntimeSymbol::StackChkGuard]);
        assert_eq!(RuntimeSymbol::from_name("printf"), None);
    }

    fn global(name: &str, linkage: trust_ir::Linkage, initialized: bool) -> trust_ir::Global {
        trust_ir::Global {
            name: name.into(),
            ty: trust_ir::Ty::I64,
            mutable: true,
            initializer: initialized.then_some(trust_ir::Constant::Int(42)),
            linkage,
            tls: None,
            align: Some(8),
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        }
    }

    fn function(name: &str, linkage: trust_ir::Linkage, bodied: bool) -> trust_ir::Function {
        let mut function = trust_ir::Function::new(
            trust_ir::FuncId::new(0),
            name,
            trust_ir::FuncTyId::new(0),
            trust_ir::BlockId::new(0),
        );
        function.linkage = linkage;
        if bodied {
            function.blocks.push(trust_ir::Block {
                id: trust_ir::BlockId::new(0),
                params: vec![],
                body: vec![trust_ir::InstrNode::new(trust_ir::Inst::Return {
                    values: vec![],
                })],
            });
        }
        function
    }

    /// The shadow finder over every listed name. Found: a module-local
    /// function of any listed name; module-local data of any listed name or
    /// of the selected personality; External, weak and ODR data definitions
    /// of a listed ROUTINE or of either personality. Not found: an External
    /// function definition (the program's own routine), a bodyless
    /// declaration, an import (`available_externally`, an initializer-less
    /// External global), External data `__stack_chk_guard` (a runtime's own
    /// canary), module-local data of the personality the module does not
    /// select, a module-local function named like the selected personality,
    /// and ordinary names.
    #[test]
    fn backend_symbol_shadow_finds_every_reaching_definition() {
        use trust_ir::Linkage;
        let with = |functions: Vec<trust_ir::Function>, globals: Vec<trust_ir::Global>| {
            let mut module = trust_ir::Module::new("shadow");
            module
                .add_func_type(trust_ir::FuncTy {
                    params: vec![],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            module.functions = functions;
            module.globals = globals;
            module
        };
        for symbol in RuntimeSymbol::ALL {
            let name = symbol.name();
            for linkage in [Linkage::Internal, Linkage::Private] {
                assert_eq!(
                    backend_symbol_shadow(&with(vec![function(name, linkage, true)], vec![])),
                    Some(BackendSymbolShadow::ModuleLocalFunction { name, symbol }),
                    "{linkage} fn {name}"
                );
                assert_eq!(
                    backend_symbol_shadow(&with(vec![], vec![global(name, linkage, true)])),
                    Some(BackendSymbolShadow::Data { name }),
                    "{linkage} data {name}"
                );
            }
            for linkage in [
                Linkage::External,
                Linkage::Weak,
                Linkage::LinkOnce,
                Linkage::WeakOdr,
                Linkage::LinkOnceOdr,
            ] {
                assert_eq!(
                    backend_symbol_shadow(&with(vec![], vec![global(name, linkage, true)])),
                    (!symbol.is_data()).then_some(BackendSymbolShadow::Data { name }),
                    "{linkage} data {name}"
                );
                assert_eq!(
                    backend_symbol_shadow(&with(vec![function(name, linkage, true)], vec![])),
                    None,
                    "{linkage} fn {name}"
                );
            }
            for (functions, globals) in [
                (vec![function(name, Linkage::External, false)], vec![]),
                (
                    vec![],
                    vec![global(name, Linkage::AvailableExternally, true)],
                ),
                (vec![], vec![global(name, Linkage::External, false)]),
            ] {
                assert_eq!(
                    backend_symbol_shadow(&with(functions, globals)),
                    None,
                    "{name}"
                );
            }
        }
        for personality in ["__gxx_personality_v0", "rust_eh_personality"] {
            for linkage in [Linkage::External, Linkage::Weak] {
                assert_eq!(
                    backend_symbol_shadow(&with(vec![], vec![global(personality, linkage, true)])),
                    Some(BackendSymbolShadow::Data { name: personality }),
                    "{linkage} data {personality}"
                );
            }
        }
        assert_eq!(
            backend_symbol_shadow(&with(
                vec![],
                vec![global("__gxx_personality_v0", Linkage::Internal, true)]
            )),
            Some(BackendSymbolShadow::Data {
                name: "__gxx_personality_v0"
            })
        );
        // A non-local definition named like either personality's `DW.ref`
        // slot collides with the slot; a module-local one, an import and an
        // unrelated `DW.ref.` name do not.
        for personality in ["__gxx_personality_v0", "rust_eh_personality"] {
            let slot = format!("DW.ref.{personality}");
            for linkage in [
                Linkage::External,
                Linkage::Weak,
                Linkage::LinkOnce,
                Linkage::WeakOdr,
                Linkage::LinkOnceOdr,
            ] {
                assert_eq!(
                    backend_symbol_shadow(&with(vec![], vec![global(&slot, linkage, true)])),
                    Some(BackendSymbolShadow::Data {
                        name: slot.as_str()
                    }),
                    "{linkage} data {slot}"
                );
            }
            for global in [
                global(&slot, Linkage::Internal, true),
                global(&slot, Linkage::Private, true),
                global(&slot, Linkage::External, false),
                global(&slot, Linkage::AvailableExternally, true),
            ] {
                assert_eq!(
                    backend_symbol_shadow(&with(vec![], vec![global.clone()])),
                    None,
                    "{} data {slot}",
                    global.linkage
                );
            }
        }
        assert!(!super::is_eh_personality_slot_name("DW.ref._ZTIi"));
        assert!(!super::is_eh_personality_slot_name("__gxx_personality_v0"));
        for (functions, globals) in [
            (
                vec![],
                vec![global("DW.ref.my_personality", Linkage::External, true)],
            ),
            (
                vec![],
                vec![global("rust_eh_personality", Linkage::Internal, true)],
            ),
            (
                vec![function("rust_eh_personality", Linkage::Internal, true)],
                vec![],
            ),
            (vec![function("printf", Linkage::Internal, true)], vec![]),
            (vec![], vec![global("printf", Linkage::External, true)]),
        ] {
            assert_eq!(backend_symbol_shadow(&with(functions, globals)), None);
        }
    }

    /// A `Producer::TRust` function selects `rust_eh_personality` whatever
    /// the module default (`eh_personality_override`), so module-local data
    /// of that name shadows the routine its frames unwind with and is found,
    /// although the module's function names select the C++ default. The same
    /// data beside only unstamped functions (or a function another frontend
    /// produced) is not found: no frame of that module runs the Rust
    /// personality. The C++ default stays covered beside the override.
    #[test]
    fn backend_symbol_shadow_covers_a_provenance_selected_personality() {
        use trust_ir::{Linkage, Producer};
        let module = |producer: Option<Producer>, local_data: &str| {
            let mut module = trust_ir::Module::new("shadow_override");
            module
                .add_func_type(trust_ir::FuncTy {
                    params: vec![],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut stamped = function("rust_frame", Linkage::External, true);
            stamped.producer = producer;
            module.functions = vec![stamped, function("cxx_frame", Linkage::External, true)];
            module.globals = vec![global(local_data, Linkage::Internal, true)];
            module
        };
        for linkage_name in ["rust_eh_personality", "__gxx_personality_v0"] {
            let with_override = module(Some(Producer::TRust), linkage_name);
            assert_eq!(
                backend_symbol_shadow(&with_override),
                Some(BackendSymbolShadow::Data { name: linkage_name }),
                "module-local `{linkage_name}` beside a TRust frame"
            );
        }
        for producer in [None, Some(Producer::Clean)] {
            assert_eq!(
                backend_symbol_shadow(&module(producer.clone(), "rust_eh_personality")),
                None,
                "{producer:?}: no frame of this module runs the Rust personality"
            );
        }
    }

    /// Drift, over every non-test file of `trust-cg-lower` (the shared test
    /// scanner walks the crate's module tree from `lib.rs`, so submodules
    /// such as `isel/branch_compare.rs` and `adapter_bounds_assert.rs` are
    /// read too, and code after a test module is not skipped):
    ///
    /// * no file but this list spells a listed name as a string literal
    ///   (with or without the Mach-O underscore): every emitting site names
    ///   a `RuntimeSymbol` variant;
    /// * no file builds a symbol operand from a literal or imports a symbol
    ///   variant by glob or list;
    /// * the selectors' call helpers take no literal callee, and their libcall
    ///   helpers take a `RuntimeSymbol`;
    /// * the adapter builds an ordinary `Interposable` call only in
    ///   `runtime_call_opcode` and the source direct-call binding
    ///   (`source_direct_call_binding`, which the direct `Call` and the
    ///   generic `Invoke` lowering share): 2 sites;
    /// * every file's symbol-operand uses (`::Symbol`, `::ExactModuleSymbol`,
    ///   whatever names the enum, `.as_symbol`, `.as_exact_module_symbol`)
    ///   are pinned per file. Only the two selectors have any: AArch64's are
    ///   the source callee (by name or exact), the source symbol and TLS
    ///   address forms, `_Unwind_Resume`, the two libcall helpers and the
    ///   operand-lowering match; x86-64's the same shapes on its own
    ///   operands. A use in any other file (the adapter, `va_list.rs`, ...)
    ///   fails until it is classified and pinned;
    /// * no non-test file splices source in with `include!` (the scanner
    ///   refuses it, since it does not read the included text).
    ///
    /// A new emitting site fails here until it is classified, and a new
    /// runtime routine must add a variant. (`trust-cg-opt` and AArch64 frame
    /// lowering are checked in their own crates, with the same scanner.)
    #[test]
    fn emitting_sites_draw_runtime_names_from_this_list() {
        use crate::source_scan::{Tok, crate_scans};
        let scans = crate_scans(&std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src"));
        let listed: std::collections::BTreeSet<String> = RuntimeSymbol::ALL
            .into_iter()
            .flat_map(|symbol| [symbol.name().to_string(), format!("_{}", symbol.name())])
            .collect();
        let mut mentions = std::collections::BTreeMap::new();
        let mut interposable = 0;
        for (file, scan) in &scans {
            if file != "runtime_calls.rs" {
                for literal in &scan.literals {
                    assert!(
                        !listed.contains(literal),
                        "{file} spells \"{literal}\" directly; name its RuntimeSymbol instead"
                    );
                }
            }
            assert_eq!(
                scan.literal_operands, 0,
                "{file} builds a symbol operand from a literal"
            );
            assert_eq!(
                scan.aliases, 0,
                "{file} imports a symbol variant by glob or list"
            );
            let tokens = &scan.tokens;
            for (at, token) in tokens.iter().enumerate() {
                let Tok::Ident(name) = token else {
                    continue;
                };
                // The callee argument of a selector call helper.
                let callee_argument = match name.as_str() {
                    "select_call"
                    | "select_call_with_arg_types"
                    | "select_call_with_arg_locations"
                    | "select_i128_div_libcall"
                    | "select_i128_to_float_libcall" => Some(0),
                    "select_memory_intrinsic_call" => Some(1),
                    _ => None,
                };
                if let Some(argument) = callee_argument
                    && tokens.get(at + 1) == Some(&Tok::Punct('('))
                {
                    let mut index = at + 2;
                    for _ in 0..argument {
                        while index < tokens.len() && tokens[index] != Tok::Punct(',') {
                            index += 1;
                        }
                        index += 1;
                    }
                    assert!(
                        !matches!(tokens.get(index), Some(Tok::Str(_))),
                        "{file} passes a string-literal callee to `{name}`"
                    );
                }
                if name == "DirectCallBinding"
                    && tokens.get(at + 1) == Some(&Tok::PathSep)
                    && tokens.get(at + 2) == Some(&Tok::Ident("Interposable".into()))
                    && (file == "adapter.rs" || file.starts_with("adapter"))
                {
                    interposable += 1;
                }
            }
            if scan.mentions != 0 {
                mentions.insert(file.as_str(), scan.mentions);
            }
        }
        assert_eq!(
            interposable, 2,
            "the adapter builds an ordinary by-name call outside `runtime_call_opcode` and the \
             source direct-call lowering; a backend runtime call must go through \
             `runtime_call_opcode(RuntimeSymbol::..)`"
        );
        assert_eq!(
            mentions,
            std::collections::BTreeMap::from(PINNED_SYMBOL_OPERAND_MENTIONS),
            "a file gained or lost a symbol-operand use; a runtime call must name a \
             `RuntimeSymbol` variant, and the pin and this test's doc move with it"
        );
    }

    /// Every non-test file's symbol-operand uses (files without any are
    /// absent; see [`emitting_sites_draw_runtime_names_from_this_list`]).
    const PINNED_SYMBOL_OPERAND_MENTIONS: [(&str, usize); 2] =
        [("isel.rs", 19), ("x86_64_isel.rs", 10)];
}
