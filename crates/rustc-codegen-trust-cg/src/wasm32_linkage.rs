// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Give each wasm32 function definition the linkage rustc's partitioning
//! assigned its mono item.
//!
//! rustc places every function mono item in one or more codegen units with a
//! `MonoItemData { linkage, visibility, .. }`. A `LocalCopy` instance (an
//! `#[inline]` function, drop glue at `-O`, a small cross-crate-inlinable
//! body) is copied into EVERY CGU that reaches it with `Linkage::Internal`,
//! and an item used only inside its home CGU is internalized to
//! `Linkage::Internal` as well. The LLVM backend emits each such copy as a
//! file-local symbol of its CGU's object.
//!
//! The bridge's objects do not follow CGU boundaries: a CGU's functions are
//! batched into one object only when they merge, and otherwise compiled one
//! object per function, while statics (whose data may hold a function's
//! address) always get objects of their own. A file-local symbol would then be
//! unresolvable from the sibling objects that reference it. Every
//! `Linkage::Internal` definition is therefore emitted as a HIDDEN definition
//! under a CRATE-PRIVATE name instead: never exported from the linked module
//! and resolvable from every object of this crate. A symbol rustc placed in
//! several CGUs (a `LocalCopy`) is defined by several objects, so it is
//! `linkonce_odr`, coalesced by `wasm-ld` into one definition rather than
//! refused as a duplicate. A symbol placed in exactly ONE CGU is defined by
//! exactly one object, so it stays a strong (`External`) definition: the wasm
//! lane treats a weak or link-once definition as replaceable at link time
//! (`interposable_linkage`) — it copies by-address arguments passed to it and
//! derives no pointer-capture facts from its body, which pins every stack
//! array handed to it into its own frame bytes — while a strong definition's
//! body is the one every call reaches (a second strong definition of the
//! crate-private name would be a duplicate-symbol link error, never a silent
//! rebinding).
//!
//! Coalescing is sound only among the copies of ONE rustc session: they are
//! the same instance lowered from the same MIR under the same session flags.
//! rustc's symbol for a `LocalCopy` of an upstream function (`u32::pow`,
//! `i32::abs`, `u32::wrapping_add`) carries no instantiating crate, so every
//! crate that copies it uses the same name, yet the copies are NOT equivalent:
//! `#[rustc_inherit_overflow_checks]` and `ub_checks` take the value of the
//! session that codegens the copy. The crate-private name
//! ([`crate_private_symbol`]: rustc's symbol plus this crate's
//! `StableCrateId`) is identical across this crate's CGUs and distinct from
//! every other crate's in the link, and every definition, declaration and
//! `SymbolAddr` reference of the symbol in every object of this crate is
//! renamed to it. No `Internal` symbol is ever referenced from another crate
//! (rustc exports only `External` mono items), so a reference the rename
//! missed is unresolved at link, never bound to another crate's copy. The one
//! observable difference from per-CGU private copies is that two CGUs'
//! function pointers to the instance compare equal, which Rust leaves
//! unspecified.
//!
//! An explicit `#[linkage]` keeps its binding (`weak`/`linkonce` and their ODR
//! forms are weak wasm definitions under rustc's symbol, which its author
//! chose to share); a linkage with no wasm definition spelling
//! (`available_externally`, `common`, `extern_weak`) is refused by name. So is
//! a symbol rustc placed with two different linkages, which partitioning never
//! does: there is no single definition that honours both.
//!
//! Only DEFINITIONS the bridge left at the default `External` linkage get
//! rustc's linkage; declarations bind by name and keep their import form.
//!
//! Native sessions use the same table for the CGU-private copies the native
//! objects would otherwise define as a strong symbol some other object also
//! defines ([`Wasm32FnLinkage::record_native_copies`]): a copy rustc placed in
//! several codegen units of this crate, and a copy whose symbol names no
//! instantiating crate, which every other crate that copies the instance
//! defines under the same name. Both lanes take their never-inline set from
//! the table too ([`Wasm32FnLinkage::record_never_inline`]): every function
//! rustc marked `#[inline(never)]` or `#[cold]`, under the name its objects
//! define it by (its codegen unit's name for it, then the table's own
//! rename).

use std::collections::{BTreeSet, HashMap};

use crate::compiler_attributes::Linkage as RustcLinkage;
use crate::function_linkage::CguSymbols;
use rustc_middle::mono::Visibility as RustcVisibility;
use trust_ir::{Constant, Inst, Linkage, Module, Visibility};

/// The wasm32 symbol attributes of one function DEFINITION placed by rustc
/// with `linkage` and `visibility`, or the refusal for a linkage a wasm
/// object cannot define.
pub(crate) fn definition_linkage(
    linkage: RustcLinkage,
    visibility: RustcVisibility,
) -> Result<(Linkage, Visibility), String> {
    let visibility = crate::trust_ir_visibility(visibility);
    match linkage {
        RustcLinkage::External => Ok((Linkage::External, visibility)),
        // A CGU-private copy, renamed crate-private; see the module docs for
        // why it is not local.
        RustcLinkage::Internal => Ok((Linkage::LinkOnceOdr, Visibility::Hidden)),
        RustcLinkage::LinkOnceODR => Ok((Linkage::LinkOnceOdr, visibility)),
        RustcLinkage::WeakODR => Ok((Linkage::WeakOdr, visibility)),
        RustcLinkage::LinkOnceAny => Ok((Linkage::LinkOnce, visibility)),
        RustcLinkage::WeakAny => Ok((Linkage::Weak, visibility)),
        #[cfg(rustc_linkage_common)]
        RustcLinkage::Common => Err(unsupported_definition_linkage(linkage)),
        RustcLinkage::AvailableExternally | RustcLinkage::ExternalWeak => {
            Err(unsupported_definition_linkage(linkage))
        }
    }
}

fn unsupported_definition_linkage(linkage: RustcLinkage) -> String {
    format!(
        "[TCG-WASM32-LINKAGE] rustc placed this function with linkage {linkage:?}, \
         which has no wasm32 object definition form; refusing rather than emit it \
         with a different linker binding"
    )
}

/// The name every object of the crate identified by `crate_tag` (its
/// `StableCrateId`) defines and references a CGU-private `symbol` under:
/// the same in all of that crate's CGUs, distinct from every other crate's.
pub(crate) fn crate_private_symbol(symbol: &str, crate_tag: u64) -> String {
    format!("{symbol}.tcg.crate.{crate_tag:016x}")
}

/// How one placed function symbol is emitted in every object of the crate.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Placement {
    linkage: Linkage,
    visibility: Visibility,
    /// The crate-private name of a CGU-private (`Internal`) symbol; `None`
    /// keeps rustc's symbol.
    rename: Option<String>,
}

/// rustc's placement verdict for every function symbol of a wasm32 session.
#[derive(Debug, Default)]
pub(crate) struct Wasm32FnLinkage {
    /// The local crate's `StableCrateId`, which makes CGU-private names
    /// crate-private.
    crate_tag: u64,
    by_symbol: HashMap<String, Result<Placement, String>>,
    /// The functions marked `#[inline(never)]` or `#[cold]`, by the names
    /// their codegen units' modules give them before [`Self::apply`]
    /// ([`CguSymbols::emitted`]): every lane's inline-hint side table
    /// (trust-ir has no inline-hint field).
    never_inline: BTreeSet<String>,
}

impl Wasm32FnLinkage {
    /// An empty table for the crate whose `StableCrateId` is `crate_tag`.
    pub(crate) fn new(crate_tag: u64) -> Self {
        Self {
            crate_tag,
            by_symbol: HashMap::new(),
            never_inline: BTreeSet::new(),
        }
    }

    /// Record that the function rustc names `symbol`, placed in the codegen
    /// unit whose function names `cgu` plans, is `#[inline(never)]` or
    /// `#[cold]`: no lane's inliner splices its body into a caller.
    ///
    /// It is recorded under the name that unit's module gives it when the
    /// function is lowered ([`CguSymbols::emitted`]: on Mach-O and AArch64
    /// ELF an `Internal` function's CGU-private name, rustc's symbol
    /// elsewhere), the name [`Self::apply`] then looks up. Recorded under
    /// rustc's symbol, a renamed function would match no module function
    /// and keep no call.
    pub(crate) fn record_never_inline(&mut self, cgu: &CguSymbols, symbol: &str) {
        self.never_inline.insert(cgu.emitted(symbol).to_owned());
    }

    /// Every `#[inline(never)]` or `#[cold]` function under the name its
    /// objects define it by (the crate-private name of a CGU-private symbol,
    /// [`Self::apply`]).
    fn never_inline_names(&self) -> impl Iterator<Item = &str> {
        self.never_inline
            .iter()
            .map(|symbol| self.renamed(symbol).unwrap_or(symbol))
    }

    /// The wasm lane's inline hints: every `#[inline(never)]` or `#[cold]`
    /// function under the name its objects define it by.
    pub(crate) fn inline_hints(&self) -> trust_cg_codegen::wasm::WasmInlineHints {
        trust_cg_codegen::wasm::WasmInlineHints {
            never_inline: self.never_inline_names().map(str::to_owned).collect(),
            ..Default::default()
        }
    }

    /// A native module's never-inline set (`CompilerConfig::never_inline`):
    /// the `#[inline(never)]` and `#[cold]` functions `module` holds a body
    /// of, by the names [`Self::apply`] gave them. The native inliner
    /// (OPT-4) splices only bodies the module holds (the bridge passes no
    /// inline-only dependency), so a name it does not hold could change
    /// nothing; leaving it out keeps the module's compile policy and cache
    /// identity independent of the rest of the crate. Call after
    /// [`Self::apply`].
    pub(crate) fn never_inline_defined_in(&self, module: &Module) -> BTreeSet<String> {
        let marked: BTreeSet<&str> = self.never_inline_names().collect();
        module
            .functions
            .iter()
            .filter(|func| !func.blocks.is_empty() && marked.contains(func.name.as_str()))
            .map(|func| func.name.clone())
            .collect()
    }

    /// Record one placement of `symbol` in one codegen unit. A CGU-private
    /// symbol is a strong definition until a second placement makes it
    /// `linkonce_odr` (module docs); any other later placement that maps to
    /// different attributes turns the symbol's verdict into a refusal.
    pub(crate) fn record(
        &mut self,
        symbol: &str,
        linkage: RustcLinkage,
        visibility: RustcVisibility,
    ) {
        let internal = linkage == RustcLinkage::Internal;
        let placed =
            definition_linkage(linkage, visibility).map(|(wasm_linkage, visibility)| Placement {
                linkage: wasm_linkage,
                visibility,
                rename: internal.then(|| crate_private_symbol(symbol, self.crate_tag)),
            });
        // A CGU-private symbol's first placement is its only copy so far: one
        // strong definition (module docs). A second copy makes it the
        // coalesced `linkonce_odr` form `definition_linkage` gives it.
        let single_copy = |placed: &Result<Placement, String>| {
            placed.clone().map(|p| Placement {
                linkage: Linkage::External,
                ..p
            })
        };
        match self.by_symbol.get_mut(symbol) {
            None => {
                let first = if internal {
                    single_copy(&placed)
                } else {
                    placed
                };
                self.by_symbol.insert(symbol.to_owned(), first);
            }
            Some(existing) => {
                if internal && existing.is_ok() && *existing == single_copy(&placed) {
                    *existing = placed;
                } else if existing.is_ok() && *existing != placed {
                    *existing = Err(format!(
                        "[TCG-WASM32-LINKAGE] rustc placed `{symbol}` in several codegen \
                         units with different attributes ({existing:?} and {placed:?}); no \
                         single wasm32 definition honours both"
                    ));
                }
            }
        }
    }

    /// Record, for a NATIVE session, the function symbols rustc placed
    /// CGU-private (`Linkage::Internal`) in every placement that some other
    /// object would also define. `placements` holds `(symbol, linkage,
    /// visibility, names_no_crate)`, where `names_no_crate` says the symbol
    /// carries no instantiating crate (a non-generic `LocalCopy` of an upstream
    /// function: `str::as_ptr`, `u32::pow`), so every crate that copies the
    /// instance uses the same name. The native bridge emits each lowered
    /// definition as a strong external symbol, so without this two objects
    /// define the same name: a copy placed in several CGUs of this crate, or a
    /// crate-agnostic copy this crate and another both place (a duplicate
    /// symbol, or, where the linker keeps one, a binding to another session's
    /// copy compiled under different `overflow-checks` / `ub_checks`). Each
    /// such symbol takes the crate-private name the wasm32 table gives it (see
    /// the module docs for why that is sound): `linkonce_odr` when several
    /// CGUs define it, which the AArch64 and x86-64 Mach-O and ELF writers
    /// bind weak (`N_WEAK_DEF` / `STB_WEAK`) so the static linker keeps one,
    /// and the bridge's strong `External` when exactly one object of this
    /// crate does. Their visibility stays default: only the AArch64 ELF
    /// adapter entry admits a hidden function definition (every Mach-O and
    /// x86-64 entry refuses one), and the crate-private name already keeps
    /// every other crate's copy apart. Any other symbol — placed once and
    /// naming this crate (a local item, a generic instantiated here) — keeps
    /// the bridge's own linkage and name.
    pub(crate) fn record_native_copies(
        &mut self,
        placements: &[(&str, RustcLinkage, RustcVisibility, bool)],
    ) {
        let mut count: HashMap<&str, (usize, bool, bool)> = HashMap::new();
        for &(symbol, linkage, _, names_no_crate) in placements {
            let entry = count.entry(symbol).or_insert((0, true, false));
            entry.0 += 1;
            entry.1 &= linkage == RustcLinkage::Internal;
            entry.2 |= names_no_crate;
        }
        for (symbol, (copies, all_internal, names_no_crate)) in count {
            if all_internal && (copies > 1 || names_no_crate) {
                self.by_symbol.insert(
                    symbol.to_owned(),
                    Ok(Placement {
                        linkage: if copies > 1 {
                            Linkage::LinkOnceOdr
                        } else {
                            Linkage::External
                        },
                        visibility: Visibility::Default,
                        rename: Some(crate_private_symbol(symbol, self.crate_tag)),
                    }),
                );
            }
        }
    }

    /// The crate-private name of `symbol`, when rustc placed it CGU-private.
    fn renamed(&self, symbol: &str) -> Option<&str> {
        match self.by_symbol.get(symbol) {
            Some(Ok(Placement {
                rename: Some(name), ..
            })) => Some(name),
            _ => None,
        }
    }

    /// Give every function DEFINITION of `module` that rustc placed the
    /// linkage and visibility of its placement, and move every definition,
    /// declaration and `SymbolAddr` reference of a CGU-private symbol to its
    /// crate-private name.
    ///
    /// A DECLARATION of a CGU-private symbol placed as one strong hidden
    /// definition takes that definition's hidden visibility, so every object
    /// of the crate sees the symbol with the same name, linkage and
    /// visibility: the wasm lane decides from exactly those (and the
    /// signature) whether direct calls to it use its internal-ABI entry, and
    /// a caller and the callee's own object must decide alike. Native
    /// placements are never hidden, so native declarations are unchanged.
    pub(crate) fn apply(&self, module: &mut Module) -> Result<(), String> {
        for func in &mut module.functions {
            let Some(placed) = self.by_symbol.get(&func.name) else {
                continue;
            };
            let is_definition =
                !func.blocks.is_empty() && func.linkage != Linkage::AvailableExternally;
            if is_definition {
                let placement = placed
                    .clone()
                    .map_err(|err| format!("`{}`: {err}", func.name))?;
                if func.linkage != Linkage::External {
                    return Err(format!(
                        "[TCG-WASM32-LINKAGE] `{}`: the bridge gave this mono item's \
                         definition linkage {:?}, and rustc placed it as {:?}; refusing \
                         rather than pick one",
                        func.name, func.linkage, placement.linkage
                    ));
                }
                func.linkage = placement.linkage;
                func.visibility = placement.visibility;
            } else if func.linkage == Linkage::External
                && matches!(
                    placed,
                    Ok(Placement {
                        linkage: Linkage::External,
                        visibility: Visibility::Hidden,
                        rename: Some(_),
                    })
                )
            {
                func.visibility = Visibility::Hidden;
            }
            // A refused symbol keeps its name: its definition refuses the
            // crate, and a reference left behind is unresolved at link.
            if let Some(name) = self.renamed(&func.name) {
                func.name = name.to_owned();
            }
        }
        for global in &mut module.globals {
            if let Some(initializer) = &mut global.initializer {
                self.rename_references(initializer);
            }
        }
        for func in &mut module.functions {
            for block in &mut func.blocks {
                for node in &mut block.body {
                    match &mut node.inst {
                        Inst::Const { value, .. } => self.rename_references(value),
                        Inst::Switch { cases, .. } => {
                            for case in cases {
                                self.rename_references(&mut case.value);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        Ok(())
    }

    /// Move every `SymbolAddr` inside `constant` that names a CGU-private
    /// symbol to its crate-private name. The walk keeps its own stack, as
    /// trust-ir's constant visitors do, so nesting depth never meets the
    /// thread's stack.
    fn rename_references(&self, constant: &mut Constant) {
        let mut pending = vec![constant];
        while let Some(constant) = pending.pop() {
            match constant {
                Constant::Ext(e) => e.unreachable(),
                Constant::SymbolAddr { symbol, .. } => {
                    if let Some(name) = self.renamed(symbol) {
                        *symbol = name.to_owned();
                    }
                }
                Constant::Aggregate(items)
                | Constant::Array(items)
                | Constant::Vector(items)
                | Constant::Sequence(items)
                | Constant::Set(items)
                | Constant::Closure {
                    captures: items, ..
                } => pending.extend(items.iter_mut()),
                Constant::Record(fields) => pending.extend(fields.iter_mut().map(|(_, item)| item)),
                // A splat holds its one element once; renaming it renames every
                // lane.
                Constant::Splat { elem, .. } => pending.push(elem.as_mut()),
                // No symbol reference: a `FnDef` names its function by id, and
                // the function itself is renamed in `apply`.
                Constant::Int(_)
                | Constant::U128(_)
                | Constant::Bytes { .. }
                | Constant::Float(_)
                | Constant::Bool(_)
                | Constant::FnDef(_)
                | Constant::PhantomData
                | Constant::Uninit
                // A tensor weight blob names its bytes by digest: no symbol.
                | Constant::TensorBlob { .. } => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Global, InstrNode, Ty};

    const CRATE: u64 = 0x0123_4567_89ab_cdef;

    fn module(text: &str) -> Module {
        trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("parse: {e}\n{text}"))
    }

    const MODULE: &str = "module \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
        functy.0 = (i32) -> (i32)\n\n\
        fn @callee(functy.0) {\n}\n\n\
        fn @local_copy(functy.0) {\n\
        bb0(%1: i32):\n\
        \x20   %2 = call @func.0(%1)\n\
        \x20   ret %2\n\
        }\n\n\
        fn @shared(functy.0) {\n\
        bb0(%1: i32):\n\
        \x20   ret %1\n\
        }\n\n\
        fn @helper(functy.0) {\n\
        bb0(%1: i32):\n\
        \x20   ret %1\n\
        }\n";

    fn func<'m>(module: &'m Module, name: &str) -> &'m trust_ir::Function {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .expect(name)
    }

    /// A pointer-sized data global holding `&symbol`.
    fn address_global(name: &str, symbol: &str) -> Global {
        Global {
            name: name.to_owned(),
            ty: Ty::Tuple(vec![Ty::Ptr, Ty::Ptr]),
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::symbol_addr(symbol),
                Constant::symbol_addr("shared"),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        }
    }

    #[test]
    fn internal_copy_is_a_hidden_linkonce_odr_definition() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        // One `LocalCopy` in two CGUs, a hidden cross-CGU item, and a
        // declaration rustc also placed: only the two definitions get rustc's
        // linkage.
        placed.record(
            "local_copy",
            RustcLinkage::Internal,
            RustcVisibility::Default,
        );
        placed.record(
            "local_copy",
            RustcLinkage::Internal,
            RustcVisibility::Default,
        );
        placed.record("shared", RustcLinkage::External, RustcVisibility::Hidden);
        placed.record("callee", RustcLinkage::Internal, RustcVisibility::Default);
        let mut m = module(MODULE);
        placed.apply(&mut m).unwrap();
        let local = func(&m, &crate_private_symbol("local_copy", CRATE));
        assert_eq!(
            (local.linkage, local.visibility),
            (Linkage::LinkOnceOdr, Visibility::Hidden)
        );
        let shared = func(&m, "shared");
        assert_eq!(
            (shared.linkage, shared.visibility),
            (Linkage::External, Visibility::Hidden)
        );
        let callee = func(&m, &crate_private_symbol("callee", CRATE));
        assert!(callee.blocks.is_empty(), "callee is a declaration");
        // A declaration of a single strong crate-private definition carries
        // that definition's hidden visibility.
        assert_eq!(
            (callee.linkage, callee.visibility),
            (Linkage::External, Visibility::Hidden)
        );
        // Not a mono item (a bridge-synthesized function): untouched.
        let helper = func(&m, "helper");
        assert_eq!(
            (helper.linkage, helper.visibility),
            (Linkage::External, Visibility::Default)
        );
    }

    #[test]
    fn never_inline_hints_name_the_symbols_objects_define() {
        // An `#[inline(never)]` item rustc placed CGU-private is named by its
        // crate-private symbol, any other by rustc's own.
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record(
            "local_copy",
            RustcLinkage::Internal,
            RustcVisibility::Default,
        );
        placed.record("shared", RustcLinkage::External, RustcVisibility::Hidden);
        placed.record("plain", RustcLinkage::External, RustcVisibility::Default);
        // A wasm32 session plans no CGU-private names: rustc's symbols.
        let unplanned = CguSymbols::default();
        placed.record_never_inline(&unplanned, "local_copy");
        placed.record_never_inline(&unplanned, "shared");
        let hints = placed.inline_hints();
        assert_eq!(
            hints.never_inline.into_iter().collect::<Vec<_>>(),
            vec![
                crate_private_symbol("local_copy", CRATE),
                "shared".to_string()
            ]
        );
    }

    #[test]
    fn native_never_inline_set_names_the_bodies_the_module_holds() {
        // A native table: `local_copy` is a CGU-private copy placed in two
        // CGUs (renamed), `shared` keeps rustc's symbol, `callee` (also
        // renamed) is only DECLARED by this module, and `absent` is a marked
        // function the module does not mention.
        let mut placed = Wasm32FnLinkage::new(CRATE);
        let copy = (
            "local_copy",
            RustcLinkage::Internal,
            RustcVisibility::Default,
            false,
        );
        let callee = (
            "callee",
            RustcLinkage::Internal,
            RustcVisibility::Default,
            false,
        );
        placed.record_native_copies(&[copy, copy, callee, callee]);
        // No CGU-private names (x86-64 ELF): every function keeps rustc's.
        let unplanned = CguSymbols::default();
        for symbol in ["local_copy", "shared", "callee", "absent"] {
            placed.record_never_inline(&unplanned, symbol);
        }
        let mut m = module(MODULE);
        placed.apply(&mut m).unwrap();
        // Bodies only, under the names the object defines; `helper` is not
        // marked and stays out.
        assert_eq!(
            placed
                .never_inline_defined_in(&m)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![
                crate_private_symbol("local_copy", CRATE),
                "shared".to_string()
            ]
        );
        // Nothing marked: empty, so the module's compile policy and cache
        // identity keep their default digests.
        let unmarked = Wasm32FnLinkage::new(CRATE);
        assert!(unmarked.never_inline_defined_in(&m).is_empty());
    }

    #[test]
    fn native_never_inline_set_follows_the_cgu_private_names() {
        // Mach-O (Apple x86-64 and AArch64) and AArch64 ELF: lowering gives
        // every `Internal` function its CGU-private name (`CguSymbols::apply`)
        // before the module reaches `apply` and `never_inline_defined_in`.
        // The Mach-O name keeps rustc's symbol; the ELF one is the unit and
        // index alone, so no test can find it by rustc's symbol. `local_copy`
        // and `helper` are `Internal` here; `shared` is not.
        use crate::function_linkage::PrivateSymbolFormat;
        for (format, private) in [
            (
                PrivateSymbolFormat::MachO,
                "__trust_cg_private.cgu.0.0.local_copy",
            ),
            (PrivateSymbolFormat::Elf, "__trust_cg_private.cgu.0.0"),
        ] {
            let mut plan = CguSymbols::enabled_for(format);
            for (index, symbol, linkage) in [
                (0, "local_copy", Linkage::Internal),
                (1, "shared", Linkage::External),
                (2, "helper", Linkage::Internal),
            ] {
                plan.insert(
                    "cgu.0",
                    index,
                    symbol.to_owned(),
                    linkage,
                    Visibility::Default,
                )
                .unwrap();
            }
            let mut m = module(MODULE);
            plan.apply(&mut m).unwrap();
            assert!(
                m.functions.iter().any(|f| f.name == private),
                "{format:?}: lowering names `local_copy` `{private}`"
            );
            let mut placed = Wasm32FnLinkage::new(CRATE);
            for symbol in ["local_copy", "shared"] {
                placed.record_never_inline(&plan, symbol);
            }
            placed.apply(&mut m).unwrap();
            assert_eq!(
                placed
                    .never_inline_defined_in(&m)
                    .into_iter()
                    .collect::<Vec<_>>(),
                vec![private.to_string(), "shared".to_string()],
                "{format:?}"
            );
            // Non-vacuity: the same functions recorded under rustc's symbols
            // (the bridge before this rule) name only the one lowering did not
            // rename.
            let mut by_rustc_symbol = Wasm32FnLinkage::new(CRATE);
            for symbol in ["local_copy", "shared"] {
                by_rustc_symbol.record_never_inline(&CguSymbols::default(), symbol);
            }
            assert_eq!(
                by_rustc_symbol
                    .never_inline_defined_in(&m)
                    .into_iter()
                    .collect::<Vec<_>>(),
                vec!["shared".to_string()],
                "{format:?}"
            );
        }
    }

    #[test]
    fn internal_item_placed_once_is_a_strong_hidden_definition() {
        // Internalized into its only CGU: one object defines it, so it stays
        // strong, and the wasm lane may analyse the body its calls reach.
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record(
            "local_copy",
            RustcLinkage::Internal,
            RustcVisibility::Default,
        );
        let mut m = module(MODULE);
        placed.apply(&mut m).unwrap();
        let local = func(&m, &crate_private_symbol("local_copy", CRATE));
        assert_eq!(
            (local.linkage, local.visibility),
            (Linkage::External, Visibility::Hidden)
        );
        // A second and a third copy: coalesced, whichever CGU came first.
        for copies in [2, 3] {
            let mut placed = Wasm32FnLinkage::new(CRATE);
            for _ in 0..copies {
                placed.record(
                    "local_copy",
                    RustcLinkage::Internal,
                    RustcVisibility::Default,
                );
            }
            let mut m = module(MODULE);
            placed.apply(&mut m).unwrap();
            let local = func(&m, &crate_private_symbol("local_copy", CRATE));
            assert_eq!(
                (local.linkage, local.visibility),
                (Linkage::LinkOnceOdr, Visibility::Hidden),
                "{copies} copies"
            );
        }
        // An exported placement is never mistaken for a single CGU-private
        // copy, in either order.
        for order in [
            [RustcLinkage::Internal, RustcLinkage::External],
            [RustcLinkage::External, RustcLinkage::Internal],
        ] {
            let mut placed = Wasm32FnLinkage::new(CRATE);
            for linkage in order {
                placed.record("shared", linkage, RustcVisibility::Hidden);
            }
            let err = placed.apply(&mut module(MODULE)).unwrap_err();
            assert!(err.contains("several codegen units"), "{err}");
        }
    }

    #[test]
    fn native_table_claims_only_copies_placed_in_several_cgus() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record_native_copies(&[
            // A `LocalCopy` in two CGUs: the one symbol every object defined.
            (
                "local_copy",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                false,
            ),
            (
                "local_copy",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                false,
            ),
            // Internalized into its only CGU, naming this crate: the bridge's
            // own linkage and name stay.
            (
                "helper",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                false,
            ),
            (
                "shared",
                RustcLinkage::External,
                RustcVisibility::Hidden,
                false,
            ),
            // A declaration of a copy: renamed with it, never given linkage.
            (
                "callee",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                false,
            ),
            (
                "callee",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                false,
            ),
        ]);
        let mut m = module(MODULE);
        placed.apply(&mut m).unwrap();
        let local = func(&m, &crate_private_symbol("local_copy", CRATE));
        // Default visibility: the native function emitters spell no hidden
        // definition, and the crate-private name keeps other crates apart.
        assert_eq!(
            (local.linkage, local.visibility),
            (Linkage::LinkOnceOdr, Visibility::Default)
        );
        let callee = func(&m, &crate_private_symbol("callee", CRATE));
        assert!(callee.blocks.is_empty(), "callee is a declaration");
        assert_eq!(callee.linkage, Linkage::External);
        for name in ["helper", "shared"] {
            let f = func(&m, name);
            assert_eq!(
                (f.linkage, f.visibility),
                (Linkage::External, Visibility::Default),
                "{name}"
            );
        }
        // The call inside the copy names the renamed declaration.
        let local = func(&m, &crate_private_symbol("local_copy", CRATE));
        let callee_id = m
            .functions
            .iter()
            .position(|f| f.name == crate_private_symbol("callee", CRATE))
            .unwrap();
        assert!(local.blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::Call { callee, .. } if callee.index() as usize == callee_id
        )));
    }

    #[test]
    fn native_table_is_empty_for_a_single_cgu_crate_naming_itself() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record_native_copies(&[
            (
                "local_copy",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                false,
            ),
            (
                "shared",
                RustcLinkage::External,
                RustcVisibility::Default,
                false,
            ),
        ]);
        let mut m = module(MODULE);
        let before = m.clone();
        placed.apply(&mut m).unwrap();
        assert_eq!(m, before);
    }

    /// A crate-agnostic copy (an upstream `#[inline]` function's `LocalCopy`,
    /// whose symbol names no instantiating crate) placed in ONE codegen unit
    /// is still defined by every other crate that copies it: it takes the
    /// crate-private name, as a strong definition since this crate has one.
    #[test]
    fn native_table_renames_a_crate_agnostic_copy_placed_once() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record_native_copies(&[
            (
                "local_copy",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                true,
            ),
            (
                "callee",
                RustcLinkage::Internal,
                RustcVisibility::Default,
                true,
            ),
            // Exported: rustc's symbol is the contract; never renamed.
            (
                "shared",
                RustcLinkage::External,
                RustcVisibility::Default,
                true,
            ),
        ]);
        let mut m = module(MODULE);
        placed.apply(&mut m).unwrap();
        let local = func(&m, &crate_private_symbol("local_copy", CRATE));
        assert_eq!(
            (local.linkage, local.visibility),
            (Linkage::External, Visibility::Default)
        );
        let callee_id = m
            .functions
            .iter()
            .position(|f| f.name == crate_private_symbol("callee", CRATE))
            .unwrap();
        assert!(m.functions[callee_id].blocks.is_empty());
        assert!(local.blocks[0].body.iter().any(|node| matches!(
            &node.inst,
            Inst::Call { callee, .. } if callee.index() as usize == callee_id
        )));
        assert!(m.functions.iter().any(|f| f.name == "shared"));
        assert!(m.functions.iter().all(|f| f.name != "local_copy"));
    }

    #[test]
    fn internal_references_move_to_the_crate_private_name() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record(
            "local_copy",
            RustcLinkage::Internal,
            RustcVisibility::Default,
        );
        placed.record("callee", RustcLinkage::Internal, RustcVisibility::Default);
        placed.record("shared", RustcLinkage::External, RustcVisibility::Default);
        let mut m = module(MODULE);
        m.globals.push(address_global("table", "local_copy"));
        let helper = m.functions.iter_mut().find(|f| f.name == "helper").unwrap();
        helper.blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::Ptr,
                value: Constant::symbol_addr("callee"),
            }),
        );
        placed.apply(&mut m).unwrap();
        let symbols = |constant: &Constant| -> Vec<String> {
            let mut out = Vec::new();
            constant.visit_constants(|c| {
                if let Constant::SymbolAddr { symbol, .. } = c {
                    out.push(symbol.clone());
                }
            });
            out
        };
        // The data slot and the code constant follow the rename; the
        // External item keeps rustc's symbol.
        assert_eq!(
            symbols(m.globals[0].initializer.as_ref().unwrap()),
            [
                crate_private_symbol("local_copy", CRATE),
                "shared".to_owned()
            ]
        );
        let Inst::Const { value, .. } = &func(&m, "helper").blocks[0].body[0].inst else {
            panic!("helper lost its constant");
        };
        assert_eq!(symbols(value), [crate_private_symbol("callee", CRATE)]);
        // The call through `func.0` names the renamed declaration.
        assert_eq!(m.functions[0].name, crate_private_symbol("callee", CRATE));
        assert!(!m.functions.iter().any(|f| f.name == "local_copy"));
    }

    #[test]
    fn crate_private_names_differ_between_crates() {
        // Two crates' copies of one upstream `LocalCopy` (rustc gives both the
        // same symbol) never share a wasm symbol, so `wasm-ld` cannot
        // coalesce copies codegened under different session flags.
        let symbol = "_RNvMs0_NtCs0_4core3numl3abs";
        let mut first = module(MODULE);
        let mut second = module(MODULE);
        for (m, crate_tag) in [(&mut first, 1u64), (&mut second, 2u64)] {
            let mut placed = Wasm32FnLinkage::new(crate_tag);
            placed.record(
                "local_copy",
                RustcLinkage::Internal,
                RustcVisibility::Default,
            );
            placed.apply(m).unwrap();
        }
        assert_ne!(
            crate_private_symbol(symbol, 1),
            crate_private_symbol(symbol, 2)
        );
        assert_ne!(first.functions[1].name, second.functions[1].name);
        assert!(first.functions[1].name.starts_with("local_copy."));
    }

    #[test]
    fn explicit_weak_linkages_stay_weak() {
        for (rustc, expected) in [
            (RustcLinkage::WeakAny, Linkage::Weak),
            (RustcLinkage::WeakODR, Linkage::WeakOdr),
            (RustcLinkage::LinkOnceAny, Linkage::LinkOnce),
            (RustcLinkage::LinkOnceODR, Linkage::LinkOnceOdr),
        ] {
            assert_eq!(
                definition_linkage(rustc, RustcVisibility::Default),
                Ok((expected, Visibility::Default))
            );
            // An explicit `#[linkage]` shares rustc's symbol by design.
            let mut placed = Wasm32FnLinkage::new(CRATE);
            placed.record("shared", rustc, RustcVisibility::Default);
            let mut m = module(MODULE);
            placed.apply(&mut m).unwrap();
            assert_eq!(func(&m, "shared").linkage, expected);
        }
    }

    #[test]
    fn linkage_without_a_definition_form_is_refused() {
        for rustc in [
            RustcLinkage::AvailableExternally,
            #[cfg(rustc_linkage_common)]
            RustcLinkage::Common,
            RustcLinkage::ExternalWeak,
        ] {
            let mut placed = Wasm32FnLinkage::new(CRATE);
            placed.record("shared", rustc, RustcVisibility::Default);
            let err = placed.apply(&mut module(MODULE)).unwrap_err();
            assert!(err.contains("[TCG-WASM32-LINKAGE]"), "{err}");
        }
    }

    #[test]
    fn conflicting_placements_are_refused() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record("shared", RustcLinkage::External, RustcVisibility::Default);
        placed.record("shared", RustcLinkage::Internal, RustcVisibility::Default);
        let err = placed.apply(&mut module(MODULE)).unwrap_err();
        assert!(err.contains("several codegen units"), "{err}");
    }

    #[test]
    fn a_bridge_chosen_linkage_is_never_overridden() {
        let mut placed = Wasm32FnLinkage::new(CRATE);
        placed.record("shared", RustcLinkage::Internal, RustcVisibility::Default);
        let mut m = module(MODULE);
        m.functions
            .iter_mut()
            .find(|f| f.name == "shared")
            .unwrap()
            .linkage = Linkage::Internal;
        let err = placed.apply(&mut m).unwrap_err();
        assert!(err.contains("refusing rather than pick one"), "{err}");
    }
}
