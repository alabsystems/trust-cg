// trust-cg-codegen/tests/aarch64_elf_symbol_binding/visibility_table.rs
//
// L02-P6 closure audit 4: the AArch64 ELF visibility cross-product table.
//
// Every earlier round pinned the classes its own audit found. This table
// generates the whole cross-product instead, so a visibility decision site
// that only one class reaches cannot survive unpinned:
//
//   {definition, declaration}
//   x {external, weak, linkonce, linkonce_odr, weak_odr, internal,
//      external_weak, available_externally}
//   x {default, hidden, protected}
//   x {function, mutable data, read-only data, pointer-bearing read-only data
//      (`.data.rel.ro`), zero-fill data (`.bss`), thread-local (`.tdata`),
//      zero-fill thread-local (`.tbss`)}
//   x {implicit section, explicit family name (`.data.vt_c`, a shared
//      `.text.vt_c`, a COMDAT's own `.text.vtc_<symbol>` ...), explicit
//      `.text`}
//   x {function sections off, on}
//   x {static, pie, pic}
//   x {Compiler::compile sequential and parallel (the unwind emitter), the
//      Pipeline unwind emitter, the layout-less relocating emitter, the
//      relocation-free emitter}.
//
// [`classify`] sorts each of the 1,008 symbol cases into admitted, refused
// with a named diagnostic, or inexpressible with the reason. Every refused
// case is compiled and its diagnostic asserted, and every inexpressible
// class has a witness, so a pruned combination cannot hide a gap. For every
// admitted case and route the object's symbol is read back by the
// independent parser in the parent module and checked for binding, type,
// visibility, section name, type and flags, COMDAT group membership and
// signature, and address form: a GOT pair exactly when the shared predicate
// makes the address GOT-indirect, the relocation model's TLS access, the
// object-local `.Ltls.<symbol>` anchor exactly for a strong hidden
// thread-local definition under `pic`, and a kept branch for every call the
// module inliner may not fold. The Pipeline routes are also run through the
// emitters' relocation-model backstop: every PC-relative reference the
// shared predicate forbids is refused by name, and the one it allows under
// the executable models (a default-visibility strong data import) compiles.
// Structural purity, read from the public module translation's pure
// callees, follows the same replacement predicates.
//
// The native row in the parent module links the `pic` objects of every
// route into one shared library with GNU ld, gold and LLD and checks
// `.dynsym` and `LD_PRELOAD` interposition for every admitted definition and
// declaration.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use std::collections::BTreeMap;
use trust_cg_codegen::RelocationModel;

// =============================================================================
// The cross-product and its classification
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Role {
    Definition,
    Declaration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(clippy::enum_variant_names)] // The variants spell trust-ir's linkage kinds.
pub(super) enum Link {
    External,
    Weak,
    LinkOnce,
    LinkOnceOdr,
    WeakOdr,
    Internal,
    ExternalWeak,
    AvailableExternally,
}

impl Link {
    pub(super) const ALL: [Self; 8] = [
        Self::External,
        Self::Weak,
        Self::LinkOnce,
        Self::LinkOnceOdr,
        Self::WeakOdr,
        Self::Internal,
        Self::ExternalWeak,
        Self::AvailableExternally,
    ];

    /// The trust-ir text keyword.
    pub(super) const fn keyword(self) -> &'static str {
        match self {
            Self::External => "external",
            Self::Weak => "weak",
            Self::LinkOnce => "linkonce",
            Self::LinkOnceOdr => "linkonce_odr",
            Self::WeakOdr => "weak_odr",
            Self::Internal => "internal",
            Self::ExternalWeak => "external_weak",
            Self::AvailableExternally => "available_externally",
        }
    }

    const fn tag(self) -> &'static str {
        match self {
            Self::External => "ext",
            Self::Weak => "weak",
            Self::LinkOnce => "lo",
            Self::LinkOnceOdr => "lodr",
            Self::WeakOdr => "wodr",
            Self::Internal => "int",
            Self::ExternalWeak => "xw",
            Self::AvailableExternally => "ae",
        }
    }

    /// `STB_WEAK` definition linkages.
    const fn weak_definition(self) -> bool {
        matches!(
            self,
            Self::Weak | Self::LinkOnce | Self::LinkOnceOdr | Self::WeakOdr
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Kind {
    Function,
    Data,
    Rodata,
    RelRo,
    Bss,
    Tdata,
    Tbss,
}

impl Kind {
    pub(super) const ALL: [Self; 7] = [
        Self::Function,
        Self::Data,
        Self::Rodata,
        Self::RelRo,
        Self::Bss,
        Self::Tdata,
        Self::Tbss,
    ];

    const fn tag(self) -> &'static str {
        match self {
            Self::Function => "fn",
            Self::Data => "data",
            Self::Rodata => "ro",
            Self::RelRo => "rr",
            Self::Bss => "bss",
            Self::Tdata => "td",
            Self::Tbss => "tb",
        }
    }

    pub(super) const fn tls(self) -> bool {
        matches!(self, Self::Tdata | Self::Tbss)
    }

    /// The implicit section, and the family an explicit name extends.
    const fn base(self) -> &'static str {
        match self {
            Self::Function => ".text",
            Self::Data => ".data",
            Self::Rodata => ".rodata",
            Self::RelRo => ".data.rel.ro",
            Self::Bss => ".bss",
            Self::Tdata => ".tdata",
            Self::Tbss => ".tbss",
        }
    }

    const fn sh_type(self) -> u32 {
        match self {
            Self::Bss | Self::Tbss => SHT_NOBITS,
            _ => SHT_PROGBITS,
        }
    }

    const fn sh_flags(self) -> u64 {
        match self {
            Self::Function => SHF_ALLOC | SHF_EXECINSTR,
            Self::Rodata => SHF_ALLOC,
            Self::Data | Self::RelRo | Self::Bss => SHF_ALLOC | SHF_WRITE,
            Self::Tdata | Self::Tbss => SHF_ALLOC | SHF_WRITE | SHF_TLS,
        }
    }

    const fn mutable(self) -> bool {
        matches!(self, Self::Data | Self::Bss | Self::Tdata | Self::Tbss)
    }

    /// Declarations the text form can state without an initializer.
    const fn declarable(self) -> bool {
        matches!(self, Self::Data | Self::Rodata | Self::Tdata)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Place {
    /// No explicit section.
    Implicit,
    /// An explicit name in the kind's own family: a shared `<base>.vt_<route>`
    /// for non-COMDAT members, `<base>.vtc_<symbol>` for a COMDAT one.
    Named,
    /// The explicit name `.text`.
    Text,
}

impl Place {
    pub(super) const ALL: [Self; 3] = [Self::Implicit, Self::Named, Self::Text];

    const fn tag(self) -> &'static str {
        match self {
            Self::Implicit => "i",
            Self::Named => "n",
            Self::Text => "t",
        }
    }
}

pub(super) const VISIBILITY_ORDER: [Visibility; 3] = [
    Visibility::Default,
    Visibility::Hidden,
    Visibility::Protected,
];

const fn visibility_tag(visibility: Visibility) -> &'static str {
    match visibility {
        Visibility::Default => "d",
        Visibility::Hidden => "h",
        Visibility::Protected => "p",
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Case {
    pub(super) role: Role,
    pub(super) link: Link,
    pub(super) visibility: Visibility,
    pub(super) kind: Kind,
    pub(super) place: Place,
}

impl Case {
    /// The symbol this case defines or declares in route `route`'s object.
    pub(super) fn name(self, route: &str) -> String {
        format!(
            "{route}_{}_{}_{}_{}_{}",
            match self.role {
                Role::Definition => "def",
                Role::Declaration => "dec",
            },
            self.link.tag(),
            visibility_tag(self.visibility),
            self.kind.tag(),
            self.place.tag()
        )
    }

    /// A COMDAT definition: the one-definition-rule function linkages, and
    /// every link-once or ODR data linkage.
    pub(super) const fn comdat(self) -> bool {
        matches!(self.role, Role::Definition)
            && match self.kind {
                Kind::Function => matches!(self.link, Link::LinkOnceOdr | Link::WeakOdr),
                _ => matches!(
                    self.link,
                    Link::LinkOnce | Link::LinkOnceOdr | Link::WeakOdr
                ),
            }
    }

    /// Whether the object DEFINES the symbol. Every declaration row's symbol
    /// is undefined, an initializer-less `internal` thread-local's included:
    /// the backend reads it as an import.
    pub(super) const fn defined(self) -> bool {
        matches!(self.role, Role::Definition)
    }

    /// The visibility the object must spell: a module-local definition is
    /// `STV_DEFAULT` whatever it states.
    pub(super) const fn spelled_visibility(self) -> Visibility {
        if self.defined() && matches!(self.link, Link::Internal) {
            Visibility::Default
        } else {
            self.visibility
        }
    }

    /// Whether a C program or another image can name the symbol at all.
    pub(super) const fn exported(self) -> bool {
        !(self.defined() && matches!(self.link, Link::Internal))
    }
}

/// A combination the backend refuses, by the diagnostic it names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Refusal {
    /// A module-local function with non-default visibility.
    FunctionVisibility,
    /// A COMDAT function naming the shared `.text`.
    ComdatFunctionInText,
    /// Data naming an executable section.
    DataInText,
    /// A declaration with an explicit section.
    DeclarationSection,
    /// An `external_weak` global with an initializer.
    WeakDeclarationInitializer,
    /// An `external_weak` function with a body.
    WeakDeclarationBody,
    /// An `external_weak` thread-local.
    WeakThreadLocal,
    /// A bodyless function whose linkage is not a declaration linkage:
    /// trust-ir's validator reports `EmptyFunction`, and the backend names
    /// the linkage (`[TCG-DECLARATION-LINKAGE]`).
    BodylessDefinitionLinkage,
    /// An initializer-less `internal` thread-local (read as an import) with
    /// non-default visibility: the adapter spells import visibility only for
    /// a linkage that names another object's symbol.
    InternalThreadLocalImportVisibility,
}

impl Refusal {
    /// The text `Compiler::compile`'s error must contain (trust-ir's
    /// validator separately reports `EmptyFunction` for
    /// [`Self::BodylessDefinitionLinkage`]).
    pub(super) const fn diagnostic(self) -> &'static str {
        match self {
            Self::FunctionVisibility => "[TCG-FUNCTION-VISIBILITY]",
            Self::ComdatFunctionInText => "[TCG-SECTION-RESERVED]",
            Self::DataInText => "[TCG-SECTION-EXEC]",
            Self::DeclarationSection => "[TCG-SECTION-IMPORT]",
            Self::WeakDeclarationInitializer => {
                "an `external_weak` global is a weak DECLARATION; an initializer cannot be emitted"
            }
            Self::WeakDeclarationBody => {
                "an `external_weak` function is a weak DECLARATION; a body cannot be emitted"
            }
            Self::WeakThreadLocal => {
                "a thread-local `external_weak` global needs a weak undefined TLS reference"
            }
            Self::BodylessDefinitionLinkage => "[TCG-DECLARATION-LINKAGE]",
            Self::InternalThreadLocalImportVisibility => "is a cross-object import with visibility",
        }
    }
}

/// A combination the text form cannot state as its row, with the reason and
/// the row that covers it instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Inexpressible {
    /// `available_externally` bodies and initializers are never emitted: the
    /// object gets an undefined reference, which the declaration rows cover.
    AvailableExternallyDefinition,
    /// An initializer-less `internal` global is a zero-fill DEFINITION (the
    /// internal `.bss`/`.rodata` definition rows cover it).
    InternalDeclarationIsDefinition,
    /// A declaration has no initializer, so it cannot be zero-fill or
    /// pointer-bearing; its undefined symbol is the mutable/read-only/TLS
    /// declaration row's.
    DeclarationHasNoInitializer,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Class {
    Admitted,
    Refused(Refusal),
    Inexpressible(Inexpressible),
}

/// The whole cross-product, in a fixed order.
pub(super) fn cross_product() -> Vec<Case> {
    let mut cases = Vec::new();
    for role in [Role::Definition, Role::Declaration] {
        for link in Link::ALL {
            for visibility in VISIBILITY_ORDER {
                for kind in Kind::ALL {
                    for place in Place::ALL {
                        cases.push(Case {
                            role,
                            link,
                            visibility,
                            kind,
                            place,
                        });
                    }
                }
            }
        }
    }
    cases
}

/// Sort one case, in the order the backend checks: the first refusal it
/// reaches is the one asserted.
pub(super) fn classify(case: Case) -> Class {
    use Class::{Admitted, Inexpressible as Never, Refused};
    let function = case.kind == Kind::Function;
    if case.role == Role::Definition {
        return match case.link {
            // The backend treats the body or initializer as absent: the case
            // is its declaration twin.
            Link::AvailableExternally => match classify(Case {
                role: Role::Declaration,
                ..case
            }) {
                Admitted => Never(Inexpressible::AvailableExternallyDefinition),
                other => other,
            },
            Link::ExternalWeak if function => Refused(Refusal::WeakDeclarationBody),
            Link::ExternalWeak => Refused(Refusal::WeakDeclarationInitializer),
            _ if function
                && case.link == Link::Internal
                && case.visibility != Visibility::Default =>
            {
                Refused(Refusal::FunctionVisibility)
            }
            _ if function && case.place == Place::Text && case.comdat() => {
                Refused(Refusal::ComdatFunctionInText)
            }
            _ if !function && case.place == Place::Text => Refused(Refusal::DataInText),
            _ => Admitted,
        };
    }
    if function {
        return match case.link {
            Link::External | Link::ExternalWeak | Link::AvailableExternally
                if case.place == Place::Implicit =>
            {
                Admitted
            }
            Link::External | Link::ExternalWeak | Link::AvailableExternally => {
                Refused(Refusal::DeclarationSection)
            }
            _ => Refused(Refusal::BodylessDefinitionLinkage),
        };
    }
    if case.link == Link::ExternalWeak && case.kind.tls() {
        return Refused(Refusal::WeakThreadLocal);
    }
    if case.link == Link::Internal && !case.kind.tls() {
        return if case.place == Place::Text {
            Refused(Refusal::DataInText)
        } else {
            Never(Inexpressible::InternalDeclarationIsDefinition)
        };
    }
    if case.link == Link::Internal && case.visibility != Visibility::Default {
        return Refused(Refusal::InternalThreadLocalImportVisibility);
    }
    if case.place != Place::Implicit {
        return Refused(Refusal::DeclarationSection);
    }
    if !case.kind.declarable() && case.link != Link::AvailableExternally {
        return Never(Inexpressible::DeclarationHasNoInitializer);
    }
    Admitted
}

/// The admitted cases, in cross-product order.
pub(super) fn admitted() -> Vec<Case> {
    cross_product()
        .into_iter()
        .filter(|case| classify(*case) == Class::Admitted)
        .collect()
}

// =============================================================================
// Expected object attributes
// =============================================================================

const SHT_PROGBITS: u32 = 1;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_EXECINSTR: u64 = 0x4;
const SHF_GROUP: u64 = 0x200;
const SHF_TLS: u64 = 0x400;
const R_AARCH64_TLSLE: [u32; 2] = [
    R_AARCH64_TLSLE_ADD_TPREL_HI12,
    R_AARCH64_TLSLE_ADD_TPREL_LO12_NC,
];
const R_AARCH64_TLSIE: [u32; 2] = [
    R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21,
    R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC,
];
const GOT_PAIR: [u32; 2] = [R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC];
const DIRECT_PAIR: [u32; 2] = [R_AARCH64_ADR_PREL_PG_HI21, R_AARCH64_ADD_ABS_LO12_NC];

/// The object routes the table runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Route {
    /// `Compiler::compile`, sequential or parallel: the unwind emitter.
    Compiler,
    /// `Pipeline` module emission with every frame layout: the unwind emitter.
    PipelineUnwind,
    /// `Pipeline` module emission without layouts, with fixups: the
    /// layout-less relocating emitter.
    PipelineLayoutLess,
    /// `Pipeline` module emission without layouts, fixups or pointer slots:
    /// the relocation-free emitter.
    PipelineRelocationFree,
}

impl Route {
    /// Symbol prefix, so every route's object links into one library.
    pub(super) const fn prefix(self) -> &'static str {
        match self {
            Self::Compiler => "c",
            Self::PipelineUnwind => "u",
            Self::PipelineLayoutLess => "l",
            Self::PipelineRelocationFree => "r",
        }
    }

    /// The admitted cases this route carries. The Pipeline API has no
    /// trust-ir linkage: it takes the Compiler's admitted cases as the
    /// `ObjectGlobal`/`FunctionSymbolBinding` fields the Compiler maps them
    /// to, plus the local functions with a stated visibility the Compiler
    /// refuses (a `Local` binding normalizes visibility to default). The
    /// relocation-free route carries no accessor, so it has no references:
    /// its declarations emit nothing, and a pointer-bearing global would
    /// give it a relocation (checked by
    /// the target's `visibility_table_pruned_combinations_are_refused_by_name`
    /// row).
    pub(super) fn cases(self) -> Vec<Case> {
        let mut cases = admitted();
        if self != Self::Compiler {
            cases.extend(
                cross_product()
                    .into_iter()
                    .filter(|case| classify(*case) == Class::Refused(Refusal::FunctionVisibility)),
            );
            cases.sort();
        }
        if self == Self::PipelineRelocationFree {
            cases.retain(|case| case.kind != Kind::RelRo);
        }
        cases
    }
}

/// How the object must reach a thread-local.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TlsAccess {
    LocalExec,
    InitialExec,
    Descriptor { anchored: bool },
}

/// The section a defined case must land in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Placement {
    pub(super) name: String,
    sh_type: u32,
    sh_flags: u64,
    comdat: bool,
}

pub(super) fn placement(case: Case, route: Route, function_sections: bool) -> Placement {
    let prefix = route.prefix();
    let symbol = case.name(prefix);
    let name = match (case.kind, case.place) {
        (Kind::Function, Place::Text) => ".text".to_string(),
        (Kind::Function, Place::Implicit) if case.comdat() || function_sections => {
            format!(".text.{symbol}")
        }
        (_, Place::Implicit) if case.comdat() => format!("{}.{symbol}", case.kind.base()),
        (_, Place::Implicit) => case.kind.base().to_string(),
        (_, Place::Named) if case.comdat() => format!("{}.vtc_{symbol}", case.kind.base()),
        (_, Place::Named) => format!("{}.vt_{prefix}", case.kind.base()),
        (_, Place::Text) => unreachable!("data in `.text` is refused"),
    };
    Placement {
        name,
        sh_type: case.kind.sh_type(),
        sh_flags: case.kind.sh_flags() | if case.comdat() { SHF_GROUP } else { 0 },
        comdat: case.comdat(),
    }
}

/// The explicit section a case states, if any.
pub(super) fn explicit_section(case: Case, route: Route) -> Option<String> {
    match case.place {
        Place::Implicit => None,
        Place::Text => Some(".text".to_string()),
        Place::Named => Some(placement(case, route, false).name),
    }
}

/// Whether every address of the case's symbol comes from the GOT under
/// `model`: every undefined reference, and a default-visibility non-local
/// definition in shared-object code (the shared predicate's table).
pub(super) fn got_indirect(case: Case, model: RelocationModel) -> bool {
    if !case.defined() {
        return true;
    }
    model == RelocationModel::Pic && case.exported() && case.visibility == Visibility::Default
}

/// Whether `case`'s TLS descriptors name its object-local `.Ltls` anchor
/// under `model` (a strong hidden thread-local definition under `pic`).
/// Only the native link-time audit reads it, so it exists where that does.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
pub(super) fn anchored(case: Case, model: RelocationModel) -> bool {
    case.kind.tls() && tls_access(case, model) == TlsAccess::Descriptor { anchored: true }
}

fn tls_access(case: Case, model: RelocationModel) -> TlsAccess {
    match (model, case.defined()) {
        (RelocationModel::Pic, defined) => TlsAccess::Descriptor {
            anchored: defined
                && case.link == Link::External
                && case.visibility == Visibility::Hidden,
        },
        (_, true) => TlsAccess::LocalExec,
        (_, false) => TlsAccess::InitialExec,
    }
}

/// Whether a function case gets a `call_<symbol>` accessor: every
/// definition and every declaration trust-ir may call directly (not an
/// `external_weak` one).
pub(super) const fn callable(case: Case) -> bool {
    matches!(case.kind, Kind::Function) && !matches!(case.link, Link::ExternalWeak)
}

/// Whether `call_<symbol>` must stay a branch at every optimization level:
/// the module inliner may fold neither a declaration without a body, nor a
/// definition another module may replace: `weak`/`linkonce` at static link,
/// or a preemptible `external` one at load time. (The one-definition-rule
/// linkages promise equivalent copies, so the inliner may fold a preemptible
/// `linkonce_odr`/`weak_odr` one, as LLVM does.)
pub(super) fn call_kept(case: Case, model: RelocationModel, route: Route) -> bool {
    route != Route::Compiler
        || match (case.role, case.link) {
            (Role::Declaration, Link::AvailableExternally) => false,
            (Role::Declaration, _) => true,
            (Role::Definition, Link::Weak | Link::LinkOnce) => true,
            (Role::Definition, Link::External) => got_indirect(case, model),
            (Role::Definition, _) => false,
        }
}

/// A distinct nonzero value per case ordinal (the zero-fill kinds hold 0).
pub(super) const fn case_value(ordinal: usize) -> u64 {
    0x1000 + ordinal as u64
}

// =============================================================================
// Inputs: trust-ir text for the Compiler route, LIR and ObjectGlobals for the
// Pipeline routes
// =============================================================================

/// The slot target every pointer-bearing global points at.
pub(super) fn slot_target(route: Route) -> String {
    format!("{}_slot_target", route.prefix())
}

pub(super) const SLOT_TARGET_VALUE: u64 = 0x5107;

/// The trust-ir text of the Compiler route's module: the slot target, every
/// data case, every function case, then `call_<symbol>` for every callable
/// function case and `addr_<symbol>` for every case.
pub(super) fn table_text(cases: &[Case]) -> String {
    let route = Route::Compiler;
    let prefix = route.prefix();
    let mut text = String::from(
        "module \"visibility_table\"\nfuncty.0 = () -> (u64)\nfuncty.1 = () -> (ptr)\n",
    );
    text.push_str(&format!(
        "global external visibility(hidden) @{} u64 = {SLOT_TARGET_VALUE}\n",
        slot_target(route)
    ));
    let mut global_index = BTreeMap::new();
    for (ordinal, case) in cases.iter().enumerate() {
        if case.kind == Kind::Function {
            continue;
        }
        let name = case.name(prefix);
        let tls = if case.kind.tls() {
            " tls(general_dynamic)"
        } else {
            ""
        };
        let mutable = if case.kind.mutable() { " mut" } else { "" };
        let section = explicit_section(*case, route)
            .map(|section| format!(" section(\"{section}\")"))
            .unwrap_or_default();
        let (ty, initializer) = match case.kind {
            Kind::RelRo => ("ptr", format!(" = symaddr<{}>", slot_target(route))),
            Kind::Bss | Kind::Tbss => ("u64", " = 0".to_string()),
            _ => ("u64", format!(" = {}", case_value(ordinal))),
        };
        let initializer = match (case.role, case.link) {
            (Role::Definition, _) | (_, Link::AvailableExternally) => initializer,
            _ => String::new(),
        };
        global_index.insert(name.clone(), global_index.len() + 1);
        text.push_str(&format!(
            "global {}{tls}{mutable} visibility({}){section} @{name} {ty}{initializer}\n",
            case.link.keyword(),
            case.visibility
        ));
    }
    let mut function_index = BTreeMap::new();
    for (ordinal, case) in cases.iter().enumerate() {
        if case.kind != Kind::Function {
            continue;
        }
        let name = case.name(prefix);
        function_index.insert(name.clone(), function_index.len());
        let section = explicit_section(*case, route)
            .map(|section| format!("    ; #section: \"{section}\"\n"))
            .unwrap_or_default();
        let bodied = case.role == Role::Definition || case.link == Link::AvailableExternally;
        let body = if bodied {
            format!(
                "bb0:\n    %0 = const u64 {}\n    ret %0\n",
                case_value(ordinal)
            )
        } else {
            String::new()
        };
        text.push_str(&format!(
            "{} fn @{name}(functy.0) {{\n{section}    ; #visibility: {}\n{body}}}\n",
            case.link.keyword(),
            case.visibility
        ));
    }
    for case in cases {
        let name = case.name(prefix);
        if case.kind == Kind::Function {
            if callable(*case) {
                text.push_str(&format!(
                    "fn @call_{name}(functy.0) {{\nbb0:\n    %0 = call @func.{}()\n    ret %0\n}}\n",
                    function_index[&name]
                ));
            }
            text.push_str(&format!(
                "fn @addr_{name}(functy.1) {{\nbb0:\n    %0 = const ptr symaddr<{name}>\n    ret %0\n}}\n"
            ));
        } else {
            text.push_str(&format!(
                "fn @addr_{name}(functy.1) {{\nbb0:\n    %0 = global_addr @global.{}\n    ret %0\n}}\n",
                global_index[&name]
            ));
        }
    }
    text
}

/// The Compiler route's module for `cases`.
pub(super) fn table_module(cases: &[Case]) -> Module {
    parse_linux(&table_text(cases))
}

/// The number of functions [`table_text`] defines for `cases`.
fn table_function_count(cases: &[Case]) -> usize {
    cases
        .iter()
        .map(|case| match case.kind {
            Kind::Function => 2 + usize::from(callable(*case)),
            _ => 1,
        })
        .sum()
}

/// A compiler with an explicit relocation model, function-sections policy
/// and a full trace.
pub(super) fn table_compiler(
    opt_level: OptLevel,
    model: RelocationModel,
    function_sections: bool,
    parallel: bool,
) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel,
            relocation_model: model,
            function_sections,
            trace_level: CompilerTraceLevel::Full,
            ..Default::default()
        },
        TargetSpec::parse(LINUX).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// The `ObjectGlobal` the Pipeline routes hand over for a data case, as
/// `module_object_globals` maps the case's trust-ir global.
fn pipeline_global(case: Case, route: Route, ordinal: usize) -> ObjectGlobal {
    let name = case.name(route.prefix());
    let import = !case.defined();
    let (data, symbol_refs) = match case.kind {
        _ if import => (vec![], vec![]),
        Kind::RelRo => (
            vec![0; 8],
            vec![GlobalSymbolRef {
                offset: 0,
                symbol: slot_target(route),
                addend: 0,
            }],
        ),
        Kind::Bss | Kind::Tbss => (vec![0; 8], vec![]),
        _ => (case_value(ordinal).to_le_bytes().to_vec(), vec![]),
    };
    ObjectGlobal {
        name,
        data,
        mutable: case.kind.mutable(),
        is_external: case.exported(),
        symbol_refs,
        is_thread_local: case.kind.tls(),
        is_import: import,
        is_weak: if import {
            case.link == Link::ExternalWeak
        } else {
            case.link.weak_definition()
        },
        align: 8,
        visibility: case.visibility,
        retained: false,
        section: explicit_section(case, route),
        comdat: case.comdat(),
    }
}

/// The binding the Pipeline routes give a function definition.
fn pipeline_binding(case: Case) -> FunctionSymbolBinding {
    let linkage = match case.link {
        Link::External => FunctionSymbolLinkage::Global,
        Link::Internal => FunctionSymbolLinkage::Local,
        _ => FunctionSymbolLinkage::Weak,
    };
    FunctionSymbolBinding::new(linkage, case.visibility)
}

fn returns_tls_ref(name: &str, symbol: &str, model: trust_cg_ir::TlsModel) -> LirFunction {
    lir_function(
        name,
        vec![
            Instruction {
                opcode: Opcode::TlsRef {
                    name: symbol.to_owned(),
                    model,
                    local_exec_offset: None,
                },
                args: vec![],
                results: vec![Value(0)],
            },
            Instruction {
                opcode: Opcode::Return,
                args: vec![Value(0)],
                results: vec![],
            },
        ],
    )
}

/// The accessor the Pipeline routes give `case`'s address under `model`,
/// choosing GOT or PC-relative access by the shared predicate (`got`
/// overrides it for the backstop rows).
fn pipeline_address_accessor(
    case: Case,
    route: Route,
    model: RelocationModel,
    got: bool,
) -> LirFunction {
    let name = case.name(route.prefix());
    let accessor = format!("addr_{name}");
    if case.kind.tls() {
        let tls_model = match tls_access(case, model) {
            TlsAccess::LocalExec => trust_cg_ir::TlsModel::LocalExec,
            TlsAccess::InitialExec => trust_cg_ir::TlsModel::InitialExec,
            TlsAccess::Descriptor { .. } => trust_cg_ir::TlsModel::GeneralDynamic,
        };
        returns_tls_ref(&accessor, &name, tls_model)
    } else if got {
        returns_got_address(&accessor, &name)
    } else {
        returns_direct_address(&accessor, &name)
    }
}

/// One Pipeline route's input: functions (definitions, then accessors), the
/// globals, and the symbol linkage.
pub(super) struct PipelineInput {
    pub(super) functions: Vec<LirFunction>,
    pub(super) globals: Vec<ObjectGlobal>,
    bindings: Vec<FunctionSymbolBinding>,
    weak_undefined: BTreeSet<String>,
    undefined_visibility: BTreeMap<String, Visibility>,
    comdat: BTreeSet<String>,
    sections: BTreeMap<String, String>,
}

impl PipelineInput {
    pub(super) fn linkage(&self) -> ModuleSymbolLinkage {
        ModuleSymbolLinkage::new(self.bindings.clone(), self.weak_undefined.clone())
            .with_undefined_function_visibility(self.undefined_visibility.clone())
            .with_comdat_functions(self.comdat.clone())
            .with_explicit_function_sections(self.sections.clone())
    }
}

/// The Pipeline input of `route` under `model`. The relocation-free route
/// gets no accessor.
pub(super) fn pipeline_input(route: Route, model: RelocationModel) -> PipelineInput {
    let prefix = route.prefix();
    let cases = route.cases();
    let mut input = PipelineInput {
        functions: Vec::new(),
        globals: Vec::new(),
        bindings: Vec::new(),
        weak_undefined: BTreeSet::new(),
        undefined_visibility: BTreeMap::new(),
        comdat: BTreeSet::new(),
        sections: BTreeMap::new(),
    };
    if route != Route::PipelineRelocationFree {
        input.globals.push(ObjectGlobal {
            mutable: false,
            visibility: Visibility::Hidden,
            ..object_global(
                &slot_target(route),
                SLOT_TARGET_VALUE.to_le_bytes().to_vec(),
            )
        });
    }
    for (ordinal, case) in cases.iter().enumerate() {
        let name = case.name(prefix);
        if case.kind != Kind::Function {
            input.globals.push(pipeline_global(*case, route, ordinal));
            continue;
        }
        if !case.defined() {
            input
                .undefined_visibility
                .insert(name.clone(), case.visibility);
            if case.link == Link::ExternalWeak {
                input.weak_undefined.insert(name);
            }
            continue;
        }
        input
            .functions
            .push(returns_constant(&name, case_value(ordinal) as i64));
        input.bindings.push(pipeline_binding(*case));
        if case.comdat() {
            input.comdat.insert(name.clone());
        }
        if let Some(section) = explicit_section(*case, route) {
            input.sections.insert(name, section);
        }
    }
    if route == Route::PipelineRelocationFree {
        return input;
    }
    for case in &cases {
        let name = case.name(prefix);
        if callable(*case) {
            input
                .functions
                .push(returns_call(&format!("call_{name}"), &name));
            input.bindings.push(FunctionSymbolBinding::GLOBAL);
        }
        input.functions.push(pipeline_address_accessor(
            *case,
            route,
            model,
            got_indirect(*case, model),
        ));
        input.bindings.push(FunctionSymbolBinding::GLOBAL);
    }
    input
}

/// Emit `route`'s object for `input` (sequential and parallel emission must
/// agree byte for byte).
pub(super) fn pipeline_object(
    route: Route,
    model: RelocationModel,
    function_sections: bool,
    opt_level: OptLevel,
    input: &PipelineInput,
) -> Vec<u8> {
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: LINUX.to_owned(),
        opt_level,
        relocation_model: model,
        ..PipelineConfig::default()
    })
    .with_function_sections(function_sections);
    let (functions, layouts) = prepare(&pipeline, &input.functions);
    let layouts: &[_] = if route == Route::PipelineUnwind {
        &layouts
    } else {
        &[]
    };
    let linkage = input.linkage();
    let label = format!("{route:?} {model} fs={function_sections}");
    let sequential = pipeline
        .compile_module_emission_with_symbol_linkage(&functions, &input.globals, layouts, &linkage)
        .unwrap_or_else(|error| panic!("{label}: {error}"))
        .into_emission()
        .object;
    let parallel = pipeline
        .compile_module_parallel_emission_with_symbol_linkage(
            &functions,
            &input.globals,
            layouts,
            &linkage,
        )
        .unwrap_or_else(|error| panic!("{label} parallel: {error}"))
        .into_emission()
        .object;
    assert!(
        parallel == sequential,
        "{label}: parallel and sequential emission differ"
    );
    sequential
}

// =============================================================================
// Object checks
// =============================================================================

/// `(sh_type, sh_flags)` per section header index, read from the headers.
fn section_attributes(bytes: &[u8]) -> Vec<(u32, u64)> {
    let shoff = rd_u64(bytes, 0x28) as usize;
    let shentsize = rd_u16(bytes, 0x3a) as usize;
    let shnum = rd_u16(bytes, 0x3c) as usize;
    (0..shnum)
        .map(|index| {
            let header = shoff + index * shentsize;
            (rd_u32(bytes, header + 4), rd_u64(bytes, header + 8))
        })
        .collect()
}

/// The emitter an object came from, told apart by what it carries.
fn assert_route_shape(elf: &Elf, attributes: &[(u32, u64)], route: Route, label: &str) {
    let eh_frame = elf.sections.iter().any(|(name, ..)| name == ".eh_frame");
    let rela = attributes.iter().any(|(sh_type, _)| *sh_type == SHT_RELA);
    let expected = match route {
        Route::Compiler | Route::PipelineUnwind => (true, true),
        Route::PipelineLayoutLess => (false, true),
        Route::PipelineRelocationFree => (false, false),
    };
    assert_eq!(
        (eh_frame, rela),
        expected,
        "{label}: `.eh_frame` and relocation sections of the {route:?} emitter"
    );
}

/// Every mismatch between `bytes` and the table's expectation for `cases`
/// on `route` under `model`, `function_sections`.
pub(super) fn table_mismatches(
    bytes: &[u8],
    cases: &[Case],
    route: Route,
    model: RelocationModel,
    function_sections: bool,
    label: &str,
) -> Vec<String> {
    let elf = parse_elf(bytes);
    let attributes = section_attributes(bytes);
    assert_route_shape(&elf, &attributes, route, label);
    let groups = comdat_groups(bytes);
    let prefix = route.prefix();
    let mut mismatches = Vec::new();
    let named_kinds = |name: &str| -> BTreeSet<u32> {
        elf.relocs
            .iter()
            .filter(|reloc| reloc.symbol == name && !reloc.section.starts_with(".debug"))
            .map(|reloc| reloc.kind)
            .collect()
    };
    for case in cases {
        let name = case.name(prefix);
        let found: Vec<&Sym> = elf.symbols.iter().filter(|s| s.name == name).collect();
        let references = route != Route::PipelineRelocationFree;
        if !case.defined() && !references {
            if !found.is_empty() {
                mismatches.push(format!(
                    "{name}: an unreferenced declaration emits a symbol: {found:?}"
                ));
            }
            continue;
        }
        let [symbol] = found.as_slice() else {
            mismatches.push(format!("{name}: expected one symbol, found {found:?}"));
            continue;
        };
        let (bind, sym_type) = if case.defined() {
            (
                match case.link {
                    Link::Internal => STB_LOCAL,
                    Link::External => STB_GLOBAL,
                    _ => STB_WEAK,
                },
                match case.kind {
                    Kind::Function => STT_FUNC,
                    kind if kind.tls() => STT_TLS,
                    _ => STT_OBJECT,
                },
            )
        } else {
            (
                if case.link == Link::ExternalWeak {
                    STB_WEAK
                } else {
                    STB_GLOBAL
                },
                if case.kind.tls() { STT_TLS } else { STT_NOTYPE },
            )
        };
        let expected = (
            bind,
            sym_type,
            stv(case.spelled_visibility()),
            case.defined(),
        );
        let actual = (
            symbol.bind,
            symbol.kind,
            symbol.visibility,
            symbol.shndx != 0,
        );
        if actual != expected {
            mismatches.push(format!(
                "{name}: (bind, type, visibility, defined) {actual:?}, expected {expected:?}"
            ));
        }
        if case.defined() {
            let placed = placement(*case, route, function_sections);
            let index = usize::from(symbol.shndx);
            let section = elf.sections.get(index).map(|(name, ..)| name.as_str());
            let attribute = attributes.get(index).copied();
            if section != Some(placed.name.as_str())
                || attribute != Some((placed.sh_type, placed.sh_flags))
            {
                mismatches.push(format!(
                    "{name}: section {section:?} {attribute:x?}, expected {} ({}, {:#x})",
                    placed.name, placed.sh_type, placed.sh_flags
                ));
            }
            let signatures: Vec<&str> = groups
                .iter()
                .filter(|(_, members)| members.contains(&placed.name))
                .map(|(signature, _)| signature.as_str())
                .collect();
            let expected_signatures: Vec<&str> = if placed.comdat {
                vec![name.as_str()]
            } else {
                vec![]
            };
            if signatures != expected_signatures {
                mismatches.push(format!(
                    "{name}: COMDAT signatures {signatures:?}, expected {expected_signatures:?}"
                ));
            }
            if case.kind != Kind::Function && symbol.size != 8 {
                mismatches.push(format!("{name}: st_size {}", symbol.size));
            }
            if case.kind == Kind::RelRo {
                let slot = slot_target(route);
                let slots = elf
                    .relocs
                    .iter()
                    .filter(|reloc| {
                        reloc.section == placed.name
                            && reloc.offset == symbol.value
                            && reloc.kind == R_AARCH64_ABS64
                            && reloc.symbol == slot
                    })
                    .count();
                if slots != 1 {
                    mismatches.push(format!(
                        "{name}: {slots} ABS64 slot relocation(s) against `{slot}` at its own offset"
                    ));
                }
            }
        }
        let anchor_name = elf_anchor_name(&name);
        let anchor: Vec<&Sym> = elf
            .symbols
            .iter()
            .filter(|s| s.name == anchor_name)
            .collect();
        if !references {
            if !named_kinds(&name).is_empty() || !anchor.is_empty() {
                mismatches.push(format!(
                    "{name}: the relocation-free route names it or anchors it"
                ));
            }
            continue;
        }
        let named = named_kinds(&name);
        if case.kind.tls() {
            let access = tls_access(*case, model);
            let expected_named: BTreeSet<u32> = match access {
                TlsAccess::LocalExec => BTreeSet::from(R_AARCH64_TLSLE),
                TlsAccess::InitialExec => BTreeSet::from(R_AARCH64_TLSIE),
                TlsAccess::Descriptor { anchored: false } => BTreeSet::from(R_AARCH64_TLSDESC),
                TlsAccess::Descriptor { anchored: true } => BTreeSet::new(),
            };
            if named != expected_named {
                mismatches.push(format!(
                    "{name}: {access:?} relocations naming it {named:?}, expected {expected_named:?}"
                ));
            }
            let anchored = access == TlsAccess::Descriptor { anchored: true };
            match (anchored, anchor.as_slice()) {
                (false, []) => {}
                (true, [anchor]) => {
                    let spelled = (
                        anchor.bind,
                        anchor.kind,
                        anchor.visibility,
                        anchor.shndx,
                        anchor.value,
                        anchor.size,
                    );
                    let wanted = (
                        STB_LOCAL,
                        STT_TLS,
                        STV_DEFAULT,
                        symbol.shndx,
                        symbol.value,
                        symbol.size,
                    );
                    let kinds = named_kinds(&anchor_name);
                    if spelled != wanted || kinds != BTreeSet::from(R_AARCH64_TLSDESC) {
                        mismatches.push(format!(
                            "{name}: anchor {spelled:?} named by {kinds:?}, expected {wanted:?} named by the descriptor"
                        ));
                    }
                }
                (anchored, found) => {
                    mismatches.push(format!("{name}: anchored={anchored}, anchors {found:?}"))
                }
            }
            continue;
        }
        if !anchor.is_empty() {
            mismatches.push(format!("{name}: a non-TLS symbol has an anchor"));
        }
        let got = got_indirect(*case, model);
        let pair = BTreeSet::from(if got { GOT_PAIR } else { DIRECT_PAIR });
        if case.kind == Kind::Function {
            let branches: BTreeSet<u32> = named
                .iter()
                .copied()
                .filter(|kind| [R_AARCH64_CALL26, R_AARCH64_JUMP26].contains(kind))
                .collect();
            let addresses: BTreeSet<u32> = named.difference(&branches).copied().collect();
            if addresses != pair {
                mismatches.push(format!(
                    "{name}: address relocations {addresses:?}, expected {pair:?} (GOT: {got})"
                ));
            }
            if callable(*case) && call_kept(*case, model, route) && branches.is_empty() {
                mismatches.push(format!("{name}: its call must stay a branch: {named:?}"));
            }
            if !callable(*case) && !branches.is_empty() {
                mismatches.push(format!("{name}: an uncallable declaration is branched to"));
            }
        } else if named != pair {
            mismatches.push(format!(
                "{name}: relocations naming it {named:?}, expected {pair:?} (GOT: {got})"
            ));
        }
    }
    mismatches
}

/// The object-local anchor name of a strong hidden thread-local.
fn elf_anchor_name(name: &str) -> String {
    format!(".Ltls.{name}")
}

// =============================================================================
// Object-level rows
// =============================================================================

/// The admitted, refused and inexpressible counts of the 1,008-case
/// cross-product: a classification change moves them.
const CLASS_COUNTS: (usize, usize, usize) = (337, 574, 97);

/// The body of the target's `visibility_table_classifies_the_whole_cross_product` row.
pub(super) fn classifies_the_whole_cross_product() {
    let cases = cross_product();
    assert_eq!(cases.len(), 2 * 8 * 3 * 7 * 3);
    let mut by_class: BTreeMap<Class, usize> = BTreeMap::new();
    for case in &cases {
        *by_class.entry(classify(*case)).or_default() += 1;
    }
    let admitted_count = by_class.get(&Class::Admitted).copied().unwrap_or(0);
    let refused: usize = by_class
        .iter()
        .filter(|(class, _)| matches!(class, Class::Refused(_)))
        .map(|(_, count)| count)
        .sum();
    let inexpressible = cases.len() - admitted_count - refused;
    eprintln!("visibility table classes: {by_class:#?}");
    assert_eq!(
        (admitted_count, refused, inexpressible),
        CLASS_COUNTS,
        "{by_class:#?}"
    );
    let module = table_module(&admitted());
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{errors:#?}");
}

/// Fail with every mismatch at once.
fn assert_no_mismatches(mismatches: &[String], label: &str) {
    assert!(
        mismatches.is_empty(),
        "{label}: {} mismatch(es):\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// The body of the target's `visibility_table_compiler_routes_spell_every_admitted_class` row.
pub(super) fn compiler_routes_spell_every_admitted_class() {
    let cases = Route::Compiler.cases();
    let module = table_module(&cases);
    assert_eq!(module.functions.len(), table_function_count(&cases));
    // `available_externally` bodies are never emitted.
    let emitted = module
        .functions
        .iter()
        .filter(|function| {
            !function.blocks.is_empty() && function.linkage != Linkage::AvailableExternally
        })
        .count();
    for model in RELOCATION_MODELS {
        for function_sections in [false, true] {
            for (parallel, opt_level) in OPT_LEVELS
                .into_iter()
                .flat_map(|opt_level| [(false, opt_level), (true, opt_level)])
            {
                let label = format!(
                    "Compiler {model} fs={function_sections} parallel={parallel} {opt_level:?}"
                );
                let result = table_compiler(opt_level, model, function_sections, parallel)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
                assert_emission_path(&result, parallel, emitted, &label);
                assert_no_mismatches(
                    &table_mismatches(
                        &result.object_code,
                        &cases,
                        Route::Compiler,
                        model,
                        function_sections,
                        &label,
                    ),
                    &label,
                );
            }
        }
    }
}

/// The body of the target's `visibility_table_pipeline_routes_spell_every_admitted_class` row.
pub(super) fn pipeline_routes_spell_every_admitted_class() {
    for route in [
        Route::PipelineUnwind,
        Route::PipelineLayoutLess,
        Route::PipelineRelocationFree,
    ] {
        let cases = route.cases();
        for model in RELOCATION_MODELS {
            let input = pipeline_input(route, model);
            for (function_sections, opt_level) in [
                (false, OptLevel::O0),
                (true, OptLevel::O0),
                (false, OptLevel::O2),
                (true, OptLevel::O2),
            ] {
                let label = format!("{route:?} {model} fs={function_sections} {opt_level:?}");
                let bytes = pipeline_object(route, model, function_sections, opt_level, &input);
                assert_no_mismatches(
                    &table_mismatches(&bytes, &cases, route, model, function_sections, &label),
                    &label,
                );
            }
        }
    }
}

/// The body of the target's `visibility_table_purity_reads_the_replacement_predicates` row.
pub(super) fn purity_reads_the_replacement_predicates() {
    let cases = Route::Compiler.cases();
    let module = table_module(&cases);
    let prefix = Route::Compiler.prefix();
    let mut rows = 0usize;
    for model in RELOCATION_MODELS {
        // The object path lowers only an ADMITTED module (WS7.3).
        // The table's fixtures carry no license (`body_gate: None`), refused
        // by default (WS7.5, DG-73); this row is about symbol binding, so it
        // states `Permit`.
        let admitted = trust_cg_lower::admit_module(
            &module,
            &trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
            &[],
        )
        .unwrap_or_else(|error| panic!("{model}: admission: {error}"));
        let (functions, _) =
            trust_cg_lower::translate_admitted_module_for_arch_with_access_model_and_stats(
                &admitted,
                trust_cg_lower::GuardCarrierArch::AArch64,
                trust_cg_lower::ObjectAccessModel::elf(model),
                trust_cg_lower::ObjectSymbolPolicy::AARCH64_ELF_MODULE,
            )
            .unwrap_or_else(|error| panic!("{model}: {error}"));
        let by_name: BTreeMap<&str, &LirFunction> = functions
            .iter()
            .map(|(function, _)| (function.name.as_str(), function))
            .collect();
        let mut wrong = Vec::new();
        // An `available_externally` body stands for a definition elsewhere;
        // its purity is not a visibility decision and is not asserted here.
        for case in cases.iter().filter(|case| {
            case.kind == Kind::Function
                && callable(**case)
                && case.link != Link::AvailableExternally
        }) {
            let name = case.name(prefix);
            let caller = by_name
                .get(format!("call_{name}").as_str())
                .unwrap_or_else(|| panic!("{model}: no LIR `call_{name}`"));
            let pure = case.defined()
                && !matches!(case.link, Link::Weak | Link::LinkOnce)
                && !got_indirect(*case, model);
            if caller.pure_callees.contains(&name) != pure {
                wrong.push(format!(
                    "{name}: pure={pure}, pure_callees={:?}",
                    caller.pure_callees
                ));
            }
            rows += 1;
        }
        assert_no_mismatches(&wrong, &format!("purity {model}"));
    }
    assert_eq!(rows, 3 * 45, "purity rows");
}

/// Compile a one-case table module under `model`.
fn compile_one(case: Case, model: RelocationModel) -> Result<Vec<u8>, String> {
    table_compiler(OptLevel::O0, model, false, false)
        .compile(&table_module(&[case]))
        .map(|result| result.object_code)
        .map_err(|error| error.to_string())
}

/// A pruned case is refused by name: by trust-ir's own first admission
/// finding when trust-ir refuses the case's module (since WS7.3 ingestion
/// admission runs before any backend arm: `ContradictoryFunctionVisibility`,
/// `EmptyFunction`, ...), else by the backend's `diagnostic`. trust-ir judges
/// the module under the license policy [`table_compiler`] states (`Permit`):
/// under the default policy every claim-less fixture would carry an
/// `UnlicensedBodyForCodegen` finding that [`compile_one`] never raises.
fn assert_refused_by_name(case: Case, model: RelocationModel, error: &str, diagnostic: &str) {
    match super::admission_expect::names_first_finding(
        &table_module(&[case]),
        error,
        &permit_unlicensed(),
    ) {
        Some(named) => assert!(named, "{case:?} {model}: trust-ir's finding: {error}"),
        None => assert!(
            error.contains(diagnostic),
            "{case:?} {model}: expected `{diagnostic}`: {error}"
        ),
    }
}

/// The body of the target's `visibility_table_pruned_combinations_are_refused_by_name` row.
pub(super) fn pruned_combinations_are_refused_by_name() {
    let mut seen: BTreeMap<Class, usize> = BTreeMap::new();
    for case in cross_product() {
        let class = classify(case);
        *seen.entry(class).or_default() += 1;
        let name = case.name(Route::Compiler.prefix());
        match class {
            Class::Admitted => {}
            Class::Refused(Refusal::BodylessDefinitionLinkage) => {
                let module = table_module(&[case]);
                let errors = trust_ir_build::validate_module(&module);
                assert!(
                    errors
                        .iter()
                        .any(|error| error.to_string().contains("function has no blocks")),
                    "{case:?}: trust-ir's validator must refuse `{name}`: {errors:?}"
                );
                for model in [RelocationModel::Static, RelocationModel::Pic] {
                    let error = compile_one(case, model).expect_err(&format!(
                        "{case:?} {model}: the backend compiled a bodyless `{}` function",
                        case.link.keyword()
                    ));
                    assert_refused_by_name(
                        case,
                        model,
                        &error,
                        Refusal::BodylessDefinitionLinkage.diagnostic(),
                    );
                }
            }
            Class::Refused(refusal) => {
                for model in [RelocationModel::Static, RelocationModel::Pic] {
                    let error = compile_one(case, model)
                        .expect_err(&format!("{case:?} {model}: must be refused ({refusal:?})"));
                    assert_refused_by_name(case, model, &error, refusal.diagnostic());
                }
            }
            Class::Inexpressible(reason) => {
                for model in [RelocationModel::Static, RelocationModel::Pic] {
                    let bytes = compile_one(case, model)
                        .unwrap_or_else(|error| panic!("{case:?} {model} ({reason:?}): {error}"));
                    let elf = parse_elf(&bytes);
                    let symbol = elf.symbol(&name);
                    let section = &elf.sections[usize::from(symbol.shndx)].0;
                    let spelled = (symbol.bind, symbol.visibility, symbol.shndx != 0);
                    let expected = match reason {
                        Inexpressible::InternalDeclarationIsDefinition => {
                            let placed =
                                explicit_section(case, Route::Compiler).unwrap_or_else(|| {
                                    if case.kind.mutable() {
                                        ".bss"
                                    } else {
                                        ".rodata"
                                    }
                                    .to_string()
                                });
                            assert_eq!(section, &placed, "{case:?} {model}: {symbol:?}");
                            (STB_LOCAL, STV_DEFAULT, true)
                        }
                        Inexpressible::AvailableExternallyDefinition
                        | Inexpressible::DeclarationHasNoInitializer => {
                            let bind = if case.link == Link::ExternalWeak {
                                STB_WEAK
                            } else {
                                STB_GLOBAL
                            };
                            let kind = match case.kind {
                                kind if kind.tls() => STT_TLS,
                                _ => STT_NOTYPE,
                            };
                            assert_eq!(symbol.kind, kind, "{case:?} {model}: {symbol:?}");
                            (bind, stv(case.visibility), false)
                        }
                    };
                    assert_eq!(
                        spelled, expected,
                        "{case:?} {model} ({reason:?}): {symbol:?}"
                    );
                }
            }
        }
    }
    eprintln!("visibility table pruning checked: {seen:#?}");

    // A pointer slot gives the layout-less API the relocating emitter even
    // without a text fixup, so the relocation-free route never carries one.
    let pointer = Case {
        role: Role::Definition,
        link: Link::External,
        visibility: Visibility::Hidden,
        kind: Kind::RelRo,
        place: Place::Implicit,
    };
    let pipeline = pipeline(LINUX, OptLevel::O0);
    let (functions, _) = prepare(&pipeline, &[returns_constant("leaf", 1)]);
    let globals = vec![
        ObjectGlobal {
            mutable: false,
            visibility: Visibility::Hidden,
            ..object_global(
                &slot_target(Route::PipelineRelocationFree),
                SLOT_TARGET_VALUE.to_le_bytes().to_vec(),
            )
        },
        pipeline_global(pointer, Route::PipelineRelocationFree, 0),
    ];
    let bytes = pipeline
        .compile_module_with_globals(&functions, &globals)
        .expect("a pointer-bearing global without fixups");
    let elf = parse_elf(&bytes);
    assert_route_shape(
        &elf,
        &section_attributes(&bytes),
        Route::PipelineLayoutLess,
        "pointer slot without fixups",
    );
}

/// What the emitters' relocation-model backstop must answer for a
/// PC-relative reference to `case` under `model`: `None` when it compiles,
/// else the reason it names.
fn backstop_refusal(case: Case, model: RelocationModel) -> Option<&'static str> {
    if case.kind == Kind::Function && !case.defined() {
        return Some(if case.link == Link::ExternalWeak {
            "a weak undefined symbol"
        } else {
            "a declared function (visibility"
        });
    }
    if !case.defined() {
        return if case.link == Link::ExternalWeak {
            Some("a weak undefined symbol")
        } else if case.visibility != Visibility::Default {
            Some("a data import (visibility")
        } else if model == RelocationModel::Pic {
            Some("an undefined symbol, PC-relatively; its address must be loaded from the GOT")
        } else {
            // A default strong data import may be copy-relocated into an
            // executable, which its PC-relative link resolves.
            None
        };
    }
    if got_indirect(case, model) {
        return Some(if case.kind == Kind::Function {
            "a preemptible function definition, PC-relatively; its address must be loaded from the GOT"
        } else {
            "a preemptible data definition, PC-relatively; its address must be loaded from the GOT"
        });
    }
    None
}

/// The body of the target's `visibility_table_backstop_refuses_every_forbidden_pc_relative_address` row.
pub(super) fn backstop_refuses_every_forbidden_pc_relative_address() {
    let mut refused = 0usize;
    let mut compiled = 0usize;
    for route in [Route::PipelineUnwind, Route::PipelineLayoutLess] {
        let prefix = route.prefix();
        for model in RELOCATION_MODELS {
            let pipeline = Pipeline::new(PipelineConfig {
                target_triple: LINUX.to_owned(),
                opt_level: OptLevel::O0,
                relocation_model: model,
                ..PipelineConfig::default()
            });
            for (ordinal, case) in route.cases().into_iter().enumerate() {
                let name = case.name(prefix);
                let label = format!("{route:?} {model} `{name}`");
                let mut functions = Vec::new();
                let mut bindings = Vec::new();
                let mut globals = Vec::new();
                let mut undefined_visibility = BTreeMap::new();
                let mut weak_undefined = BTreeSet::new();
                if case.kind == Kind::Function {
                    if case.defined() {
                        functions.push(returns_constant(&name, 1));
                        bindings.push(pipeline_binding(case));
                    } else {
                        undefined_visibility.insert(name.clone(), case.visibility);
                        if case.link == Link::ExternalWeak {
                            weak_undefined.insert(name.clone());
                        }
                    }
                } else {
                    if case.kind == Kind::RelRo && case.defined() {
                        globals.push(object_global(&slot_target(route), vec![0; 8]));
                    }
                    globals.push(pipeline_global(case, route, ordinal));
                }
                let (accessor, expected) = if case.kind.tls() {
                    if model != RelocationModel::Pic {
                        continue;
                    }
                    let executable = if case.defined() {
                        trust_cg_ir::TlsModel::LocalExec
                    } else {
                        trust_cg_ir::TlsModel::InitialExec
                    };
                    (
                        returns_tls_ref(&format!("addr_{name}"), &name, executable),
                        Some("uses the executable-only TLS model"),
                    )
                } else {
                    (
                        pipeline_address_accessor(case, route, model, false),
                        backstop_refusal(case, model),
                    )
                };
                functions.push(accessor);
                bindings.push(FunctionSymbolBinding::GLOBAL);
                let comdat: BTreeSet<String> = if case.comdat() && case.kind == Kind::Function {
                    BTreeSet::from([name.clone()])
                } else {
                    BTreeSet::new()
                };
                let sections: BTreeMap<String, String> = explicit_section(case, route)
                    .filter(|_| case.kind == Kind::Function)
                    .map(|section| BTreeMap::from([(name.clone(), section)]))
                    .unwrap_or_default();
                let linkage = ModuleSymbolLinkage::new(bindings, weak_undefined)
                    .with_undefined_function_visibility(undefined_visibility)
                    .with_comdat_functions(comdat)
                    .with_explicit_function_sections(sections);
                let (prepared, layouts) = prepare(&pipeline, &functions);
                let layouts: &[_] = if route == Route::PipelineUnwind {
                    &layouts
                } else {
                    &[]
                };
                let result = pipeline.compile_module_emission_with_symbol_linkage(
                    &prepared, &globals, layouts, &linkage,
                );
                match (expected, result) {
                    (None, Ok(_)) => compiled += 1,
                    (Some(reason), Err(error)) => {
                        let error = error.to_string();
                        assert!(
                            error.contains(reason) && error.contains(&format!("`{name}`")),
                            "{label}: expected `{reason}`: {error}"
                        );
                        refused += 1;
                    }
                    (None, Err(error)) => panic!("{label}: must compile: {error}"),
                    (Some(reason), Ok(_)) => panic!("{label}: must be refused with `{reason}`"),
                }
            }
        }
    }
    eprintln!("backstop rows: {refused} refused, {compiled} compiled");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
