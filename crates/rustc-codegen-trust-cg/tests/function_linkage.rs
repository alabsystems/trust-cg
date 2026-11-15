//! Structural checks for the bridge's split-CGU symbol namespace.
#[path = "../src/function_linkage.rs"]
mod function_linkage;

use function_linkage::{CguSymbols, PrivateSymbolFormat};
use std::collections::HashSet;
use trust_ir::*;

fn plan(cgu: &str) -> CguSymbols {
    let mut plan = CguSymbols::default();
    plan.insert(
        cgu,
        0,
        "helper".into(),
        Linkage::Internal,
        Visibility::Default,
    )
    .unwrap();
    plan.insert(cgu, 1, "api".into(), Linkage::External, Visibility::Default)
        .unwrap();
    plan
}

fn fixture() -> Module {
    let mut m = Module::new("fixture");
    let ty = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut api = Function::new(FuncId::new(0), "api", ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(1),
        args: vec![],
    }));
    block.body.push(InstrNode::new(Inst::Const {
        ty: Ty::Func(ty),
        value: Constant::FnDef(FuncId::new(1)),
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    api.blocks.push(block);
    m.try_add_function(api)
        .expect("Module::try_add_function: test fixture");
    m.try_add_function(Function::new(FuncId::new(1), "helper", ty, BlockId::new(0)))
        .expect("Module::try_add_function: test fixture");
    m.globals.push(Global {
        name: "callback".into(),
        ty: Ty::Func(ty),
        mutable: false,
        initializer: Some(Constant::SymbolAddr {
            symbol: "helper".into(),
            addend: -7,
        }),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: true,
    });
    m
}

#[test]
fn declarations_addresses_and_public_abi_preserve_ids_and_offsets() {
    let mut m = fixture();
    let before = m.clone();
    plan("crate.cgu.0").apply(&mut m).unwrap();
    assert_eq!(m.functions[0], before.functions[0]);
    assert_eq!(m.functions[1].name, "__trust_cg_private.crate.cgu.0.0");
    assert_eq!(m.functions[1].linkage, Linkage::External);
    assert_eq!(m.functions[1].visibility, Visibility::Hidden);
    assert_eq!(
        m.globals[0].initializer,
        Some(Constant::SymbolAddr {
            symbol: "__trust_cg_private.crate.cgu.0.0".into(),
            addend: -7,
        })
    );
    // Restore only the documented spelling/visibility edits: every other IR
    // field, instruction, identifier and data-layout attribute must be exact.
    m.functions[1].name.clone_from(&before.functions[1].name);
    m.functions[1].visibility = before.functions[1].visibility;
    m.globals[0]
        .initializer
        .clone_from(&before.globals[0].initializer);
    assert_eq!(m, before);
}

#[test]
fn split_definition_resolves_to_the_same_hidden_name() {
    let mut definition = fixture();
    definition.functions[1]
        .blocks
        .push(Block::new(BlockId::new(0)));
    let mut caller = fixture();
    let p = plan("a.cgu.1");
    p.apply(&mut definition).unwrap();
    p.apply(&mut caller).unwrap();
    assert_eq!(definition.functions[1].name, caller.functions[1].name);
    assert_eq!(definition.functions[1].visibility, Visibility::Hidden);
    let mut other = fixture();
    plan("a.cgu.2").apply(&mut other).unwrap();
    assert_ne!(other.functions[1].name, caller.functions[1].name);
}

#[test]
fn nested_constant_containers_are_renamed_without_changing_payloads() {
    let address = Constant::SymbolAddr {
        symbol: "helper".into(),
        addend: 11,
    };
    let mut m = fixture();
    let constant = Constant::Record(vec![(
        "slot".into(),
        Constant::Closure {
            func: FuncId::new(1),
            captures: vec![Constant::Aggregate(vec![Constant::Array(vec![
                Constant::Vector(vec![Constant::Sequence(vec![Constant::Set(vec![address])])]),
            ])])],
        },
    )]);
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: constant.clone(),
        }));
    m.globals[0].initializer = Some(constant);
    plan("nested").apply(&mut m).unwrap();
    let mut count = 0;
    let mut check = |c: &Constant| {
        if let Constant::SymbolAddr { symbol, addend } = c {
            assert_eq!(symbol, "__trust_cg_private.nested.0");
            assert_eq!(*addend, 11);
            count += 1;
        }
    };
    if let Inst::Const { value, .. } = &m.functions[0].blocks[0].body.last().unwrap().inst {
        value.visit_constants(&mut check);
    } else {
        panic!("missing nested constant")
    }
    m.globals[0]
        .initializer
        .as_ref()
        .unwrap()
        .visit_constants(&mut check);
    assert_eq!(count, 2);
}

#[test]
fn collisions_refuse_before_mutation() {
    for kind in 0..4 {
        let p = plan("collision");
        let mut m = fixture();
        match kind {
            0 => m.functions[0].name = p.emitted("helper").to_owned(),
            1 => m.globals[0].name = p.emitted("helper").to_owned(),
            2 => {
                m.globals[0].initializer = Some(Constant::SymbolAddr {
                    symbol: "__trust_cg_private.other.0".into(),
                    addend: 0,
                })
            }
            3 => m.globals[0].name = "helper".into(),
            _ => unreachable!(),
        }
        let before = m.clone();
        assert!(p.apply(&mut m).unwrap_err().contains("collides"));
        assert_eq!(m, before);
    }
    let p = plan("collision");
    assert!(
        p.check_collected_names(&HashSet::from([p.emitted("helper").into()]))
            .is_err()
    );
}

#[test]
fn opaque_contracts_and_assembly_refuse_before_mutation() {
    for assembly in [false, true] {
        let mut m = fixture();
        if assembly {
            m.global_asm.push("call helper".into());
        } else {
            m.functions[0].summary =
                Some(FunctionSummary::new().requiring(ProofFormula::smtlib2("helper", "Bool")));
        }
        let before = m.clone();
        assert!(plan("proof").apply(&mut m).is_err());
        assert_eq!(m, before);
    }
}

#[test]
fn explicit_linkage_visibility_and_unplanned_symbols_are_preserved() {
    for linkage in [
        Linkage::External,
        Linkage::Weak,
        Linkage::WeakOdr,
        Linkage::LinkOnce,
        Linkage::LinkOnceOdr,
    ] {
        let mut p = CguSymbols::default();
        p.insert("weak", 0, "api".into(), linkage, Visibility::Protected)
            .unwrap();
        let mut m = fixture();
        let helper = m.functions[1].clone();
        p.apply(&mut m).unwrap();
        assert_eq!(m.functions[0].name, "api");
        assert_eq!(m.functions[0].linkage, linkage);
        assert_eq!(m.functions[0].visibility, Visibility::Protected);
        assert_eq!(m.functions[1], helper);
    }
}

#[test]
fn duplicate_names_and_private_personality_refuse() {
    let mut p = plan("duplicates");
    assert!(
        p.insert(
            "duplicates",
            2,
            "helper".into(),
            Linkage::External,
            Visibility::Default
        )
        .is_err()
    );
    assert!(
        CguSymbols::default()
            .insert(
                "eh",
                0,
                "rust_eh_personality".into(),
                Linkage::Internal,
                Visibility::Default
            )
            .is_err()
    );
    assert!(
        CguSymbols::default()
            .insert(
                "reserved",
                0,
                "__trust_cg_private.other.0".into(),
                Linkage::External,
                Visibility::Default
            )
            .is_err()
    );
}

#[test]
fn a_static_only_cgu_still_rejects_imports_in_the_private_namespace() {
    let mut m = fixture();
    m.functions.clear();
    m.globals[0].initializer = Some(Constant::SymbolAddr {
        symbol: "__trust_cg_private.other-cgu.1".into(),
        addend: 0,
    });
    assert!(
        CguSymbols::enabled()
            .apply(&mut m)
            .unwrap_err()
            .starts_with(function_linkage::REFUSAL_PREFIX)
    );
}

/// Every rustc linkage is carried 1:1, emits no definition (only
/// `available_externally`, as in LLVM) or is refused as `[TCG-LINKAGE]`
/// (ledger L06-P7); a function and a static share the one map.
#[test]
fn every_rustc_definition_linkage_is_carried_omitted_or_refused_by_name() {
    use function_linkage::{
        LINKAGE_REFUSAL, RustcLinkage, function_definition_linkage, is_weak_definition,
        static_definition_linkage,
    };
    let carried = [
        (RustcLinkage::External, Linkage::External, false),
        (RustcLinkage::Internal, Linkage::Internal, false),
        (RustcLinkage::LinkOnceAny, Linkage::LinkOnce, true),
        (RustcLinkage::LinkOnceOdr, Linkage::LinkOnceOdr, true),
        (RustcLinkage::WeakAny, Linkage::Weak, true),
        (RustcLinkage::WeakOdr, Linkage::WeakOdr, true),
    ];
    for (rustc, trust_ir, weak) in carried {
        assert_eq!(function_definition_linkage("f", rustc), Ok(Some(trust_ir)));
        assert_eq!(static_definition_linkage("s", rustc), Ok(trust_ir));
        assert_eq!(is_weak_definition(trust_ir), weak, "{rustc:?}");
    }
    assert_eq!(
        function_definition_linkage("f", RustcLinkage::AvailableExternally),
        Ok(None)
    );
    for rustc in [RustcLinkage::Common, RustcLinkage::ExternalWeak] {
        let refusal = function_definition_linkage("f", rustc).unwrap_err();
        assert!(
            refusal.starts_with(&format!("{LINKAGE_REFUSAL} function `f` has rustc linkage")),
            "{refusal}"
        );
    }
    for rustc in [
        RustcLinkage::AvailableExternally,
        RustcLinkage::Common,
        RustcLinkage::ExternalWeak,
    ] {
        let refusal = static_definition_linkage("s", rustc).unwrap_err();
        assert!(
            refusal.starts_with(&format!("{LINKAGE_REFUSAL} static `s` has rustc linkage")),
            "{refusal}"
        );
    }
    for linkage in [
        Linkage::Private,
        Linkage::AvailableExternally,
        Linkage::ExternalWeak,
    ] {
        assert!(!is_weak_definition(linkage), "{linkage:?}");
    }
}

/// Mach-O (Apple AArch64): the private definition is hidden `External`
/// (`N_EXT | N_PEXT`) under `__trust_cg_private.<cgu>.<index>.<rustc symbol>`,
/// a sibling object's declaration of it is a plain default-visibility
/// undefined reference (Mach-O spells no visibility there), and a
/// non-`Internal` function keeps its name while its definition gets rustc's
/// linkage and visibility (ledger L06-P7).
#[test]
fn macho_private_definitions_are_hidden_and_their_references_plain() {
    let mut plan = CguSymbols::enabled_for(PrivateSymbolFormat::MachO);
    plan.insert(
        "crate.cgu.0",
        3,
        "helper".into(),
        Linkage::Internal,
        Visibility::Default,
    )
    .unwrap();
    plan.insert(
        "crate.cgu.0",
        4,
        "api".into(),
        Linkage::External,
        Visibility::Hidden,
    )
    .unwrap();
    assert_eq!(
        plan.emitted("helper"),
        "__trust_cg_private.crate.cgu.0.3.helper"
    );
    assert_eq!(plan.emitted("api"), "api");

    let mut definition = fixture();
    definition.functions[1]
        .blocks
        .push(Block::new(BlockId::new(0)));
    let mut caller = fixture();
    let before = caller.functions[0].clone();
    plan.apply(&mut definition).unwrap();
    plan.apply(&mut caller).unwrap();
    let defined = &definition.functions[1];
    assert_eq!(
        (defined.name.as_str(), defined.linkage, defined.visibility),
        (
            "__trust_cg_private.crate.cgu.0.3.helper",
            Linkage::External,
            Visibility::Hidden
        )
    );
    let declared = &caller.functions[1];
    assert_eq!(
        (
            declared.name.as_str(),
            declared.linkage,
            declared.visibility
        ),
        (
            "__trust_cg_private.crate.cgu.0.3.helper",
            Linkage::External,
            Visibility::Default
        )
    );
    // `api` is planned External + hidden by rustc: Mach-O keeps its name and
    // carries the hidden visibility onto its definition (`N_PEXT`, L06-P7);
    // nothing else of it changes.
    let api = &caller.functions[0];
    assert_eq!(
        (api.name.as_str(), api.linkage, api.visibility),
        ("api", Linkage::External, Visibility::Hidden)
    );
    let mut unchanged = api.clone();
    unchanged.visibility = before.visibility;
    assert_eq!(unchanged, before);
    // A weak definition keeps its weak linkage on Mach-O (`N_WEAK_DEF`).
    let mut weak = CguSymbols::enabled_for(PrivateSymbolFormat::MachO);
    weak.insert(
        "crate.cgu.0",
        0,
        "api".into(),
        Linkage::Weak,
        Visibility::Default,
    )
    .unwrap();
    let mut weak_module = fixture();
    weak.apply(&mut weak_module).unwrap();
    assert_eq!(
        (
            weak_module.functions[0].name.as_str(),
            weak_module.functions[0].linkage
        ),
        ("api", Linkage::Weak)
    );
    // Two CGUs' copies of one rustc symbol never share a name.
    let mut other = CguSymbols::enabled_for(PrivateSymbolFormat::MachO);
    other
        .insert(
            "crate.cgu.1",
            3,
            "helper".into(),
            Linkage::Internal,
            Visibility::Default,
        )
        .unwrap();
    assert_ne!(other.emitted("helper"), plan.emitted("helper"));
}

/// Which targets use the CGU-private namespace, and in which spelling: AArch64
/// and x86-64 Linux as ELF (x86-64 since ruling
/// OD-X86-BRIDGE-ELF-PRIVATE-ROUTE-20261106, once that emitter spelled an
/// undefined symbol's visibility and so could carry this route's hidden
/// DECLARATIONS), Apple AArch64 and x86-64 as Mach-O (both Mach-O module
/// emitters write a hidden `External` definition as a private extern), and no
/// other target — COFF and the remaining ELF targets, RISC-V Linux among
/// them, spell no function visibility, so they keep rustc's names.
#[test]
fn private_namespace_targets_are_linux_elf_and_apple_aarch64_and_x86_64() {
    // (arch, is_linux, is_like_darwin) -> format
    for (arch, linux, darwin, format) in [
        ("aarch64", true, false, Some(PrivateSymbolFormat::Elf)),
        // x86-64 Linux joined the ELF namespace once its module emitter
        // spelled an undefined symbol's visibility, which is what the ELF
        // route's hidden DECLARATIONS need
        // (OD-X86-ELF-UNDEFINED-REFERENCE-20261106).
        ("x86_64", true, false, Some(PrivateSymbolFormat::Elf)),
        ("aarch64", false, true, Some(PrivateSymbolFormat::MachO)),
        ("x86_64", false, true, Some(PrivateSymbolFormat::MachO)),
        ("x86_64", false, false, None),
        ("aarch64", false, false, None),
        ("riscv64", true, false, None),
        ("x86", false, true, None),
        ("arm", false, true, None),
    ] {
        assert_eq!(
            PrivateSymbolFormat::for_target(arch, linux, darwin),
            format,
            "{arch} linux={linux} darwin={darwin}"
        );
    }
}

/// The function symbol route of each target: the private namespace where it
/// exists (both Linux ELF architectures and Apple AArch64/x86-64), wasm32's
/// own placement lane, and the unspelled route everywhere else (COFF and
/// bare-metal ELF among them).
#[test]
fn function_symbol_routes_are_private_wasm32_or_unspelled() {
    use function_linkage::FunctionSymbolRoute;
    for (arch, linux, darwin, route) in [
        (
            "aarch64",
            true,
            false,
            FunctionSymbolRoute::Private(PrivateSymbolFormat::Elf),
        ),
        (
            "aarch64",
            false,
            true,
            FunctionSymbolRoute::Private(PrivateSymbolFormat::MachO),
        ),
        (
            "x86_64",
            false,
            true,
            FunctionSymbolRoute::Private(PrivateSymbolFormat::MachO),
        ),
        (
            "x86_64",
            true,
            false,
            FunctionSymbolRoute::Private(PrivateSymbolFormat::Elf),
        ),
        ("wasm32", false, false, FunctionSymbolRoute::Wasm32),
        ("x86_64", false, false, FunctionSymbolRoute::Unspelled),
        ("aarch64", false, false, FunctionSymbolRoute::Unspelled),
    ] {
        assert_eq!(
            FunctionSymbolRoute::for_target(arch, linux, darwin),
            route,
            "{arch} linux={linux} darwin={darwin}"
        );
    }
}

/// On the unspelled route only a strong default-visible definition is
/// emitted as rustc asked; every other binding is refused by name, naming
/// the function and the requested binding (ruling
/// OD-BRIDGE-UNSPELLED-BINDING-20261024).
#[test]
fn unspelled_route_refuses_every_function_binding_it_cannot_spell_by_name() {
    use function_linkage::{
        LINKAGE_REFUSAL, RustcLinkage, VISIBILITY_REFUSAL, function_definition_linkage,
        unspelled_function_definition_refusal,
    };
    let triple = "x86_64-unknown-linux-gnu";
    let refusal = |rustc: RustcLinkage, visibility: Visibility| {
        let linkage = function_definition_linkage("f", rustc).unwrap().unwrap();
        unspelled_function_definition_refusal(triple, "f", rustc, linkage, visibility)
    };
    assert_eq!(refusal(RustcLinkage::External, Visibility::Default), None);
    for rustc in [
        RustcLinkage::LinkOnceAny,
        RustcLinkage::LinkOnceOdr,
        RustcLinkage::WeakAny,
        RustcLinkage::WeakOdr,
    ] {
        for visibility in [Visibility::Default, Visibility::Hidden] {
            let text = refusal(rustc, visibility).expect("weak definition admitted");
            assert!(
                text.starts_with(&format!(
                    "{LINKAGE_REFUSAL} function `f` has rustc linkage {rustc:?}, which the \
                     {triple} function emission does not carry (every definition is strong)"
                )),
                "{text}"
            );
        }
    }
    for visibility in [
        Visibility::Default,
        Visibility::Hidden,
        Visibility::Protected,
    ] {
        let text = refusal(RustcLinkage::Internal, visibility).expect("Internal admitted");
        assert!(
            text.starts_with(&format!(
                "{LINKAGE_REFUSAL} function `f` has rustc linkage Internal (local to its codegen \
                 unit), which the {triple} function emission does not carry"
            )),
            "{text}"
        );
    }
    for (visibility, spelled) in [
        (Visibility::Hidden, "hidden"),
        (Visibility::Protected, "protected"),
    ] {
        let text = refusal(RustcLinkage::External, visibility).expect("visibility admitted");
        assert!(
            text.starts_with(&format!(
                "{VISIBILITY_REFUSAL} function `f` has rustc visibility {spelled} (linkage \
                 External), which the {triple} function emission does not carry"
            )),
            "{text}"
        );
    }
}

/// A synthesized definition (allocator wrapper or marker, C `main`) takes the
/// session's default visibility where the route carries it, and is refused
/// by name for hidden or protected where it does not.
#[test]
fn synthesized_definitions_take_the_session_visibility_or_refuse_by_name() {
    use function_linkage::{
        FunctionSymbolRoute, VISIBILITY_REFUSAL, synthesized_definition_visibility,
    };
    let visibilities = [
        Visibility::Default,
        Visibility::Hidden,
        Visibility::Protected,
    ];
    for route in [
        FunctionSymbolRoute::Private(PrivateSymbolFormat::Elf),
        FunctionSymbolRoute::Private(PrivateSymbolFormat::MachO),
        FunctionSymbolRoute::Wasm32,
    ] {
        for requested in visibilities {
            assert_eq!(
                synthesized_definition_visibility(route, "t", "main", requested),
                Ok(requested),
                "{route:?}"
            );
        }
    }
    let unspelled = FunctionSymbolRoute::Unspelled;
    assert_eq!(
        synthesized_definition_visibility(unspelled, "t", "main", Visibility::Default),
        Ok(Visibility::Default)
    );
    for requested in [Visibility::Hidden, Visibility::Protected] {
        let text = synthesized_definition_visibility(
            unspelled,
            "x86_64-unknown-linux-gnu",
            "main",
            requested,
        )
        .unwrap_err();
        assert!(
            text.starts_with(&format!(
                "{VISIBILITY_REFUSAL} synthesized function `main`: the session's default \
                 visibility is {requested}"
            )) && text.contains("x86_64-unknown-linux-gnu"),
            "{text}"
        );
    }
}

/// The allocator shim's `__rdl_*` declaration is hidden where an undefined
/// symbol carries a visibility (ELF, wasm32), default on Mach-O (an undefined
/// symbol there carries none, so LLVM's hidden declaration is written the
/// same way), and refused by name on the unspelled route.
#[test]
fn allocator_callee_declaration_is_hidden_where_spelled_and_refused_elsewhere() {
    use function_linkage::{
        FunctionSymbolRoute, VISIBILITY_REFUSAL, allocator_callee_declaration_visibility,
    };
    for (route, expected) in [
        (
            FunctionSymbolRoute::Private(PrivateSymbolFormat::Elf),
            Visibility::Hidden,
        ),
        (FunctionSymbolRoute::Wasm32, Visibility::Hidden),
        (
            FunctionSymbolRoute::Private(PrivateSymbolFormat::MachO),
            Visibility::Default,
        ),
    ] {
        assert_eq!(
            allocator_callee_declaration_visibility(route, "t", "__rdl_alloc"),
            Ok(expected),
            "{route:?}"
        );
    }
    let text = allocator_callee_declaration_visibility(
        FunctionSymbolRoute::Unspelled,
        "x86_64-unknown-linux-gnu",
        "__rdl_alloc",
    )
    .unwrap_err();
    assert!(
        text.starts_with(&format!(
            "{VISIBILITY_REFUSAL} the allocator shim's callee `__rdl_alloc` is a hidden \
             declaration"
        )) && text.contains("x86_64-unknown-linux-gnu"),
        "{text}"
    );
}
