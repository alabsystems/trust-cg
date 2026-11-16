// Detect selected compiler APIs without turning unrelated failures into absence.
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[path = "build_support/probe.rs"]
mod probe;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=build_support/probe.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed=PATH");
    println!("cargo:rerun-if-env-changed=RUSTUP_TOOLCHAIN");
    println!("cargo:rerun-if-env-changed=RUSTUP_HOME");
    println!("cargo:rerun-if-env-changed=RUSTFLAGS");
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo:rustc-check-cfg=cfg(rustc_middle_mir_mono)");
    println!("cargo:rustc-check-cfg=cfg(trust_ir_cg_args)");
    println!("cargo:rustc-check-cfg=cfg(rustc_attr_ir_lang_items)");
    println!("cargo:rustc-check-cfg=cfg(rustc_canonical_memory_symbols)");
    println!("cargo:rustc-check-cfg=cfg(rustc_attr_ir_attributes)");
    println!("cargo:rustc-check-cfg=cfg(rustc_linkage_common)");
    println!("cargo:rustc-check-cfg=cfg(rustc_compiled_module_cache_links)");
    println!("cargo:rustc-check-cfg=cfg(rustc_structures_crate_type)");
    println!("cargo:rustc-check-cfg=cfg(rustc_codegen_sample_profile)");
    println!("cargo:rustc-check-cfg=cfg(rustc_scalar_pair_struct)");
    println!("cargo:rustc-check-cfg=cfg(rustc_cast_pad_count)");
    println!("cargo:rustc-check-cfg=cfg(rustc_session_split)");
    println!("cargo:rustc-check-cfg=cfg(rustc_indirect_modes)");
    println!("cargo:rustc-check-cfg=cfg(rustc_extended_float_formats)");
    println!("cargo:rustc-check-cfg=cfg(rustc_ppc_f128_register)");
    println!("cargo:rustc-check-cfg=cfg(rustc_scalar_direct_pointer)");
    println!("cargo:rustc-check-cfg=cfg(rustc_terminator_attributes)");
    println!("cargo:rustc-check-cfg=cfg(rustc_goto_loop_hints)");
    println!("cargo:rustc-check-cfg=cfg(rustc_backend_lane_count)");
    println!("cargo:rustc-check-cfg=cfg(rustc_bound_fn_args)");
    println!("cargo:rustc-check-cfg=cfg(rustc_generic_args_value)");
    println!("cargo:rustc-check-cfg=cfg(rustc_super_clauses_query)");
    println!("cargo:rustc-check-cfg=cfg(rustc_own_clauses_query)");
    println!("cargo:rustc-check-cfg=cfg(rustc_box_deref_facts)");

    // Integration tests must load this dylib into the compiler that built it.
    // A linked rustup `trust` may differ from the installed Trust pack on PATH.
    let compiler = resolve_build_compiler();
    probe::set_probe_sysroot(target_compile_sysroot());
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is set by cargo"));
    fs::write(
        out_dir.join("test_build_compiler.rs"),
        format!(
            "const BUILD_COMPILER: &str = {:?};\n",
            compiler.to_str().expect("UTF-8 compiler path")
        ),
    )
    .expect("record the compiler for backend integration tests");

    // Flags every capability probe below must carry; see `probe_flags`.
    let options = probe::probe_options(&compiler);
    let probe_flags = &options.flags;

    if probe::compile_probe(
        &compiler,
        probe_flags,
        "early_session",
        r#"
#![feature(rustc_private)]
extern crate rustc_session;
use rustc_session::EarlySession;
pub fn probe(session: &EarlySession) -> &EarlySession { session }
"#,
        Some(probe::MissingApi::EarlySession),
    ) {
        println!("cargo:rustc-cfg=rustc_session_split");
    }

    if probe_mir_mono_path(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_middle_mir_mono");
    }

    let attr_ir_lang_items = probe_lang_item_path(&compiler, probe_flags);
    if attr_ir_lang_items {
        println!("cargo:rustc-cfg=rustc_attr_ir_lang_items");
    }
    if probe_canonical_memory_symbols(&compiler, probe_flags, attr_ir_lang_items) {
        println!("cargo:rustc-cfg=rustc_canonical_memory_symbols");
    }
    let attr_ir_attributes = probe_attribute_path(&compiler, probe_flags);
    if attr_ir_attributes {
        println!("cargo:rustc-cfg=rustc_attr_ir_attributes");
    }
    if probe_common_linkage(&compiler, probe_flags, attr_ir_attributes) {
        println!("cargo:rustc-cfg=rustc_linkage_common");
    }
    if probe_compiled_module_cache_links(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_compiled_module_cache_links");
    }
    if probe_crate_type_path(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_structures_crate_type");
    }
    if probe_sample_profile_path(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_codegen_sample_profile");
    }
    if probe_scalar_pair_shape(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_scalar_pair_struct");
    }
    if probe_cast_padding(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_cast_pad_count");
    }
    if probe_indirect_modes(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_indirect_modes");
    }
    if probe_float_formats(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_extended_float_formats");
    }
    if probe_register_kinds(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_ppc_f128_register");
    }
    if probe_scalar_pointer(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_scalar_direct_pointer");
    }
    if probe_terminator_attributes(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_terminator_attributes");
    }
    if probe_goto_loop_hints(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_goto_loop_hints");
    }
    if probe_backend_lane_count(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_backend_lane_count");
    }
    let args_ref_alias = probe_generic_args_ref(&compiler, probe_flags);
    if !args_ref_alias {
        println!("cargo:rustc-cfg=rustc_generic_args_value");
    }
    if probe_bound_fn_args(&compiler, probe_flags, args_ref_alias) {
        println!("cargo:rustc-cfg=rustc_bound_fn_args");
    }
    if probe_super_clauses_query(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_super_clauses_query");
    }
    if probe_own_clauses_query(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_own_clauses_query");
    }
    if probe_box_deref_facts(&compiler, probe_flags) {
        println!("cargo:rustc-cfg=rustc_box_deref_facts");
    }

    // The backend's operator knobs come from the TRACKED `-Ztrust-ir-cg-args`
    // option (see `src/knobs.rs`). That option is a Trust addition, so a
    // compiler that predates it has no such field and naming it would be a hard
    // build error. Probe for the field instead of assuming it: with the cfg
    // unset the knob module reads an empty list, which is the fully checked
    // default lane — and on such a compiler the option cannot be passed either
    // (rustc rejects an unknown `-Z`), so nothing an operator asked for is
    // silently dropped.
    let tracked_field = probe_trust_ir_cg_args(&compiler, probe_flags);
    assert!(
        tracked_field || !options.tracked_arguments,
        "build compiler advertises -Ztrust-ir-cg-args but its field probe is absent; refusing to ignore accepted backend arguments"
    );
    if tracked_field {
        println!("cargo:rustc-cfg=trust_ir_cg_args");
    } else {
        // Measured 2026-09-14: this probe fails for reasons unrelated to the
        // option existing — a build script's `$RUSTC` is not the compiler the
        // crate is compiled with — and the failure used to be completely silent,
        // leaving every operator knob inert. Say so. `tracked_backend_args` also
        // now REFUSES a compile that passes `-Ztrust-ir-cg-args` to such a build,
        // so a silent wrong-lane compile is no longer possible either way.
        println!(
            "cargo:warning=trust-ir-cg: the `trust_ir_cg_args` capability probe did not \
             succeed, so `-Ztrust-ir-cg-args` knobs are UNAVAILABLE in this backend build \
             (passing the option will now refuse rather than be ignored)"
        );
    }

    emit_hidden_rlib_symbols();
}

/// Whether the build compiler exports Box-deref validity facts
/// (`TyCtxt::trust_box_deref_facts`, a sited `CastKind::BoxDerefTransmute`).
///
/// Absence is classified exactly (the one E0599 on the query name); any other
/// failure aborts the build. With the query absent the retained probe pins the
/// unit spelling of the cast kind, which is what the unconditional
/// `[TCG-BOX-DEREF]` refusal matches. With it present the retained probe pins
/// every name the fact translation reads, so a compiler that has the query
/// under another fact schema fails this build instead of selecting the
/// emission path.
fn probe_box_deref_facts(compiler: &Path, flags: &[&str]) -> bool {
    let facts = probe::compile_probe(
        compiler,
        flags,
        "box_deref_facts",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
extern crate rustc_span;
use rustc_middle::ty::TyCtxt;
pub fn read<'tcx>(tcx: TyCtxt<'tcx>, id: rustc_span::def_id::DefId) -> bool { tcx.trust_box_deref_facts(id).is_some() }
"#,
        Some(probe::MissingApi::BoxDerefFacts),
    );
    let source = if facts {
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
extern crate rustc_span;
use rustc_middle::mir::{self, trust_box_deref as facts};
use rustc_middle::ty::TyCtxt;
const _: () = assert!(facts::BOX_DEREF_FACT_SCHEMA == 3);
pub fn site(kind: &mir::CastKind) -> Option<mir::BoxDerefSite> {
    match kind { mir::CastKind::BoxDerefTransmute(site) => Some(*site), _ => None }
}
pub fn admit<'a>(table: &'a facts::TrustBoxDerefFacts, site: mir::BoxDerefSite) -> Result<&'a facts::BoxValidityFact, facts::BoxFactRefusal> {
    table.admit(site, facts::BoxFactAdmission::FAIL_CLOSED)
}
pub fn carrier<'tcx>(tcx: TyCtxt<'tcx>, id: rustc_span::def_id::DefId) -> facts::BoxFactCarrierStatus {
    tcx.trust_box_deref_fact_carrier(id.krate).status
}
pub fn roots(root: facts::BoxValidityRoot) -> u8 {
    match root {
        facts::BoxValidityRoot::ParamByValue => 0,
        facts::BoxValidityRoot::AllocPostcondition => 1,
        facts::BoxValidityRoot::ReturnedBoxDischarged => 2,
        facts::BoxValidityRoot::ReturnedBoxAssumed => 3,
        facts::BoxValidityRoot::ReferenceArgBoxValid => 4,
        facts::BoxValidityRoot::ReferenceReturnedAssumed => 5,
        facts::BoxValidityRoot::LentSlotAssumed(_) => 6,
    }
}
pub fn evidence(evidence: &facts::BoxValidityEvidence) -> Option<&facts::BoxValidityPremise> {
    match evidence { facts::BoxValidityEvidence::Premise(premise) => Some(premise), facts::BoxValidityEvidence::ZeroSized => None }
}
"#
    } else {
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::mir;
pub fn is_box_deref(kind: &mir::CastKind) -> bool { matches!(kind, mir::CastKind::BoxDerefTransmute) }
"#
    };
    probe::compile_probe(compiler, flags, "retained_box_deref", source, None);
    facts
}

/// Explicit super clauses exclude associated-type implications and transitive expansion.
fn probe_super_clauses_query(compiler: &Path, flags: &[&str]) -> bool {
    let modern = probe::compile_probe(
        compiler,
        flags,
        "super_clauses_query",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle; extern crate rustc_hir; extern crate rustc_span;
use rustc_middle::ty::{self, TyCtxt}; use rustc_hir::def_id::DefId; use rustc_span::Span;
pub fn read<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> { tcx.explicit_super_clauses_of(id) }
"#,
        Some(probe::MissingApi::SuperClausesQuery),
    );
    let method = if modern {
        "explicit_super_clauses_of"
    } else {
        "explicit_super_predicates_of"
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_middle; extern crate rustc_hir; extern crate rustc_span;
use rustc_middle::ty::{{self, TyCtxt}}; use rustc_hir::def_id::DefId; use rustc_span::Span;
pub fn read<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> {{ tcx.{method}(id) }}
"#
    );
    probe::compile_probe(compiler, flags, "retained_super_clauses", &source, None);
    modern
}

/// Usage-site clauses retain inferred constraints, the parent and every own span.
fn probe_own_clauses_query(compiler: &Path, flags: &[&str]) -> bool {
    let modern = probe::compile_probe(
        compiler,
        flags,
        "own_clauses_query",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle; extern crate rustc_hir;
use rustc_middle::ty::TyCtxt; use rustc_hir::def_id::DefId;
pub fn read<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) { let _ = tcx.clauses_of(id); }
"#,
        Some(probe::MissingApi::OwnClausesQuery),
    );
    let (method, carrier, field) = if modern {
        ("clauses_of", "GenericClauses", "clauses")
    } else {
        ("predicates_of", "GenericPredicates", "predicates")
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_middle; extern crate rustc_hir; extern crate rustc_span;
use rustc_middle::ty::{{self, TyCtxt}}; use rustc_hir::def_id::DefId; use rustc_span::Span;
pub fn read<'tcx>(tcx: TyCtxt<'tcx>, id: DefId) -> (Option<DefId>, &'tcx [(ty::Clause<'tcx>, Span)]) {{
    let ty::{carrier} {{ parent, {field} }} = tcx.{method}(id);
    (parent, {field})
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_own_clauses", &source, None);
    modern
}

/// The interned generic-argument list is named either by the
/// `ty::GenericArgsRef` alias or, where that alias does not exist, by the
/// `Copy` by-value handle `ty::GenericArgs`. Returns whether the alias exists.
/// Only the exact unresolved-alias diagnostic selects the handle; the handle
/// itself is then compiled with no admitted absence.
fn probe_generic_args_ref(compiler: &Path, flags: &[&str]) -> bool {
    let alias = probe::compile_probe(
        compiler,
        flags,
        "generic_args_ref",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::ty;
pub fn read<'tcx>(_: ty::GenericArgsRef<'tcx>) {}
"#,
        Some(probe::MissingApi::GenericArgsRef),
    );
    if !alias {
        probe::compile_probe(
            compiler,
            flags,
            "retained_generic_args_value",
            r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::ty;
pub fn read<'tcx>(args: ty::GenericArgs<'tcx>) -> (ty::GenericArgs<'tcx>, ty::GenericArgs<'tcx>) { (args, args) }
"#,
            None,
        );
    }
    alias
}

/// A function item's generic arguments may be held under a real binder.
/// `args_ref_alias` selects the spelling `probe_generic_args_ref` found.
fn probe_bound_fn_args(compiler: &Path, flags: &[&str], args_ref_alias: bool) -> bool {
    let list = if args_ref_alias {
        "ty::GenericArgsRef<'tcx>"
    } else {
        "ty::GenericArgs<'tcx>"
    };
    let bound_source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::ty::{{self, Ty}};
pub fn read<'tcx>(value: Ty<'tcx>) -> Option<{list}> {{ let ty::FnDef(_, args) = *value.kind() else {{ return None; }}; args.no_bound_vars() }}
"#
    );
    let bound = probe::compile_probe(
        compiler,
        flags,
        "bound_fn_args",
        &bound_source,
        Some(probe::MissingApi::BoundFnArgs),
    );
    let read = if bound {
        "args.no_bound_vars()?"
    } else {
        "args"
    };
    let new = if bound {
        "ty::Binder::dummy(args)"
    } else {
        "args"
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::ty::{{self, Ty, TyCtxt, TyKind}};
pub fn read<'a, 'tcx>(kind: &'a TyKind<'tcx>) -> Option<({list}, &'a TyKind<'tcx>)> {{
    let ty::FnDef(_, args) = *kind else {{ return None; }};
    let args: {list} = {read};
    Some((args, kind))
}}
pub fn new<'tcx>(tcx: TyCtxt<'tcx>, value: Ty<'tcx>) -> Option<Ty<'tcx>> {{
    let ty::FnDef(def_id, args) = *value.kind() else {{ return None; }};
    let args: {list} = {read};
    Some(Ty::new_fn_def(tcx, def_id, {new}))
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_fn_args", &source, None);
    bound
}

/// Read fixed-vector counts without narrowing the backend's checked wrapper.
fn probe_backend_lane_count(compiler: &Path, flags: &[&str]) -> bool {
    let wrapped = probe::compile_probe(
        compiler,
        flags,
        "backend_lane_count",
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn probe(repr: rustc_abi::BackendRepr) { if let rustc_abi::BackendRepr::SimdVector { element: _, count } = repr { let _: u64 = count.as_u64(); } }
"#,
        Some(probe::MissingApi::BackendLaneCount),
    );
    let count = if wrapped { "count.as_u64()" } else { "*count" };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn read<'a>(repr: &'a rustc_abi::BackendRepr) -> Option<(u64, &'a rustc_abi::BackendRepr)> {{
    match repr {{ rustc_abi::BackendRepr::SimdVector {{ element, count }} => {{ let _: &rustc_abi::Scalar = element; let count: u64 = {count}; Some((count, repr)) }}, _ => None }}
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_backend_lanes", &source, None);
    wrapped
}

/// Preserve opaque Goto payloads independently of global Terminator attributes.
fn probe_goto_loop_hints(compiler: &Path, flags: &[&str]) -> bool {
    let hints = probe::compile_probe(
        compiler,
        flags,
        "goto_loop_hints",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::mir;
pub fn probe(kind: &mir::TerminatorKind<'_>) { if let mir::TerminatorKind::Goto { target: _, loop_hint_attrs: hints } = kind { let _: usize = hints.len(); } }
"#,
        Some(probe::MissingApi::GotoLoopHints),
    );
    let field = if hints {
        "loop_hint_attrs: Default::default(),"
    } else {
        ""
    };
    let pattern = if hints { ", loop_hint_attrs" } else { "" };
    let borrow = if hints {
        "let _: &[_] = loop_hint_attrs;"
    } else {
        ""
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::mir;
pub fn probe<'tcx>(target: mir::BasicBlock) -> mir::TerminatorKind<'tcx> {{
    mir::TerminatorKind::Goto {{ target, {field} }}
}}
pub fn read<'a, 'tcx>(kind: &'a mir::TerminatorKind<'tcx>) -> Option<(mir::BasicBlock, &'a mir::TerminatorKind<'tcx>)> {{
    match kind {{ mir::TerminatorKind::Goto {{ target{pattern} }} => {{ {borrow} Some((*target, kind)) }}, _ => None }}
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_goto", &source, None);
    hints
}

/// Detect the global attribute field independently of Goto's loop-hint payload.
/// The selected constructor must spell every top-level field.
fn probe_terminator_attributes(compiler: &Path, flags: &[&str]) -> bool {
    let attributes = probe::compile_probe(
        compiler,
        flags,
        "terminator_attributes",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::mir;
pub fn probe(term: &mut mir::Terminator<'_>) { term.attributes.clear(); }
"#,
        Some(probe::MissingApi::TerminatorAttributes),
    );
    let field = if attributes {
        "attributes: Default::default(),"
    } else {
        ""
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::mir;
pub fn probe<'tcx>(source_info: mir::SourceInfo, kind: mir::TerminatorKind<'tcx>) -> mir::Terminator<'tcx> {{
    mir::Terminator {{ source_info, kind, {field} }}
}}
pub fn read<'a, 'tcx>(term: &'a mir::Terminator<'tcx>) -> (mir::SourceInfo, &'a mir::TerminatorKind<'tcx>) {{
    (term.source_info, &term.kind)
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_terminator", &source, None);
    attributes
}

/// Preserve the fallible consumer contract when the private API returns a
/// pointer directly. Only the measured missing result method selects it.
fn probe_scalar_pointer(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "scalar_pointer_result",
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_middle;
use rustc_abi::HasDataLayout;
use rustc_middle::mir::interpret::{Scalar, Pointer, CtfeProvenance};
pub fn probe(cx: &impl HasDataLayout, value: Scalar) -> Option<Pointer<Option<CtfeProvenance>>> { value.to_pointer(cx).discard_err() }
"#,
        Some(probe::MissingApi::ScalarPointerResult),
    );
    let convert = if legacy {
        "value.to_pointer(cx).discard_err()"
    } else {
        "Some(value.to_pointer(cx))"
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_middle;
use rustc_abi::HasDataLayout;
use rustc_middle::mir::interpret::{{Scalar, Pointer, CtfeProvenance}};
pub fn probe(cx: &impl HasDataLayout, value: Scalar) -> Option<Pointer<Option<CtfeProvenance>>> {{
    if value.size() != cx.data_layout().pointer_size() {{ return None; }}
    {convert}
}}
pub fn read(value: Pointer<Option<CtfeProvenance>>) -> Option<(CtfeProvenance, rustc_abi::Size)> {{
    value.into_pointer_or_addr().ok().map(|p| p.prov_and_relative_offset())
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_scalar_pointer", &source, None);
    !legacy
}

/// Select by a measured single-variant absence, then require the complete enum.
fn probe_float_formats(compiler: &Path, flags: &[&str]) -> bool {
    let modern = probe::compile_probe(
        compiler,
        flags,
        "bfloat_primitive",
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn probe() -> rustc_abi::Float { rustc_abi::Float::F16B }
"#,
        Some(probe::MissingApi::BfloatPrimitive),
    );
    let extra = if modern {
        "Float::F16B => 4, Float::PpcF128 => 5,"
    } else {
        ""
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn probe(value: rustc_abi::Float) -> u8 {{
    use rustc_abi::Float;
    match value {{ Float::F16 => 0, Float::F32 => 1, Float::F64 => 2, Float::F128 => 3, {extra} }}
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_float_formats", &source, None);
    modern
}

/// Register-kind availability is independent of the primitive float enum.
fn probe_register_kinds(compiler: &Path, flags: &[&str]) -> bool {
    let modern = probe::compile_probe(
        compiler,
        flags,
        "ppc_f128_register",
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn probe() -> rustc_abi::RegKind { rustc_abi::RegKind::PpcF128 }
"#,
        Some(probe::MissingApi::PpcF128Register),
    );
    let extra = if modern {
        "RegKind::PpcF128 => None,"
    } else {
        ""
    };
    let source = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn probe(kind: rustc_abi::RegKind) -> Option<rustc_abi::Primitive> {{
    use rustc_abi::RegKind;
    match kind {{ RegKind::Integer | RegKind::Float => None, RegKind::Vector {{ hint_vector_elem }} => Some(hint_vector_elem), {extra} }}
}}
pub fn construct(hint_vector_elem: rustc_abi::Primitive) -> rustc_abi::RegKind {{ rustc_abi::RegKind::Vector {{ hint_vector_elem }} }}
"#
    );
    probe::compile_probe(compiler, flags, "retained_register_kinds", &source, None);
    modern
}

/// A fresh module has no cached-link inputs. Detect the legacy bookkeeping
/// field independently, and require every retained artifact field to compile
/// in the selected representation before publishing the capability.
fn probe_compiled_module_cache_links(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "compiled_module_cache_links",
        r#"
#![feature(rustc_private)]
extern crate rustc_codegen_ssa;
use rustc_codegen_ssa::CompiledModule;
use std::path::PathBuf;
pub fn probe(module: CompiledModule) -> Vec<PathBuf> { module.links_from_incr_cache }
"#,
        Some(probe::MissingApi::CompiledModuleCacheLinks),
    );
    let cache = if legacy {
        "links_from_incr_cache: Vec::new(),"
    } else {
        ""
    };
    let retained = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_codegen_ssa;
use rustc_codegen_ssa::{{CompiledModule, ModuleKind}};
use std::path::PathBuf;
pub fn probe(name: String, kind: ModuleKind, paths: [Option<PathBuf>; 6]) -> CompiledModule {{
    let [object, global_asm_object, dwarf_object, bytecode, assembly, llvm_ir] = paths;
    CompiledModule {{ name, kind, object, global_asm_object, dwarf_object, bytecode, assembly, llvm_ir,
        {cache}
    }}
}}
"#
    );
    probe::compile_probe(compiler, flags, "fresh_compiled_module", &retained, None);
    legacy
}

/// The crate kind controls demand lowering and the rlib-only failure exception.
/// Select its namespace independently and check every retained kind plus the
/// actual TyCtxt query before accepting either representation.
fn probe_crate_type_path(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "session_crate_type",
        r#"
#![feature(rustc_private)]
extern crate rustc_session;
use rustc_session::config::CrateType;
pub fn probe() -> CrateType { CrateType::Executable }
"#,
        Some(probe::MissingApi::SessionCrateType),
    );
    let import = if legacy {
        "use rustc_session::config::CrateType;"
    } else {
        "extern crate rustc_structures;\nuse rustc_structures::CrateType;"
    };
    let retained = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_session;
extern crate rustc_middle;
{import}
pub fn kind(value: CrateType) -> u8 {{
    match value {{
        CrateType::Executable => 0, CrateType::Dylib => 1, CrateType::Rlib => 2,
        CrateType::StaticLib => 3, CrateType::Cdylib => 4,
        CrateType::ProcMacro => 5, CrateType::Sdylib => 6,
    }}
}}
pub fn probe<'tcx>(tcx: rustc_middle::ty::TyCtxt<'tcx>) -> &'tcx [CrateType] {{
    tcx.crate_types()
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_crate_types", &retained, None);
    !legacy
}

/// Recognize the measured tuple-to-struct change, then require every component
/// and the selected offset contract. Unknown shapes never select a fallback.
fn probe_scalar_pair_shape(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "tuple_scalar_pair",
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn probe(repr: rustc_abi::BackendRepr) -> Option<(rustc_abi::Scalar, rustc_abi::Scalar)> {
    match repr { rustc_abi::BackendRepr::ScalarPair(a, b) => Some((a, b)), _ => None }
}
"#,
        Some(probe::MissingApi::TupleScalarPair),
    );
    let (construct, pattern, offset) = if legacy {
        (
            "rustc_abi::BackendRepr::ScalarPair(a, b)",
            "rustc_abi::BackendRepr::ScalarPair(a, b)",
            "a.size(cx).align_to(b.default_align(cx).abi)",
        )
    } else {
        (
            "rustc_abi::BackendRepr::ScalarPair { a, b, b_offset }",
            "rustc_abi::BackendRepr::ScalarPair { a, b, b_offset }",
            "b_offset",
        )
    };
    let offset_parameter = if legacy {
        ""
    } else {
        ", b_offset: rustc_abi::Size"
    };
    let retained = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_abi;
pub fn construct(a: rustc_abi::Scalar, b: rustc_abi::Scalar{offset_parameter}) -> rustc_abi::BackendRepr {{
    {construct}
}}
pub fn probe<C: rustc_abi::HasDataLayout>(repr: rustc_abi::BackendRepr, cx: &C) -> Option<(rustc_abi::Scalar, rustc_abi::Scalar, rustc_abi::Size)> {{
    let _ = cx;
    match repr {{ {pattern} => Some((a, b, {offset})), _ => None }}
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_scalar_pair", &retained, None);
    !legacy
}

/// Indirect payloads changed independently of cast padding. Require the full
/// selected constructors/readers and every known mode before selecting it.
fn probe_indirect_modes(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "boolean_indirect_stack",
        r#"
#![feature(rustc_private)]
extern crate rustc_target;
extern crate rustc_abi;
pub fn probe(mode: &rustc_target::callconv::PassMode) -> bool {
    matches!(mode, rustc_target::callconv::PassMode::Indirect { on_stack: _, .. })
}
"#,
        Some(probe::MissingApi::BooleanIndirectStack),
    );
    let retained = if legacy {
        r#"
#![feature(rustc_private)]
extern crate rustc_target;
extern crate rustc_abi;
pub fn construct(attrs: rustc_target::callconv::ArgAttributes, meta_attrs: Option<rustc_target::callconv::ArgAttributes>, on_stack: bool) -> rustc_target::callconv::PassMode {
    rustc_target::callconv::PassMode::Indirect { attrs, meta_attrs, on_stack }
}
pub fn read(mode: &rustc_target::callconv::PassMode) -> Option<(&rustc_target::callconv::ArgAttributes, Option<&rustc_target::callconv::ArgAttributes>, bool)> {
    match mode { rustc_target::callconv::PassMode::Indirect { attrs, meta_attrs, on_stack } => Some((attrs, meta_attrs.as_ref(), *on_stack)), _ => None }
}
"#
    } else {
        r#"
#![feature(rustc_private)]
extern crate rustc_target;
extern crate rustc_abi;
pub fn construct(attrs: rustc_target::callconv::ArgAttributes, address_space: Option<rustc_abi::AddressSpace>, mode: rustc_target::callconv::IndirectMode) -> rustc_target::callconv::PassMode {
    rustc_target::callconv::PassMode::Indirect { attrs, address_space, mode }
}
pub fn read(mode: &rustc_target::callconv::PassMode) -> Option<(&rustc_target::callconv::ArgAttributes, Option<rustc_abi::AddressSpace>, rustc_target::callconv::IndirectMode)> {
    match mode { rustc_target::callconv::PassMode::Indirect { attrs, address_space, mode } => Some((attrs, *address_space, *mode)), _ => None }
}
pub fn modes(mode: rustc_target::callconv::IndirectMode) -> u8 {
    match mode { rustc_target::callconv::IndirectMode::Pointer => 0, rustc_target::callconv::IndirectMode::OnStack => 1, rustc_target::callconv::IndirectMode::AmdgpuKernelArg => 2 }
}
pub fn construct_unsized(attrs: rustc_target::callconv::ArgAttributes, meta_attrs: rustc_target::callconv::ArgAttributes) -> rustc_target::callconv::PassMode {
    rustc_target::callconv::PassMode::IndirectUnsized { attrs, meta_attrs }
}
pub fn read_unsized(mode: &rustc_target::callconv::PassMode) -> Option<(&rustc_target::callconv::ArgAttributes, &rustc_target::callconv::ArgAttributes)> {
    match mode { rustc_target::callconv::PassMode::IndirectUnsized { attrs, meta_attrs } => Some((attrs, meta_attrs)), _ => None }
}
"#
    };
    let retained = format!(
        "{retained}\npub fn default_address_space(space: Option<rustc_abi::AddressSpace>) -> bool {{ space.is_none_or(|space| space == rustc_abi::AddressSpace::ZERO) }}\npub fn attributes(attrs: rustc_target::callconv::ArgAttributes) -> rustc_target::callconv::ArgAttributes {{ let rustc_target::callconv::ArgAttributes {{ regular, arg_ext, pointee_size, pointee_align }} = attrs; rustc_target::callconv::ArgAttributes {{ regular, arg_ext, pointee_size, pointee_align }} }}\n"
    );
    probe::compile_probe(compiler, flags, "retained_indirect_modes", &retained, None);
    !legacy
}

/// Preserve the complete cast payload and the exact leading-argument count.
/// Only the measured missing legacy field permits selecting the count API.
fn probe_cast_padding(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "boolean_cast_padding",
        r#"
#![feature(rustc_private)]
extern crate rustc_target;
pub fn probe(mode: &rustc_target::callconv::PassMode) -> bool {
    matches!(mode, rustc_target::callconv::PassMode::Cast { pad_i32: _, .. })
}
"#,
        Some(probe::MissingApi::BooleanCastPadding),
    );
    let (field, padding_type, count) = if legacy {
        ("pad_i32", "bool", "u8::from(*pad_i32)")
    } else {
        ("pad_i32_count", "u8", "*pad_i32_count")
    };
    let retained = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_target;
pub fn construct(cast: rustc_target::callconv::CastTarget, {field}: {padding_type}) -> rustc_target::callconv::PassMode {{
    rustc_target::callconv::PassMode::Cast {{ cast: Box::new(cast), {field} }}
}}
pub fn probe(mode: &rustc_target::callconv::PassMode) -> Option<(&rustc_target::callconv::CastTarget, u8)> {{
    match mode {{ rustc_target::callconv::PassMode::Cast {{ cast, {field} }} => Some((cast.as_ref(), {count})), _ => None }}
}}
pub fn payload(target: rustc_target::callconv::CastTarget) -> rustc_target::callconv::CastTarget {{
    let rustc_target::callconv::CastTarget {{ prefix, rest_offset, rest, attrs }} = target;
    rustc_target::callconv::CastTarget {{ prefix, rest_offset, rest, attrs }}
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_cast_padding", &retained, None);
    !legacy
}

/// A missing old sample-profile field permits the new field only when it still
/// supplies the actual optional Path. A wrong type or unknown failure aborts.
fn probe_sample_profile_path(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "unstable_sample_profile",
        r#"
#![feature(rustc_private)]
extern crate rustc_session;
use rustc_session::config::Options;
use std::path::Path;
pub fn probe(opts: &Options) -> Option<&Path> { opts.unstable_opts.profile_sample_use.as_deref() }
"#,
        Some(probe::MissingApi::UnstableSampleProfile),
    );
    if !legacy {
        probe::compile_probe(
            compiler,
            flags,
            "codegen_sample_profile",
            r#"
#![feature(rustc_private)]
extern crate rustc_session;
use rustc_session::config::Options;
use std::path::Path;
pub fn probe(opts: &Options) -> Option<&Path> { opts.cg.profile_sample_use.as_deref() }
"#,
            None,
        );
    }
    !legacy
}

/// Select the retained language-item enum by an actual import, after a common
/// private-crate control. Only the exact missing old import permits trying the
/// new path; failure of that replacement aborts the build.
fn probe_lang_item_path(compiler: &Path, flags: &[&str]) -> bool {
    probe::compile_probe(
        compiler,
        flags,
        "hir_control",
        r#"
#![feature(rustc_private)]
extern crate rustc_hir;
pub use rustc_hir::def_id::DefId;
"#,
        None,
    );
    if probe::compile_probe(
        compiler,
        flags,
        "hir_lang_item",
        r#"
#![feature(rustc_private)]
extern crate rustc_hir;
use rustc_hir::LangItem;
pub fn probe() -> LangItem { LangItem::Sized }
"#,
        Some(probe::MissingApi::HirLangItem),
    ) {
        return false;
    }
    probe::compile_probe(
        compiler,
        flags,
        "attr_ir_lang_item",
        r#"
#![feature(rustc_private)]
extern crate rustc_attr_ir;
use rustc_attr_ir::lang_items::LangItem;
pub fn probe() -> LangItem { LangItem::Sized }
"#,
        None,
    )
}

/// Probe memory-item variants independently of the retained enum's namespace.
/// Only an exact absent legacy variant permits the mandatory canonical-query
/// replacement; a partially supported legacy query aborts rather than guessing.
fn probe_canonical_memory_symbols(
    compiler: &Path,
    flags: &[&str],
    attr_ir_lang_items: bool,
) -> bool {
    let imports = if attr_ir_lang_items {
        "extern crate rustc_hir;\nextern crate rustc_attr_ir;\nuse rustc_attr_ir::lang_items::LangItem;"
    } else {
        "extern crate rustc_hir;\nuse rustc_hir::LangItem;"
    };
    let variant = format!(
        "#![feature(rustc_private)]\n{imports}\npub fn probe() -> LangItem {{ LangItem::MemCpy }}\n"
    );
    if probe::compile_probe(
        compiler,
        flags,
        "memory_lang_item",
        &variant,
        Some(probe::MissingApi::MemoryLangItem),
    ) {
        let all_items = format!(
            r#"
#![feature(rustc_private)]
{imports}
extern crate rustc_middle;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
pub fn probe(tcx: TyCtxt<'_>) -> [Option<DefId>; 3] {{
    [LangItem::MemCpy, LangItem::MemMove, LangItem::MemSet]
        .map(|item| tcx.lang_items().get(item))
}}
"#
        );
        probe::compile_probe(compiler, flags, "memory_lang_items", &all_items, None);
        return false;
    }
    probe::compile_probe(
        compiler,
        flags,
        "canonical_memory_symbols",
        r#"
#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
pub fn probe(tcx: TyCtxt<'_>) -> [Option<DefId>; 3] {
    ["memcpy", "memmove", "memset"].map(|name| {
        tcx.all_canonical_symbols(())
            .iter()
            .find(|entry| entry.symbol == rustc_span::Symbol::intern(name))
            .map(|entry| entry.def_id)
    })
}
"#,
        None,
    )
}

/// Select attributes independently of the language-item namespace. A present
/// old import still requires the complete retained type/macro query to compile.
fn probe_attribute_path(compiler: &Path, flags: &[&str]) -> bool {
    let legacy = probe::compile_probe(
        compiler,
        flags,
        "hir_attributes",
        r#"
#![feature(rustc_private)]
extern crate rustc_hir;
use rustc_hir::attrs::InlineAttr;
pub fn probe() -> InlineAttr { InlineAttr::Never }
"#,
        Some(probe::MissingApi::HirAttributes),
    );
    let imports = if legacy {
        "use rustc_hir::{attrs::{InlineAttr, Linkage}, find_attr};"
    } else {
        "extern crate rustc_attr_ir;\nuse rustc_attr_ir::{InlineAttr, Linkage, find_attr};"
    };
    let retained = format!(
        r#"
#![feature(rustc_private)]
extern crate rustc_hir;
extern crate rustc_middle;
{imports}
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
pub fn inline(a: InlineAttr) -> u8 {{
    match a {{
        InlineAttr::None => 0, InlineAttr::Hint => 1, InlineAttr::Always => 2,
        InlineAttr::Never => 3, InlineAttr::Force {{ .. }} => 4,
    }}
}}
pub fn linkages() -> [Linkage; 8] {{
    [Linkage::AvailableExternally, Linkage::ExternalWeak, Linkage::External,
     Linkage::Internal, Linkage::LinkOnceAny, Linkage::LinkOnceODR,
     Linkage::WeakAny, Linkage::WeakODR]
}}
pub fn builtin(tcx: TyCtxt<'_>, did: DefId) -> bool {{
    find_attr!(tcx, did, RustcBuiltinMacro {{ .. }})
}}
"#
    );
    probe::compile_probe(compiler, flags, "retained_attributes", &retained, None);
    !legacy
}

/// Common's presence is a separate enum capability, not a consequence of the
/// selected namespace. Its absence never removes the legacy policy/refusal.
fn probe_common_linkage(compiler: &Path, flags: &[&str], attr_ir_attributes: bool) -> bool {
    let imports = if attr_ir_attributes {
        "extern crate rustc_attr_ir;\nuse rustc_attr_ir::Linkage;"
    } else {
        "extern crate rustc_hir;\nuse rustc_hir::attrs::Linkage;"
    };
    let source = format!(
        "#![feature(rustc_private)]\n{imports}\npub fn probe() -> Linkage {{ Linkage::Common }}\n"
    );
    probe::compile_probe(
        compiler,
        flags,
        "common_linkage",
        &source,
        Some(probe::MissingApi::CommonLinkage),
    )
}

fn compiler_metadata(compiler: &Path, args: &[&str]) -> String {
    let output = probe::capture(Command::new(compiler).args(args), probe::PROBE_TIMEOUT)
        .unwrap_or_else(|error| {
            panic!("cannot query build compiler {compiler:?} with {args:?}: {error}")
        });
    assert!(
        output.status.success(),
        "build compiler {compiler:?} query {args:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).unwrap_or_else(|error| {
        panic!("build compiler {compiler:?} metadata is not UTF-8: {error}")
    });
    let text = text.trim();
    assert!(
        !text.is_empty(),
        "build compiler {compiler:?} returned empty metadata for {args:?}"
    );
    text.to_owned()
}

/// The sysroot the REAL compile of this crate uses: the selected `RUSTC`'s answer to
/// `--print sysroot` WITH `--target $TARGET`.
///
/// Asked without `--target`, a wrapper may answer for a different compiler role. Measured
/// under the Trust bootstrap: its rustc shim treats a `--target`-less invocation as a build
/// script compile and injects `--sysroot` only when `--target` is present
/// (src/bootstrap/src/bin/rustc.rs), so a plain `--print sysroot` returned the stage0
/// snapshot's own sysroot, whose rustc-dev rmetas are an older generation than the private
/// tool sysroot bootstrap adds with `-Lall` — and every rustc_private probe failed E0464
/// while the real compile, which does carry `--target`, never did. With no wrapper the
/// target changes nothing, so this is the same answer plain `rustc` and rustup give.
fn target_compile_sysroot() -> PathBuf {
    let selected = PathBuf::from(env::var_os("RUSTC").expect("RUSTC is set by cargo"));
    let target = env::var("TARGET").expect("TARGET is set by cargo for build scripts");
    let sysroot = PathBuf::from(compiler_metadata(
        &selected,
        &["--print", "sysroot", "--target", &target],
    ));
    assert!(
        sysroot.is_absolute(),
        "build compiler {selected:?} returned a nonabsolute target sysroot: {sysroot:?}"
    );
    sysroot
}

fn resolve_build_compiler() -> PathBuf {
    let selected = PathBuf::from(env::var_os("RUSTC").expect("RUSTC is set by cargo"));
    // Command resolves bare names through PATH and invokes rustup proxies under
    // their original name. Canonicalizing a proxy first would invoke `rustup`
    // instead of the selected `rustc` driver.
    let identity = compiler_metadata(&selected, &["-vV"]);
    let sysroot = PathBuf::from(compiler_metadata(&selected, &["--print", "sysroot"]));
    assert!(
        sysroot.is_absolute(),
        "build compiler {selected:?} returned a nonabsolute sysroot: {sysroot:?}"
    );
    let binary = identity
        .lines()
        .find_map(|line| line.strip_prefix("binary: "))
        .expect("build compiler -vV did not identify its binary");
    assert!(
        matches!(binary, "trustc" | "rustc"),
        "unsupported build compiler binary {binary:?} from {selected:?}"
    );
    let compiler = sysroot
        .join("bin")
        .join(format!("{binary}{}", env::consts::EXE_SUFFIX));
    let actual_identity = compiler_metadata(&compiler, &["-vV"]);
    assert_eq!(
        keyed_identity(&actual_identity),
        keyed_identity(&identity),
        "sysroot compiler {compiler:?} does not match selected build compiler {selected:?}"
    );
    compiler
}

/// The NAME-INDEPENDENT half of `-vV`: every `key: value` line, dropping the
/// leading version banner.
///
/// The banner is not a compiler identity. A Trust sysroot ships `rustc` as a
/// byte-identical compatibility alias of `trustc` (CLAUDE.md, "Toolchain
/// naming"), and the driver brands its first line from the name it was invoked
/// under, so the SAME binary prints
///
///     rustc 1.99.0-dev (acb08e761 2026-08-21) (trustc 0.1.0)   # as trustc
///     rustc 1.99.0-dev (acb08e761 2026-08-21)                  # as rustc
///
/// Comparing whole `-vV` output therefore fails whenever the selected build
/// compiler and `<sysroot>/bin/<binary>` are reached under different names —
/// which is the ordinary bootstrap case, and made this assertion fire on a
/// tree where both were the same compiler at the same `commit-hash`.
///
/// `commit-hash`, `commit-date`, `host` and `release` are what actually
/// identify the driver, and they are unaffected by the invoked name, so the
/// guard keeps its whole strength: a genuinely different compiler still
/// differs here.
fn keyed_identity(identity: &str) -> Vec<&str> {
    identity
        .lines()
        .map(str::trim_end)
        .filter(|line| line.contains(": "))
        .collect()
}

/// Stop re-exporting every upstream rlib symbol from the backend dylib.
///
/// rustc loads the backend through `__rustc_codegen_backend`. A Rust dylib
/// can also export symbols from statically linked rlibs, adding loader work.
///
/// `--exclude-libs,ALL` makes symbols pulled from archive members (all our
/// rlibs) local. `__rustc_codegen_backend` lives in this crate's own object,
/// not an archive, so it stays exported and `dlsym` still finds it.
///
/// Symbol counts, load-time improvements, and emitted-code identity must be
/// measured for the actual artifact. Historical measurements are not current
/// guarantees.
///
/// ELF-only: `--exclude-libs` is a GNU ld / lld flag. Mach-O's ld64 has no
/// equivalent and errors on it, so gate on the target OS.
fn emit_hidden_rlib_symbols() {
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let elf = !matches!(target_os.as_str(), "macos" | "ios" | "windows") && target_env != "msvc";
    if elf {
        println!("cargo:rustc-link-arg=-Wl,--exclude-libs,ALL");
    }
}

/// Does the selected compiler carry `Options::unstable_opts::trust_ir_cg_args`?
///
/// Named exactly as the knob module reads it, so the probe cannot pass while the
/// real access fails: the same field path, on the same type, through the same
/// rustflags.
fn probe_trust_ir_cg_args(compiler: &Path, flags: &[&str]) -> bool {
    probe::compile_probe(
        compiler,
        flags,
        "session_control",
        r#"
#![feature(rustc_private)]
extern crate rustc_session;
pub fn probe(options: &rustc_session::config::Options) {
    let _ = &options.unstable_opts;
}
"#,
        None,
    );
    probe::compile_probe(
        compiler,
        flags,
        "trust_ir_cg_args",
        r#"
#![feature(rustc_private)]
extern crate rustc_session;

pub fn probe(options: &rustc_session::config::Options) -> usize {
    options.unstable_opts.trust_ir_cg_args.len()
}
"#,
        Some(probe::MissingApi::TrackedArguments),
    )
}

fn probe_mir_mono_path(compiler: &Path, flags: &[&str]) -> bool {
    probe::compile_probe(
        compiler,
        flags,
        "middle_control",
        "#![feature(rustc_private)]\npub extern crate rustc_middle;\n",
        None,
    );
    let current = probe::compile_probe(
        compiler,
        flags,
        "mir_mono",
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;

use rustc_middle::mir::mono::MonoItem;

pub fn probe<'tcx>() {
    let _ = core::mem::size_of::<Option<MonoItem<'tcx>>>();
}
"#,
        Some(probe::MissingApi::MirMono),
    );
    if !current {
        // Absence alone cannot authorize an unusable fallback import.
        probe::compile_probe(
            compiler,
            flags,
            "legacy_mono",
            r#"
#![feature(rustc_private)]
extern crate rustc_middle;
use rustc_middle::mono::MonoItem;
pub fn probe<'tcx>() {
    let _ = core::mem::size_of::<Option<MonoItem<'tcx>>>();
}
"#,
            None,
        );
    }
    current
}
