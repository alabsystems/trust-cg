// Authenticated inline-only bodies: the trust-ir obligation on
// `Linkage::AvailableExternally` (`refuse/available_externally_inline_unauthenticated`)
// made executable.
//
// A body `h` of the compiled module M is AUTHENTICATED when an import row of M
// that `Module::verify_import` accepts against a supplied dependency D names a
// D that DEFINES `h` with a translation equal to the body's. Then the premise
// that the body computes what the linked definition computes rests on the
// import, not on the producer's word: the evidence records it as discharged
// (not a disclosed premise), and it is the only kind of body a compile that
// makes a proof claim splices. Everything here is fail-closed: a missing
// dependency, a digest that does not match, a dependency that does not define
// the symbol, or a body that differs by one constant leaves the call a call
// under a proof claim.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_codegen::{
    Compiler, CompilerConfig, InlineOnlyAdmission, InlineOnlyAuthority, JitExternBindings,
    admit_inline_only_bodies_with_authority, prepare_jit_lir_module_with_authority,
};
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    CodegenLicensePolicy, GuardCarrierArch, ObjectAccessModel, TlsDialect, prepare_module_for_lir,
};
use trust_ir::{
    Endianness, ICmpOp, Linkage, Module, ModuleImport, Producer, StructPassingPolicy, TargetInfo,
    Ty,
};
use trust_ir_build::ModuleBuilder;

const HELPER: &str = "tcg_auth_read";
const SLOW: &str = "tcg_auth_read_slow";
const RUNTIME: &str = "tcg_auth_runtime";

static DEFINITION_CALLS: AtomicUsize = AtomicUsize::new(0);

extern "C" fn host_read_slow(_table: *const i64, index: i64) -> i64 {
    -1000 - index
}

extern "C" fn host_read(table: *const i64, index: i64) -> i64 {
    DEFINITION_CALLS.fetch_add(1, Ordering::SeqCst);
    // SAFETY: the test passes a table whose word 0 is its length.
    let len = unsafe { *table };
    if (index as u64) < (len as u64) {
        // SAFETY: bounds-checked above.
        unsafe { *table.add(1 + index as usize) }
    } else {
        host_read_slow(table, index)
    }
}

fn host() -> Target {
    Target::try_host().expect("an in-process JIT host")
}

fn target_info() -> TargetInfo {
    let triple = match host() {
        Target::X86_64 if cfg!(target_os = "macos") => "x86_64-apple-darwin",
        Target::X86_64 => "x86_64-unknown-linux-gnu",
        _ if cfg!(target_os = "macos") => "aarch64-apple-darwin",
        _ => "aarch64-unknown-linux-gnu",
    };
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// Emit `h(table, i) = i < table[0] ? table[1 + i + offset - 1] : h_slow(table, i)`
/// into `mb` with `linkage`; `offset` 1 is the runtime's real body.
fn emit_read(mb: &mut ModuleBuilder, linkage: Linkage, offset: i64) -> trust_ir::FuncId {
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let slow = mb.declare_function(SLOW, ft);
    let mut fb = mb.function(HELPER, ft);
    fb.set_linkage(linkage);
    let entry = fb.create_block();
    let table = fb.add_block_param(entry, Ty::Ptr);
    let index = fb.add_block_param(entry, Ty::I64);
    let fast = fb.create_block();
    let slow_block = fb.create_block();
    fb.switch_to_block(entry);
    let len = fb.load(Ty::I64, table);
    let in_range = fb.icmp(ICmpOp::Ult, Ty::I64, index, len);
    fb.condbr(in_range, fast, vec![], slow_block, vec![]);
    fb.switch_to_block(fast);
    let one = fb.iconst(Ty::I64, i128::from(offset));
    let slot = fb.add(Ty::I64, index, one);
    let element = fb.gep(Ty::I64, table, vec![slot]);
    let value = fb.load(Ty::I64, element);
    fb.ret(vec![value]);
    fb.switch_to_block(slow_block);
    let rest = fb.call(slow, vec![table, index]);
    fb.ret(vec![rest]);
    fb.build()
}

/// The runtime module D: it DEFINES the helper (and declares its remainder).
fn runtime(with_definition: bool, extra: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(RUNTIME, target_info());
    if with_definition {
        emit_read(&mut mb, Linkage::External, 1);
    }
    if extra || !with_definition {
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("tcg_auth_unrelated", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.ret(vec![x]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The compiled module M: an inline-only body of the helper (fast path with
/// `offset`), `entry` calling it twice, and — when `import` names one — an
/// import row pinned to that dependency's digest.
fn program(offset: i64, import: Option<&Module>) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("tcg_auth_program", target_info());
    let read = emit_read(&mut mb, Linkage::AvailableExternally, offset);
    {
        let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("entry", ft);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let first = fb.call(read, vec![table, index]);
        let one = fb.iconst(Ty::I64, 1);
        let next = fb.add(Ty::I64, index, one);
        let second = fb.call(read, vec![table, next]);
        let sum = fb.add(Ty::I64, first, second);
        fb.ret(vec![sum]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    if let Some(dependency) = import {
        module
            .intern_import(
                ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                    .with_producer(Producer::TrustIr),
            )
            .expect("Module::intern_import: test fixture");
    }
    module
}

fn admit(
    module: &Module,
    dependencies: &[&Module],
    admission: InlineOnlyAdmission,
) -> trust_cg_codegen::AdmittedInlineOnlyBodies {
    admit_inline_only_bodies_with_authority(
        module,
        GuardCarrierArch::AArch64,
        ObjectAccessModel::default(),
        &permit_unlicensed(),
        admission,
        InlineOnlyAuthority { dependencies },
    )
}

/// No floating arithmetic: the returned integer observes the exact NaN bits.
fn float_bits_module(name: &str, linkage: Linkage, bits: u64) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target_info());
    let ft = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("float_bits", ft);
    fb.set_linkage(linkage);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let float = fb.fconst(Ty::F64, f64::from_bits(bits));
    let raw = fb.cast(trust_ir::CastOp::Bitcast, Ty::F64, Ty::I64, float);
    fb.ret(vec![raw]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn authenticated_float_bitcasts_require_identical_ieee_bits() {
    for (definition_bits, body_bits) in [
        (0x7ff8_0000_0000_0001, 0x7ff8_0000_0000_0002),
        (0x7ff8_0000_0000_0001, 0xfff8_0000_0000_0001),
        (0x7ff8_0000_0000_0001, 0x7ff0_0000_0000_0001),
        (0, 0x8000_0000_0000_0000),
    ] {
        let dependency = float_bits_module("float_runtime", Linkage::External, definition_bits);
        for bits in [definition_bits, body_bits] {
            let mut module = float_bits_module("float_user", Linkage::AvailableExternally, bits);
            module
                .intern_import(
                    ModuleImport::new(dependency.name.clone(), dependency.stable_digest())
                        .with_producer(Producer::TrustIr),
                )
                .expect("Module::intern_import: test fixture");
            let admitted = admit(&module, &[&dependency], InlineOnlyAdmission::Withhold);
            if bits == definition_bits {
                assert_eq!(admitted.bodies.len(), 1, "{:?}", admitted.withheld);
                assert_eq!(admitted.authenticated.len(), 1);
                assert!(admitted.withheld.is_empty());
            } else {
                assert!(
                    admitted.bodies.is_empty(),
                    "mismatched IEEE bits {bits:016x}"
                );
                assert!(admitted.authenticated.is_empty());
                assert_eq!(admitted.withheld.len(), 1);
            }
        }
    }
}

#[test]
fn an_authenticated_body_is_admitted_under_a_proof_claim() {
    let d = runtime(true, false);
    let m = program(1, Some(&d));
    let admitted = admit(&m, &[&d], InlineOnlyAdmission::Withhold);
    assert_eq!(admitted.bodies.len(), 1);
    assert!(admitted.withheld.is_empty(), "{:?}", admitted.withheld);
    assert_eq!(admitted.authenticated.len(), 1);
    let auth = &admitted.authenticated[0];
    assert_eq!(auth.name, HELPER);
    assert_eq!(auth.dependency, RUNTIME);
    let expected: String = d
        .stable_digest()
        .bytes
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(auth.digest, expected);
}

#[test]
fn without_an_authenticating_dependency_a_proof_claim_withholds() {
    let d = runtime(true, false);
    let unimported = program(1, None);
    let other_digest = runtime(true, true);
    let undefined = runtime(false, false);
    let cases: [(&str, Module, Vec<&Module>); 4] = [
        ("no dependency supplied", program(1, Some(&d)), vec![]),
        ("no import row", unimported, vec![&d]),
        // The row pins `d`'s digest; the supplied module differs.
        ("digest mismatch", program(1, Some(&d)), vec![&other_digest]),
        // The row authenticates the supplied module, which does not define
        // the helper.
        (
            "no definition",
            program(1, Some(&undefined)),
            vec![&undefined],
        ),
    ];
    for (label, module, dependencies) in cases {
        let admitted = admit(&module, &dependencies, InlineOnlyAdmission::Withhold);
        assert!(admitted.bodies.is_empty(), "{label}");
        assert!(admitted.authenticated.is_empty(), "{label}");
        assert_eq!(admitted.withheld.len(), 1, "{label}");
        assert!(
            admitted.withheld[0]
                .reason
                .contains("no supplied dependency authenticates"),
            "{label}: {:?}",
            admitted.withheld
        );
    }
}

#[test]
fn a_body_that_differs_by_one_constant_is_not_authenticated() {
    let d = runtime(true, false);
    // The inline-only body reads `table[i + 2]`; the definition `table[i + 1]`.
    let tampered = program(2, Some(&d));
    let withheld = admit(&tampered, &[&d], InlineOnlyAdmission::Withhold);
    assert!(withheld.bodies.is_empty());
    assert_eq!(withheld.withheld.len(), 1);
    // Without a proof claim it is still admitted — as a disclosed premise.
    let disclosed = admit(&tampered, &[&d], InlineOnlyAdmission::DisclosedPremise);
    assert_eq!(disclosed.bodies.len(), 1);
    assert!(disclosed.authenticated.is_empty());
}

/// The raw-lane step splices an authenticated body, recording it as
/// discharged, only when the compile claims no proof. Under the proof-claim
/// admission (OD-225) the step runs neither LIR pass, so it splices no body,
/// authenticated or not, and lists it as withheld.
#[test]
fn the_raw_lane_step_splices_an_authenticated_body_only_without_a_proof_claim() {
    let d = runtime(true, false);
    let m = program(1, Some(&d));
    let prepared = prepare_module_for_lir(&m, GuardCarrierArch::AArch64).expect("prepare");
    let (mut functions, validation) = prepared
        .translate_with_tls_and_validation_with_license(TlsDialect::default(), &permit_unlicensed())
        .expect("translate");
    validation
        .replay_exact_module_bindings(&functions)
        .expect("replay");
    drop(validation);
    let calls = |functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)]| {
        functions
            .iter()
            .flat_map(|(f, _)| f.blocks.values())
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(&i.opcode, Opcode::Call { name, .. } if name == HELPER))
            .count()
    };
    assert_eq!(calls(&functions), 2);
    let mut claimed = functions.clone();
    let preparation = prepare_jit_lir_module_with_authority(
        &mut claimed,
        prepared.module(),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        OptLevel::O2,
        InlineOnlyAdmission::Withhold,
        &permit_unlicensed(),
        JitExternBindings::Any,
        InlineOnlyAuthority {
            dependencies: &[&d],
        },
    )
    .expect("prepare");
    assert!(!preparation.ran && preparation.skipped_for_proof_claim);
    assert_eq!(calls(&claimed), 2, "a proof claim splices nothing");
    let evidence = &preparation.inline_only;
    assert!(evidence.spliced.is_empty() && evidence.authenticated.is_empty());
    assert_eq!(evidence.withheld.len(), 1);
    assert_eq!(evidence.withheld[0].name, HELPER);
    assert!(
        evidence.withheld[0].reason.contains("OD-225"),
        "{:?}",
        evidence.withheld
    );
    let preparation = prepare_jit_lir_module_with_authority(
        &mut functions,
        prepared.module(),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        OptLevel::O2,
        InlineOnlyAdmission::DisclosedPremise,
        &permit_unlicensed(),
        JitExternBindings::Any,
        InlineOnlyAuthority {
            dependencies: &[&d],
        },
    )
    .expect("prepare");
    assert_eq!(calls(&functions), 0, "both calls spliced");
    let evidence = &preparation.inline_only;
    assert_eq!(evidence.spliced.len(), 1);
    assert_eq!(evidence.spliced[0].sites, 2);
    assert_eq!(evidence.authenticated.len(), 1);
    assert!(
        evidence.premises().is_empty(),
        "an authenticated splice discloses no premise: {:?}",
        evidence.premises()
    );
}

#[test]
fn the_jit_records_an_authenticated_splice_as_discharged_and_answers_as_the_definition() {
    let d = Arc::new(runtime(true, false));
    let m = program(1, Some(&d));
    let externs = HashMap::from([
        (HELPER.to_string(), host_read as *const u8),
        (SLOW.to_string(), host_read_slow as *const u8),
    ]);
    for (dependencies, authenticated) in [(vec![], false), (vec![Arc::clone(&d)], true)] {
        let mut config = CompilerConfig::jit_fast(host());
        config.opt_level = OptLevel::O2;
        // A compile that claims no proof, as the unauthenticated leg needs:
        // x86-64's default JIT mode claims proofs and so runs no inliner
        // (OD-225).
        config.jit_validation_mode_override =
            Some(trust_cg_codegen::compiler::JitValidationMode::Unchecked);
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .with_inline_only_dependencies(dependencies)
            .compile_module_to_jit(&m, &externs)
            .expect("compile_module_to_jit");
        let evidence = &result.inline_only_bodies;
        assert_eq!(evidence.spliced.len(), 1);
        assert_eq!(evidence.authenticated.len(), usize::from(authenticated));
        assert_eq!(evidence.premises().len(), usize::from(!authenticated));
        let entry: extern "C" fn(*const i64, i64) -> i64 = unsafe {
            result
                .buffer
                .get_fn_bound("entry")
                .expect("entry symbol")
                .into_inner()
        };
        let table: [i64; 4] = [3, 10, 20, 30];
        DEFINITION_CALLS.store(0, Ordering::SeqCst);
        assert_eq!(entry(table.as_ptr(), 0), 30);
        assert_eq!(entry(table.as_ptr(), 2), 30 - 1003);
        assert_eq!(DEFINITION_CALLS.load(Ordering::SeqCst), 0);
    }
}

#[test]
fn the_aot_seam_records_an_authenticated_splice_as_discharged() {
    let d = Arc::new(runtime(true, false));
    let m = program(1, Some(&d));
    let spec = trust_cg_codegen::target::TargetSpec::parse(&target_info().triple).expect("triple");
    for (dependencies, authenticated) in [(vec![], false), (vec![Arc::clone(&d)], true)] {
        let result = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O2,
                target: host(),
                ..CompilerConfig::default()
            },
            spec,
        )
        .with_codegen_license(permit_unlicensed())
        .with_inline_only_dependencies(dependencies)
        .compile(&m)
        .expect("compile");
        let evidence = &result.inline_only_bodies;
        assert_eq!(evidence.spliced.len(), 1);
        assert_eq!(evidence.spliced[0].sites, 2);
        assert_eq!(evidence.authenticated.len(), usize::from(authenticated));
        assert_eq!(evidence.premises().len(), usize::from(!authenticated));
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
