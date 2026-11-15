//! WS7.1 — `InsertField` / `InsertElement` are VALUE updates (F-111).
//!
//! trust-ir's `InsertField { aggregate, .. }` / `InsertElement { array, .. }`
//! produce a NEW aggregate value and leave the operand unchanged; the
//! validator, the reference interpreter and the Lean semantics agree. The
//! adapter used to lower them as an in-place update of the operand's storage
//! whose result ALIASED the operand, so any later use of the operand — a second
//! insert chain off one seed, a read of the old value, a loop-carried value, the
//! caller's argument behind a by-address parameter — observed the update. It
//! compiled without a diagnostic, and `--emit-proofs` certified the object.
//!
//! Every module here is JIT-compiled and run natively, and each result is
//! checked against BOTH its closed form and the trust-ir reference interpreter.
//!
//! * Positive: the proof program's own miscompile witnesses, vendored under
//!   `tests/fixtures/insert_field/` (the proof-program cache is not
//!   version-controlled): Part A-Lean `should_emit/struct.trust_ir`, c13's
//!   `shared_seed` / `shared_nomul`, and the Rust tuple shape `c13c` that a
//!   source-built `trustc` emits from ordinary safe Rust.
//! * Negative twin: `own_seed` / `struct.distinct_seed` give each chain a
//!   private seed; they must agree with their shared-seed twins on every
//!   vector (right answer for the right reason: sharing is what changed).
//! * Adversarial: `adversarial.trust_ir` — a loop-carried aggregate header with
//!   the old value read after the update, a block-parameter swap, a
//!   loop-carried aggregate `Load` re-loaded after a store, a PARAMETER base,
//!   and `insertelement` on an array read after the update.
//! * Named refusal: the STORE FORM (a pointer operand) is invalid trust-ir and
//!   is refused as `AggregateInsertNotValueForm`, never given a meaning.
//! * Mutation control (`--features mutation-knobs`): with
//!   `legacy_in_place_insert` on, the historical wrong answers come back
//!   (`dotOf(1,2,3,4) = 25`, `two_inserts(1,2) = 2002`, …), so these tests
//!   discriminate the fix rather than pass vacuously.
//!
//! Fixture licensing: the Part A-Lean module carries `body_gate: None`, so the
//! policy states `Permit` for claim-less bodies EXPLICITLY; the c13 modules are
//! `Gated` by the repro's own authority names, which the policy recognizes by
//! name. Nothing here is refused-and-counted-as-pass: every run is asserted.
//! JIT host coverage is AArch64 (macOS, Linux/glibc) and x86-64 (Linux,
//! macOS), the same set as WS7.2's `trust_ir_interp_differential`. x86-64 was
//! added 2026-10-20, once its ISel could select an aggregate `Select`
//! (DR-X86-AGGREGATE-SELECT-20261020); before that every module here refused
//! on that node and the whole target compiled to ZERO tests on this host,
//! which the gate census read as a skip.
#![cfg(any(
    all(
        target_arch = "aarch64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    ),
    all(
        target_arch = "x86_64",
        any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
    )
))]

use std::collections::HashMap;
use std::sync::Mutex;

use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, jit::ExecutableBuffer, pipeline::OptLevel,
};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{Module, Ty};

/// The mutation knob is process-global; every test that compiles holds this.
static KNOB: Mutex<()> = Mutex::new(());

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/insert_field");

fn parse(name: &str) -> Module {
    let path = format!("{FIXTURES}/{name}");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("parse {path}: {e:?}"))
}

/// Parse a fixture and require it to be VALID trust-ir: a finding about the
/// consumer is only meaningful on input the format itself accepts.
fn parse_valid(name: &str) -> Module {
    let module = parse(name);
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "{name} must be valid trust-ir"
    );
    module
}

fn license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default()
        .with_recognized_authority("c13-repro")
        .with_recognized_authority("trust-direct-lane-structural")
        .with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn compiler(opt: OptLevel) -> Compiler {
    let host = CoreHostJitTarget::detect().expect("supported native JIT test host");
    let target = if cfg!(target_arch = "aarch64") {
        Target::Aarch64
    } else {
        Target::X86_64
    };
    let mut config = CompilerConfig::jit_fast(target);
    config.opt_level = opt;
    // These tests ARE the check on these bytes — each result is compared with
    // both its closed form and the trust-ir reference interpreter — so they do
    // not rest on JIT certificate coverage. AArch64's default is already
    // Unchecked; stating it keeps both hosts on one lane.
    config.jit_validation_mode_override = Some(JitValidationMode::Unchecked);
    Compiler::new_for_target_spec(config, host.target_spec()).with_codegen_license(license())
}

fn jit(module: &Module, opt: OptLevel) -> ExecutableBuffer {
    compiler(opt)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|e| panic!("JIT compile of `{}` at {opt:?}: {e}", module.name))
        .buffer
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Call `name` natively with u64 arguments (arity 1..=4).
fn call(buffer: &ExecutableBuffer, name: &str, args: &[u64]) -> u64 {
    type F1 = extern "C" fn(u64) -> u64;
    type F2 = extern "C" fn(u64, u64) -> u64;
    type F3 = extern "C" fn(u64, u64, u64) -> u64;
    type F4 = extern "C" fn(u64, u64, u64, u64) -> u64;
    // SAFETY: every fixture function called here is declared with exactly
    // `args.len()` u64 parameters and one u64 result under a C-register ABI
    // (C or Rust), and `buffer` outlives the call.
    unsafe {
        match *args {
            [a] => buffer.get_fn_bound::<F1>(name).expect(name).as_ref()(a),
            [a, b] => buffer.get_fn_bound::<F2>(name).expect(name).as_ref()(a, b),
            [a, b, c] => buffer.get_fn_bound::<F3>(name).expect(name).as_ref()(a, b, c),
            [a, b, c, d] => buffer.get_fn_bound::<F4>(name).expect(name).as_ref()(a, b, c, d),
            _ => panic!("unsupported arity {}", args.len()),
        }
    }
}

/// The trust-ir reference interpreter's answer for `name(args)`.
fn interpret(module: &Module, name: &str, args: &[u64]) -> u64 {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let args = args
        .iter()
        .map(|a| InterpretValue::int(Ty::U64, i128::from(*a)).expect("u64 argument"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args)
        .unwrap_or_else(|e| panic!("interpret {name}: {e:?}"));
    let [ret] = outcome.returns.as_slice() else {
        panic!("{name}: expected one result, got {:?}", outcome.returns)
    };
    u64::try_from(ret.as_int().expect("integer result").as_unsigned()).expect("u64 result")
}

/// One vector: function, arguments, the closed-form expected result.
type Vector = (&'static str, &'static [u64], u64);

/// Compile `module` at every opt level and require native == closed form ==
/// reference interpreter on every vector.
fn assert_vectors(module: &Module, vectors: &[Vector]) {
    for &(name, args, want) in vectors {
        assert_eq!(
            interpret(module, name, args),
            want,
            "interpreter oracle disagrees with the closed form for {name}{args:?}"
        );
    }
    for opt in OPTS {
        let buffer = jit(module, opt);
        for &(name, args, want) in vectors {
            assert_eq!(
                call(&buffer, name, args),
                want,
                "{}: {name}{args:?} at {opt:?}",
                module.name
            );
        }
    }
}

const W: u64 = u64::MAX;

const PARTA_LEAN_STRUCT: &[Vector] = &[
    ("dotOf", &[1, 2, 3, 4], 11),
    // (2^64-1)*2 + (2^64-1)*3 mod 2^64 = 2^64 - 5
    ("dotOf", &[W, W, 2, 3], 18_446_744_073_709_551_611),
];

const C13_SEED: &[Vector] = &[
    ("two_inserts", &[1, 2], 1002),
    ("seed_survives", &[3], 7003),
    ("nonconst_base", &[1, 2, 4], 5006),
];

/// Row `FORMAT_HOME.native.struct` (Part A-Lean): two insert chains off ONE
/// seed. The same measurement is re-reported by rows `rerun.finding06`
/// (reproduced on the source-built backend) and `crit.misw10` (the critic's
/// "re-measure before calling it real"); all three are closed here.
#[test]
fn format_home_native_struct_two_chains_off_one_seed_compute_the_dot_product() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_vectors(&parse("parta_lean_struct.trust_ir"), PARTA_LEAN_STRUCT);
}

/// Row `verify.c13.L1` (the independent-reproduction lens): the from-scratch
/// shared-seed module, including a single insert followed by a read of the
/// OLD value and a non-constant base.
#[test]
fn verify_c13_l1_shared_seed_values_survive_their_inserts() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_vectors(&parse_valid("c13_shared_seed.trust_ir"), C13_SEED);
}

#[test]
fn verify_c13_l1_shared_nomul_subtracts_the_two_chains() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_vectors(
        &parse_valid("c13_shared_nomul.trust_ir"),
        &[("two_inserts_sub", &[9, 2], 7)],
    );
}

/// The shape a source-built `trustc` emits from ordinary safe Rust:
/// `let s = (0, 5); let mut p = s; let mut q = s; p.0 = a; q.0 = b;`.
#[test]
fn c13c_rust_tuple_copies_are_independent() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_vectors(
        &parse_valid("c13c_tuple.nolayout.trust_ir"),
        &[("c13_tuple", &[1, 2], 1002)],
    );
}

/// Negative twins: a private seed per chain changes nothing observable, so the
/// shared-seed modules above are right for the right reason. Row `AL.uf03`
/// ("giving the second chain its own seed constant fixes the object").
#[test]
fn al_uf03_private_seed_twins_agree_on_every_vector() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_vectors(
        &parse("parta_lean_struct.distinct_seed.trust_ir"),
        PARTA_LEAN_STRUCT,
    );
    assert_vectors(&parse_valid("c13_own_seed.trust_ir"), C13_SEED);
}

fn loop_old_after_update(n: u64) -> u64 {
    (0..n).sum()
}

fn swap_loop(n: u64) -> u64 {
    let (mut a, mut b) = ([1_u64, 0], [2_u64, 0]);
    let (mut i, mut acc) = (0_u64, 0_u64);
    loop {
        let a2 = [a[0], i];
        acc += a[0] + a[1];
        i += 1;
        if i < n {
            (a, b) = (b, a2);
        } else {
            return acc * 1000 + a2[0] * 10 + b[0];
        }
    }
}

fn loop_carried_load(n: u64) -> u64 {
    (0..n.saturating_sub(1)).sum()
}

fn adversarial_vectors() -> Vec<(&'static str, Vec<u64>, u64)> {
    let mut vectors = Vec::new();
    for n in [1_u64, 2, 3, 7] {
        vectors.push(("loop_old_after_update", vec![n], loop_old_after_update(n)));
        vectors.push(("swap_loop", vec![n], swap_loop(n)));
        vectors.push(("loop_carried_load", vec![n], loop_carried_load(n)));
    }
    for x in [0_u64, 7, 123] {
        vectors.push(("param_base_caller", vec![x], 2000 * x + 105));
    }
    for (x, i, old) in [(42_u64, 0_u64, 7_u64), (42, 1, 8), (5, 1, 8)] {
        vectors.push(("array_insert_element", vec![x, i], old * 1000 + x));
    }
    vectors
}

#[test]
fn adversarial_aggregate_values_keep_value_semantics() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("adversarial.trust_ir");
    let vectors = adversarial_vectors();
    let vectors: Vec<Vector> = vectors
        .iter()
        .map(|(name, args, want)| {
            let args: &'static [u64] = Box::leak(args.clone().into_boxed_slice());
            (*name, args, *want)
        })
        .collect();
    assert_vectors(&module, &vectors);
}

fn select_rotate_loop(n: u64) -> u64 {
    let (mut a, mut b) = ([1_u64, 0], [2_u64, 0]);
    let (mut i, mut acc) = (0_u64, 0_u64);
    loop {
        let sel = if i & 1 != 0 { a } else { b };
        let ins = [sel[0], i];
        let acc2 = acc * 3 + a[0];
        let i2 = i + 1;
        if i2 < n {
            (a, b, i, acc) = (b, sel, i2, acc2);
        } else {
            return acc2 * 1000 + ins[0] * 100 + ins[1] * 10 + b[0];
        }
    }
}

fn interior_swap_loop(n: u64) -> u64 {
    let (mut p0, pc, mut q) = ([1_u64, 10], 7_u64, [2_u64, 20]);
    let (mut i, mut acc) = (0_u64, 0_u64);
    loop {
        let a = p0;
        let p0_next = q;
        let acc2 = acc + a[0] + q[1];
        let i2 = i + 1;
        if i2 < n {
            (p0, q, i, acc) = (p0_next, a, i2, acc2);
        } else {
            return acc2 * 10_000 + p0_next[0] * 1000 + a[0] * 100 + pc;
        }
    }
}

fn call_result_loop(n: u64) -> u64 {
    let mut cur = [1_u64, 2, 3];
    let (mut i, mut acc) = (0_u64, 0_u64);
    loop {
        let next = [cur[0] + i, cur[2], cur[2]];
        let acc2 = acc + cur[1];
        let i2 = i + 1;
        if i2 < n {
            (cur, i, acc) = (next, i2, acc2);
        } else {
            return acc2 * 1_000_000 + next[0] * 10_000 + cur[0] * 100 + cur[1];
        }
    }
}

fn diamond_param_read(n: u64, k: u64) -> u64 {
    let mut s = [5_u64, 6];
    let (mut i, mut acc) = (0_u64, 0_u64);
    loop {
        let j = if i & 1 != 0 { [k, s[1]] } else { [s[0], i] };
        let acc2 = acc * 7 + s[0] + s[1] + j[0] + j[1];
        let i2 = i + 1;
        if i2 < n {
            (s, i, acc) = (j, i2, acc2);
        } else {
            return acc2;
        }
    }
}

fn review_vectors() -> Vec<(&'static str, Vec<u64>, u64)> {
    let mut vectors = Vec::new();
    for x in [0_u64, 42, 99] {
        vectors.push(("nested_interior_insert", vec![x], 1_001_200 + x));
    }
    for n in [1_u64, 2, 3, 6, 7] {
        vectors.push(("interior_swap_loop", vec![n], interior_swap_loop(n)));
        vectors.push(("select_rotate_loop", vec![n], select_rotate_loop(n)));
        vectors.push(("call_result_loop", vec![n], call_result_loop(n)));
        vectors.push(("diamond_param_read", vec![n, 40], diamond_param_read(n, 40)));
    }
    for x in [0_u64, 5, 42] {
        vectors.push(("tri_param_read_back", vec![x], 1_000_103 + x * 10_000));
    }
    for (x, i) in [(5_u64, 0_u64), (5, 1), (0, 1)] {
        let old = [[1_u64, 2], [3, 4]][i as usize];
        vectors.push((
            "array_struct_insert",
            vec![x, i],
            old[0] * 1000 + old[1] * 100 + x * 10 + 9,
        ));
    }
    vectors
}

/// Review corpus (`adversarial_review.trust_ir`): an insert whose base is an
/// aggregate-typed `extractfield` interior; a back edge whose argument is an
/// interior of, or a `select` over, the header parameters it rewrites; an
/// aggregate CALL RESULT (an unresolved storage root) on such an edge, with a
/// callee that inserts into its by-address parameter; a callee that reads its
/// by-reference parameter again after inserting into it; a struct element
/// inserted into an array of structs; and inserts on a dominating header
/// parameter inside a diamond whose join reads that parameter.
#[test]
fn review_aggregate_edges_interiors_and_calls_keep_value_semantics() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("adversarial_review.trust_ir");
    let vectors = review_vectors();
    let vectors: Vec<Vector> = vectors
        .iter()
        .map(|(name, args, want)| {
            let args: &'static [u64] = Box::leak(args.clone().into_boxed_slice());
            (*name, args, *want)
        })
        .collect();
    assert_vectors(&module, &vectors);
}

/// The store form (a POINTER operand) is invalid trust-ir, and this backend
/// refuses it by name instead of lowering it as an in-place memory write.
/// Row `verify.c13.L2` (the by-design lens, which measured the store form as
/// `FieldAccessInvalid` + interpreter `TypeError` and the adapter's reliance
/// on it).
#[test]
fn verify_c13_l2_store_form_insert_field_is_refused_by_name() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse("store_form.trust_ir");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        !errors.is_empty(),
        "the store form must be invalid trust-ir (the premise of the refusal)"
    );
    // WS7.3: the JIT's ingestion admission refuses the store form as the
    // trust-ir finding it is (`FieldAccessInvalid`), before the adapter.
    let err = compiler(OptLevel::O0)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect_err("the store form must be refused, not compiled");
    match &err {
        trust_cg_codegen::compiler::CompileError::InvalidTrustIr(refusal) => assert!(
            refusal.any(|error| matches!(
                error,
                trust_ir_build::ValidationError::FieldAccessInvalid { .. }
            )),
            "the ingestion refusal must name FieldAccessInvalid, got: {refusal}"
        ),
        other => panic!("must be refused at ingestion (WS7.3), got: {other}"),
    }
    // The adapter's own named refusal stays behind it, for every entry that
    // lowers a module without ingestion admission (the raw adapter entries).
    let text = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::AArch64,
        trust_cg_lower::TlsDialect::MachOTlv,
        &license(),
    )
    .expect_err("the adapter refuses the store form")
    .to_string();
    assert!(
        text.contains("`insertfield` base %1 has type Some(\"Ptr\")")
            && text.contains("store form"),
        "must be the named AggregateInsertNotValueForm refusal, got: {text}"
    );
}

/// A default build carries no mutation knob.
#[test]
fn default_build_has_no_mutation_knobs() {
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}

/// MUTATION CONTROL: with the historical in-place lowering switched back on,
/// every insert-shaped witness above computes its historical WRONG answer.
/// This is what makes the positive tests discriminating. (The loop-carried
/// `Load` case does not involve an insert, so this knob cannot break it; the
/// block-parameter slots that fix it are pinned by `loop_carried_load` above
/// and by `e2e_aarch64_aggregate_insert_linux`'s parameter-storage rows.)
#[cfg(feature = "mutation-knobs")]
#[test]
fn legacy_in_place_insert_reproduces_the_miscompile() {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            trust_cg_lower::mutation_knobs::set_legacy_in_place_insert(false);
        }
    }
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    trust_cg_lower::mutation_knobs::set_legacy_in_place_insert(true);
    let _reset = Reset;

    let historical: &[(&str, &[Vector])] = &[
        (
            "parta_lean_struct.trust_ir",
            &[("dotOf", &[1, 2, 3, 4], 25)],
        ),
        (
            "c13_shared_seed.trust_ir",
            &[
                ("two_inserts", &[1, 2], 2002),
                ("seed_survives", &[3], 3003),
                ("nonconst_base", &[1, 2, 4], 6006),
            ],
        ),
        (
            "c13_shared_nomul.trust_ir",
            &[("two_inserts_sub", &[9, 2], 0)],
        ),
        (
            "c13c_tuple.nolayout.trust_ir",
            &[("c13_tuple", &[1, 2], 2_002_002)],
        ),
    ];
    for (fixture, vectors) in historical {
        let module = parse(fixture);
        let buffer = jit(&module, OptLevel::O0);
        for &(name, args, wrong) in *vectors {
            assert_eq!(
                call(&buffer, name, args),
                wrong,
                "{fixture}: {name}{args:?} must reproduce the historical miscompile"
            );
        }
    }

    // Some single vectors happen to agree under aliasing (a one-iteration
    // loop, an insert of the value already there); every insert-shaped
    // function must still be caught on at least one of its vectors.
    let module = parse("adversarial.trust_ir");
    let buffer = jit(&module, OptLevel::O0);
    for name in [
        "loop_old_after_update",
        "swap_loop",
        "param_base_caller",
        "array_insert_element",
    ] {
        let caught = adversarial_vectors()
            .into_iter()
            .filter(|(n, ..)| *n == name)
            .any(|(_, args, want)| call(&buffer, name, &args) != want);
        assert!(caught, "{name}: the legacy in-place insert went undetected");
    }

    // `call_result_loop` is not in this list. Its only insert is in the
    // callee, on the by-reference parameter, and nothing reads that parameter
    // afterwards; the in-place insert used to be visible because it wrote the
    // CALLER's value. Since cc42cb5f8 the caller passes a caller-owned copy of
    // a by-reference composite, so the legacy insert cannot reach the caller
    // there (measured: every vector matches under the knob). It still pins the
    // call-result edge copy; `tri_param_read_back` observes the same
    // by-reference parameter insert inside the callee.
    let module = parse("adversarial_review.trust_ir");
    let buffer = jit(&module, OptLevel::O0);
    for name in [
        "nested_interior_insert",
        "interior_swap_loop",
        "tri_param_read_back",
        "array_struct_insert",
        "diamond_param_read",
    ] {
        let caught = review_vectors()
            .into_iter()
            .filter(|(n, ..)| *n == name)
            .any(|(_, args, want)| call(&buffer, name, &args) != want);
        assert!(caught, "{name}: the legacy in-place insert went undetected");
    }
}
