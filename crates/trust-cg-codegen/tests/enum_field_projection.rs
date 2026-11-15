//! WS7.6 — by-value `Ty::Enum` `ExtractField` lowers natively (F-112).
//!
//! trust-ir's enum value is `[tag, fields of the ACTIVE variant..]`. A
//! direct-tag enum (no descriptor, or a Direct descriptor equal to the
//! canonical shape) lowers to trust-cg's `Type::Enum`: the tag word at byte 0
//! and each variant's payload laid out C-style from one shared offset. The
//! adapter used to refuse every projection of it with "multi-index GEP
//! expected struct, tuple, or record type, got Enum".
//!
//! Every module here is JIT-compiled and run natively, and each result is
//! checked against BOTH its closed form (the Part A-Lean kernel-certified
//! values: `area (.rect 6 7) = 42`, `area (.sq 9) = 81`) and the trust-ir
//! reference interpreter.
//!
//! * Positive: Part A-Lean `should_emit/enum.trust_ir`'s `area` (tag read,
//!   a payload lane two variants share at one offset, a single-candidate
//!   lane), vendored with two `Const`-constructed callers as
//!   `parta_lean_enum.area.trust_ir`. The proof-program cache is not
//!   version-controlled, so the fixtures live under
//!   `tests/fixtures/enum_projection/`; `parta_lean_enum.trust_ir` is the
//!   verbatim module.
//! * Still refused, by name: the verbatim module's `areaOfRect` builds a
//!   variant with payload `InsertField`s, which need WS7.1(c)'s fresh-slot
//!   value lowering on the direct-tag carrier (`EnumPayloadInsertUnsupported`;
//!   struct, array and sequence inserts have it, the enum carrier does not).
//!   Row `FORMAT_HOME.native.enum` is fully closed only when it is wired.
//! * Negative twin: the same `area` plus a lane-0 `InsertField` (a re-tag,
//!   undefined behaviour in trust-ir) is refused as `EnumTagWriteUnsupported`.
//! * Mutation control (`--features mutation-knobs`): an off-by-one payload
//!   offset makes the native result disagree with the interpreter, and a
//!   perturbed trust-cg layout is refused as `EnumCanonicalLayoutDisagrees`.
//!
//! Fixture licensing: the Part A-Lean modules carry `body_gate: None`, so the
//! policy states `Permit` for claim-less bodies EXPLICITLY. Nothing here is
//! refused-and-counted-as-pass: every run is asserted.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

#[path = "common/admission_expect.rs"]
mod admission_expect;

use std::collections::HashMap;
use std::sync::Mutex;

use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, jit::ExecutableBuffer, pipeline::OptLevel,
};
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{EnumId, Module, Ty};

/// The mutation knobs are process-global; every test that compiles holds this.
static KNOB: Mutex<()> = Mutex::new(());

const FIXTURES: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/enum_projection"
);

/// Parse a fixture and require it to be VALID trust-ir at the pinned
/// trust-ir: a finding about the consumer is only meaningful on input the
/// format itself accepts.
fn parse_valid(name: &str) -> Module {
    let path = format!("{FIXTURES}/{name}");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let module =
        trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("parse {path}: {e:?}"));
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "{name} must be valid trust-ir"
    );
    module
}

fn compiler(opt: OptLevel) -> Compiler {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt;
    Compiler::new_for_target_spec(config, host.target_spec())
        .with_codegen_license(permit_unlicensed())
}

/// The license policy [`compiler`] states: `Permit` for the claim-less Part
/// A-Lean fixtures. trust-ir's admission of a refused fixture is judged under
/// it.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn jit(module: &Module, opt: OptLevel) -> ExecutableBuffer {
    compiler(opt)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|e| panic!("JIT compile of `{}` at {opt:?}: {e}", module.name))
        .buffer
}

/// The refusal text for `module`, which must NOT compile.
fn refusal(module: &Module) -> String {
    match compiler(OptLevel::O0).compile_module_to_jit(module, &HashMap::new()) {
        Ok(_) => panic!("`{}` must be refused", module.name),
        Err(e) => e.to_string(),
    }
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// trust-cg's canonical `Type::Enum` image of `Shape { sq(u64), rect(u64,
/// u64) }`, and trust-ir's (`enum_layout_shape`): a `u8` tag at byte 0, the
/// payload at byte 8, 24 bytes, 8-aligned.
#[repr(C)]
struct ShapeImage {
    tag: u8,
    pad: [u8; 7],
    first: u64,
    second: u64,
}

/// One `area` vector: the active variant's `[tag, fields..]` and the
/// kernel-certified closed form.
type AreaVector = (&'static [u64], u64);

const AREA: &[AreaVector] = &[
    (&[1, 6, 7], 42),
    (&[0, 9], 81),
    (&[1, 1 << 32, 1 << 32], 0),
    (&[1, 3, 3], 9),
    (&[0, u64::MAX], 1),
];

fn image(value: &[u64]) -> ShapeImage {
    ShapeImage {
        tag: u8::try_from(value[0]).expect("u8 tag"),
        // Poison the padding and the inactive payload word: a projection that
        // reads them instead of the named field must not pass by luck.
        pad: [0xA5; 7],
        first: value[1],
        second: value.get(2).copied().unwrap_or(0xDEAD_BEEF_DEAD_BEEF),
    }
}

fn call_area(buffer: &ExecutableBuffer, value: &[u64]) -> u64 {
    let shape = image(value);
    // SAFETY: `area` is declared `(enum.0) -> (u64)` under the Rust calling
    // convention; an aggregate parameter is passed BY ADDRESS in x0, and
    // `shape` is exactly the canonical image it reads. `buffer` and `shape`
    // outlive the call.
    unsafe {
        buffer
            .get_fn_bound::<extern "C" fn(*const ShapeImage) -> u64>("area")
            .expect("area")
            .as_ref()(&raw const shape)
    }
}

fn call0(buffer: &ExecutableBuffer, name: &str) -> u64 {
    // SAFETY: `name` is declared `() -> (u64)`, and `buffer` outlives the call.
    unsafe {
        buffer
            .get_fn_bound::<extern "C" fn() -> u64>(name)
            .expect(name)
            .as_ref()()
    }
}

/// The reference interpreter's `area(value)`.
fn interpret_area(module: &Module, value: &[u64]) -> u64 {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "area")
        .expect("area");
    let mut lanes = vec![InterpretValue::int(Ty::U8, i128::from(value[0])).expect("u8 tag")];
    lanes.extend(
        value[1..]
            .iter()
            .map(|v| InterpretValue::int(Ty::U64, i128::from(*v)).expect("u64 field")),
    );
    let argument = InterpretValue {
        ty: Ty::Enum(EnumId::new(0)),
        kind: InterpretValueKind::Aggregate(lanes),
    };
    let outcome = Interpreter::with_module(module)
        .execute_function(function, [argument])
        .unwrap_or_else(|e| panic!("interpret area{value:?}: {e:?}"));
    let [ret] = outcome.returns.as_slice() else {
        panic!("area: expected one result, got {:?}", outcome.returns)
    };
    u64::try_from(ret.as_int().expect("integer result").as_unsigned()).expect("u64 result")
}

fn interpret0(module: &Module, name: &str) -> u64 {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, std::iter::empty())
        .unwrap_or_else(|e| panic!("interpret {name}: {e:?}"));
    let [ret] = outcome.returns.as_slice() else {
        panic!("{name}: expected one result, got {:?}", outcome.returns)
    };
    u64::try_from(ret.as_int().expect("integer result").as_unsigned()).expect("u64 result")
}

/// Row `FORMAT_HOME.native.enum` (Part A-Lean): the HEAD-valid,
/// interpreter-executable enum module's `area` — a tag read, a payload lane
/// both variants place at one offset, and a lane only `rect` has — runs
/// natively and equals the interpreter and the kernel-certified values at
/// every opt level. The row's `areaOfRect` half stays open until WS7.1(c)
/// (see `rerun_finding07_*`).
#[test]
fn format_home_native_enum_area_projects_tag_and_payload_natively() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("parta_lean_enum.area.trust_ir");
    for &(value, want) in AREA {
        assert_eq!(
            interpret_area(&module, value),
            want,
            "interpreter oracle disagrees with the closed form for area{value:?}"
        );
    }
    let constructed = [("areaOfSq9", 81), ("areaOfRect67", 42)];
    for &(name, want) in &constructed {
        assert_eq!(interpret0(&module, name), want, "interpreter {name}");
    }
    for opt in OPTS {
        let buffer = jit(&module, opt);
        for &(value, want) in AREA {
            assert_eq!(call_area(&buffer, value), want, "area{value:?} at {opt:?}");
        }
        for &(name, want) in &constructed {
            assert_eq!(call0(&buffer, name), want, "{name} at {opt:?}");
        }
    }
}

/// Row `AL.uf04` (the A-Lean reviewer's lens on the same gap): a by-value
/// `Ty::Enum` projection is no longer refused with the GEP message — the
/// extract-only module compiles at every opt level.
#[test]
fn al_uf04_by_value_enum_extract_field_is_no_longer_refused_as_a_gep() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("parta_lean_enum.area.trust_ir");
    for opt in OPTS {
        let buffer = jit(&module, opt);
        assert!(buffer.get_fn_ptr_bound("area").is_some(), "area at {opt:?}");
    }
}

const PAYLOAD_INSERT: &str = r#"
module "payload_insert"
enum @S { a(u64), b(u64, u64) } id=0
functy.0 = () -> (u64)
rustcc fn @round_trip(functy.0) {
bb0:
    %0 = const u64 7
    %1 = const enum.0 { 1, 0, 0 }
    %2 = insertfield enum.0 %1, 1, %0
    %3 = extractfield u64 %2, 1
    ret %3
}
rustcc fn @chained(functy.0) {
bb0:
    %0 = const u64 6
    %1 = const u64 7
    %2 = const enum.0 { 1, 0, 0 }
    %3 = insertfield enum.0 %2, 1, %0
    %4 = insertfield enum.0 %3, 2, %1
    %5 = extractfield u64 %4, 1
    %6 = extractfield u64 %4, 2
    %7 = mul u64 %5, %6
    ret %7
}
rustcc fn @no_alias(functy.0) {
bb0:
    %0 = const u64 3
    %1 = const u64 5
    %2 = const enum.0 { 1, 0, 0 }
    %3 = insertfield enum.0 %2, 1, %0
    %4 = insertfield enum.0 %2, 1, %1
    %5 = extractfield u64 %3, 1
    %6 = extractfield u64 %4, 1
    %7 = mul u64 %5, %6
    ret %7
}
"#;

/// WS7.1(c): the direct-tag carrier's payload `InsertField` is WIRED, and it is
/// value-semantic. Three shapes, each checked against the trust-ir interpreter at every
/// optimisation level, because "no longer refused" is not "correct":
///
///  * `round_trip` — one insert, read back. 7.
///  * `chained` — two inserts on successive lanes, the shape `areaOfRect` builds. 6 * 7.
///  * `no_alias` — THE CONTROL THAT MATTERS. Two inserts into the SAME base value `%2`,
///    then read BOTH results. With fresh-slot semantics that is 3 * 5 = 15. If the insert
///    updated the operand's storage in place — the aliasing defect this lowering was
///    refused to avoid — the second write would clobber the first and both reads would
///    return 5, giving 25. A wrong-but-accepted lowering fails here; a refusal never
///    reaches here at all.
#[test]
fn ws71c_direct_tag_payload_insert_is_value_semantic() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_text("payload_insert", PAYLOAD_INSERT);
    assert_native_matches_interpreter(
        &module,
        &[("round_trip", 7), ("chained", 42), ("no_alias", 15)],
    );
}

/// Row `rerun.finding07` (the reproduction on a source-built backend): the
/// VERBATIM Part A-Lean module is no longer refused with "got Enum", and since
/// WS7.1(c) its `areaOfRect` — which builds a variant with two payload
/// `InsertField`s — is no longer refused either. It must now BUILD and compute
/// the rectangle's area, which is what the battery row `ir-tl-format_home`
/// measures. The fresh-slot property that makes the insert safe is pinned
/// separately by `ws71c_direct_tag_payload_insert_is_value_semantic`.
#[test]
fn rerun_finding07_verbatim_enum_module_builds_including_the_payload_insert() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("parta_lean_enum.trust_ir");
    for opt in OPTS {
        let buffer = jit(&module, opt);
        assert!(
            buffer.get_fn_ptr_bound("areaOfRect").is_some(),
            "areaOfRect must be emitted at {opt:?}"
        );
        assert!(
            buffer.get_fn_ptr_bound("area").is_some(),
            "area must still be emitted at {opt:?}"
        );
    }
}

/// Negative twin: the same `area` plus a lane-0 `InsertField` — a re-tag,
/// which trust-ir makes undefined behaviour — is refused by name.
#[test]
fn enum_tag_write_twin_is_refused_by_name() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let path = format!("{FIXTURES}/parta_lean_enum.tag_write.trust_ir");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    // Parsed, not validated: a trust-ir that ratifies WS2.2 rejects this twin
    // itself; the consumer must refuse it either way.
    let module =
        trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("parse {path}: {e:?}"));
    let message = refusal(&module);
    // This trust-ir pin ratifies WS2.2, so since WS7.3 ingestion admission
    // refuses the twin first, by trust-ir's own finding; without it the
    // backend's `EnumTagWriteUnsupported` is the refusal.
    match admission_expect::names_first_finding(&module, &message, &permit_unlicensed()) {
        Some(named) => assert!(
            named,
            "the re-tag must be refused by trust-ir's finding {:?}: {message}",
            admission_expect::first_finding(&module, &permit_unlicensed())
        ),
        None => assert!(
            message.contains("InsertField at element 0 would rewrite the discriminant"),
            "the re-tag must be refused as EnumTagWriteUnsupported: {message}"
        ),
    }
}

/// A default build carries no mutation knob.
#[test]
fn default_build_has_no_mutation_knobs() {
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}

/// Mutation control: with every payload projection emitted one byte past its
/// offset, the native `area` must disagree with the interpreter — so the
/// positive test discriminates the offset rather than passing vacuously.
#[cfg(feature = "mutation-knobs")]
#[test]
fn mutation_enum_payload_off_by_one_is_caught_by_the_differential() {
    use trust_cg_lower::mutation_knobs::set_enum_payload_off_by_one;
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            set_enum_payload_off_by_one(false);
        }
    }
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("parta_lean_enum.area.trust_ir");
    let _reset = Reset;
    set_enum_payload_off_by_one(true);
    for opt in OPTS {
        let buffer = jit(&module, opt);
        let mismatches = AREA
            .iter()
            .filter(|(value, _)| call_area(&buffer, value) != interpret_area(&module, value))
            .count();
        assert!(
            mismatches > 0,
            "the off-by-one payload offset went unnoticed at {opt:?}"
        );
    }
}

/// Mutation control: a trust-cg `Type::Enum` layout that disagrees with
/// trust-ir's `enum_layout_shape` refuses the projection by name.
#[cfg(feature = "mutation-knobs")]
#[test]
fn mutation_perturbed_enum_layout_is_refused_as_canonical_disagreement() {
    use trust_cg_lower::mutation_knobs::set_perturb_enum_canonical_layout;
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            set_perturb_enum_canonical_layout(false);
        }
    }
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("parta_lean_enum.area.trust_ir");
    let _reset = Reset;
    set_perturb_enum_canonical_layout(true);
    let message = refusal(&module);
    assert!(
        message.contains("canonical layout disagrees with trust-ir's `enum_layout_shape`")
            && message.contains("payload offset"),
        "a perturbed layout must be refused as EnumCanonicalLayoutDisagrees: {message}"
    );
}

// ---------------------------------------------------------------------------
// Review adversarials (WS7.6 review). Each module is VALID trust-ir, runs
// natively at O0-O3, and must equal the reference interpreter on every entry
// point. They exercise what the positive fixture does not: mixed-alignment
// payloads, a small (register-sized) enum, an enum crossing memory, `Select`
// and a block parameter, a nested enum payload, and an enum carried as a
// FIELD of a struct. The last one SIGSEGV'd before the review fix: the struct
// arm of `ExtractField` loaded a `Type::Enum` field as a scalar, handing its
// tag word to the enum projection as an address.
// ---------------------------------------------------------------------------

/// Parse inline trust-ir text and require it to be VALID.
fn parse_text(name: &str, text: &str) -> Module {
    let module =
        trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("parse {name}: {e:?}"));
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "{name} must be valid trust-ir"
    );
    module
}

/// Every `() -> (u64)` entry of `module` runs natively at O0-O3 and equals the
/// interpreter, which must itself equal the stated closed form.
fn assert_native_matches_interpreter(module: &Module, entries: &[(&str, u64)]) {
    for &(entry, want) in entries {
        assert_eq!(
            interpret0(module, entry),
            want,
            "interpreter oracle for `{}`::{entry}",
            module.name
        );
    }
    for opt in OPTS {
        let buffer = jit(module, opt);
        for &(entry, want) in entries {
            assert_eq!(
                call0(&buffer, entry),
                want,
                "native `{}`::{entry} at {opt:?}",
                module.name
            );
        }
    }
}

const MIXED: &str = r#"
module "mixed"
enum @M { a(u8), b(u64, u8), c(u32) } id=0
functy.0 = (enum.0) -> (u64)
functy.1 = () -> (u64)
rustcc fn @get(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    switch %1 [ 0: bb1 1: bb2 2: bb3 default: bb4 ]
bb1:
    %2 = extractfield u8 %0, 1
    %3 = zext u8 %2 to u64
    ret %3
bb2:
    %4 = extractfield u64 %0, 1
    %5 = extractfield u8 %0, 2
    %6 = zext u8 %5 to u64
    %7 = add u64 %4, %6
    ret %7
bb3:
    %8 = extractfield u32 %0, 1
    %9 = zext u32 %8 to u64
    ret %9
bb4:
    unreachable
}
rustcc fn @ga(functy.1) {
bb0:
    %0 = const enum.0 { 0, 200 }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gb(functy.1) {
bb0:
    %0 = const enum.0 { 1, 1000, 77 }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gc(functy.1) {
bb0:
    %0 = const enum.0 { 2, 4000000000 }
    %1 = call @func.0(%0)
    ret %1
}
"#;

/// Payload lanes of three different widths, each with ONE candidate variant,
/// behind a u8 tag with the payload at byte 8: `a`'s u8 at byte 8, `b`'s u64
/// at 8 and u8 at 16, `c`'s u32 at 8.
#[test]
fn review_mixed_width_payload_lanes_match_the_interpreter() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_text("mixed", MIXED);
    assert_native_matches_interpreter(&module, &[("ga", 200), ("gb", 1077), ("gc", 4_000_000_000)]);
}

const SCALARS: &str = r#"
module "scalars"
enum @K { a(bool, u16), b(f64), c, d(u64, u64, u8) } id=0
functy.0 = (enum.0) -> (u64)
functy.1 = () -> (u64)
rustcc fn @get(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    switch %1 [ 0: bb1 1: bb2 2: bb3 3: bb4 default: bb5 ]
bb1:
    %2 = extractfield bool %0, 1
    %3 = extractfield u16 %0, 2
    %4 = zext u16 %3 to u64
    %5 = zext bool %2 to u64
    %6 = add u64 %4, %5
    ret %6
bb2:
    %7 = extractfield f64 %0, 1
    %8 = fptoui f64 %7 to u64
    ret %8
bb3:
    %9 = const u64 5
    ret %9
bb4:
    %10 = extractfield u8 %0, 3
    %11 = zext u8 %10 to u64
    ret %11
bb5:
    unreachable
}
rustcc fn @ga(functy.1) {
bb0:
    %0 = const enum.0 { 0, true, 300 }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gb(functy.1) {
bb0:
    %0 = const enum.0 { 1, 12.75 }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gc(functy.1) {
bb0:
    %0 = const enum.0 { 2 }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gd(functy.1) {
bb0:
    %0 = const enum.0 { 3, 1, 2, 250 }
    %1 = call @func.0(%0)
    ret %1
}
"#;

/// `bool`, `u16`, `f64`, a field-less variant and a trailing `u8` after two
/// words: every scalar load type the direct path emits.
#[test]
fn review_scalar_payload_kinds_match_the_interpreter() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_text("scalars", SCALARS);
    assert_native_matches_interpreter(&module, &[("ga", 301), ("gb", 12), ("gc", 5), ("gd", 250)]);
}

const SMALL: &str = r#"
module "small"
enum @S { x(u8), y(u32) } id=0
functy.0 = (enum.0) -> (u64)
functy.1 = () -> (u64)
rustcc fn @get(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    switch %1 [ 0: bb1 1: bb2 default: bb3 ]
bb1:
    %2 = extractfield u8 %0, 1
    %3 = zext u8 %2 to u64
    ret %3
bb2:
    %4 = extractfield u32 %0, 1
    %5 = zext u32 %4 to u64
    ret %5
bb3:
    unreachable
}
rustcc fn @gx(functy.1) {
bb0:
    %0 = const enum.0 { 0, 9 }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gy(functy.1) {
bb0:
    %0 = const enum.0 { 1, 123456 }
    %1 = call @func.0(%0)
    ret %1
}
"#;
const MEMORY: &str = r#"
module "memory"
enum @S { x(u8), y(u64) } id=0
functy.0 = () -> (u64)
rustcc fn @gm(functy.0) {
bb0:
    %0 = const enum.0 { 1, 777 }
    %1 = alloca enum.0
    store enum.0 %0, ptr %1
    %2 = load enum.0, ptr %1
    %3 = extractfield u64 %2, 1
    ret %3
}
"#;
const SELECT: &str = r#"
module "select"
enum @S { x(u8), y(u64) } id=0
functy.0 = (bool) -> (u64)
functy.1 = () -> (u64)
rustcc fn @pick(functy.0) {
bb0(%0: bool):
    %1 = const enum.0 { 1, 111 }
    %2 = const enum.0 { 1, 222 }
    %3 = select enum.0 %0, %1, %2
    %4 = extractfield u64 %3, 1
    br bb1(%3)
bb1(%5: enum.0):
    %6 = extractfield u64 %5, 1
    %7 = add u64 %4, %6
    ret %7
}
rustcc fn @gt(functy.1) {
bb0:
    %0 = const bool true
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gf(functy.1) {
bb0:
    %0 = const bool false
    %1 = call @func.0(%0)
    ret %1
}
"#;

/// An 8-byte enum (register-sized, so an ABI that passed it by value in a
/// register would break the by-address projection), an enum stored to and
/// reloaded from an `alloca`, and an enum chosen by `Select` then passed as a
/// block parameter.
#[test]
fn review_small_enum_memory_select_and_block_param_match_the_interpreter() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_native_matches_interpreter(&parse_text("small", SMALL), &[("gx", 9), ("gy", 123_456)]);
    assert_native_matches_interpreter(&parse_text("memory", MEMORY), &[("gm", 777)]);
    assert_native_matches_interpreter(&parse_text("select", SELECT), &[("gt", 222), ("gf", 444)]);
}

const NESTED: &str = r#"
module "nested"
enum @I { p(u16), q(u64) } id=0
enum @O { n, w(u8, enum.0) } id=1
functy.0 = (enum.1) -> (u64)
functy.1 = () -> (u64)
rustcc fn @get(functy.0) {
bb0(%0: enum.1):
    %1 = extractfield u8 %0, 0
    switch %1 [ 0: bb1 1: bb2 default: bb5 ]
bb1:
    %2 = const u64 1
    ret %2
bb2:
    %3 = extractfield enum.0 %0, 2
    %4 = extractfield u8 %3, 0
    switch %4 [ 0: bb3 1: bb4 default: bb5 ]
bb3:
    %5 = extractfield u16 %3, 1
    %6 = zext u16 %5 to u64
    ret %6
bb4:
    %7 = extractfield u64 %3, 1
    ret %7
bb5:
    unreachable
}
rustcc fn @gp(functy.1) {
bb0:
    %0 = const enum.1 { 1, 3, { 0, 4242 } }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gq(functy.1) {
bb0:
    %0 = const enum.1 { 1, 3, { 1, 99999999999 } }
    %1 = call @func.0(%0)
    ret %1
}
"#;

/// An enum payload field that is itself an enum: the outer projection yields
/// the inner image by ADDRESS, and the inner projection reads through it.
#[test]
fn review_nested_enum_payload_is_projected_by_address() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_text("nested", NESTED);
    assert_native_matches_interpreter(&module, &[("gp", 4242), ("gq", 99_999_999_999)]);
}

const IN_STRUCT: &str = r#"
module "in_struct"
enum @S { x(u8), y(u64) } id=0
struct @P { u64, enum.0 } id=0
functy.0 = (struct.0) -> (u64)
functy.1 = () -> (u64)
rustcc fn @get(functy.0) {
bb0(%0: struct.0):
    %1 = extractfield enum.0 %0, 1
    %2 = extractfield u8 %1, 0
    switch %2 [ 0: bb1 1: bb2 default: bb3 ]
bb1:
    %3 = extractfield u8 %1, 1
    %4 = zext u8 %3 to u64
    ret %4
bb2:
    %5 = extractfield u64 %1, 1
    ret %5
bb3:
    unreachable
}
rustcc fn @gy(functy.1) {
bb0:
    %0 = const struct.0 { 5, { 1, 31337 } }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @gx(functy.1) {
bb0:
    %0 = const struct.0 { 5, { 0, 17 } }
    %1 = call @func.0(%0)
    ret %1
}
"#;

/// REVIEW FIX (miscompile, SIGSEGV). An enum carried as a FIELD of a struct is
/// extracted and then projected. The struct arm of `ExtractField` treated only
/// `Type::Struct`/`Type::Array` fields as by-address aggregates, so it
/// LOADED the `Type::Enum` field as a scalar and handed the enum projection
/// its tag word as an address. Unreachable before WS7.6 (the projection itself
/// was refused), so this increment made it reachable.
#[test]
fn review_enum_field_of_a_struct_is_projected_by_address() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_text("in_struct", IN_STRUCT);
    assert_native_matches_interpreter(&module, &[("gx", 17), ("gy", 31_337)]);
}

const DECLARED_STRUCT: &str = r#"
module "declared_struct"
enum @S { x(u8), y(u64) } id=0
struct @P { u64, enum.0 } size=24 align=8 id=0
functy.0 = (struct.0) -> (u64)
functy.1 = () -> (u64)
functy.2 = (enum.0) -> (u64)
rustcc fn @get(functy.0) {
bb0(%0: struct.0):
    %1 = extractfield enum.0 %0, 1
    %2 = extractfield u8 %1, 0
    switch %2 [ 0: bb1 1: bb2 default: bb3 ]
bb1:
    %3 = extractfield u8 %1, 1
    %4 = zext u8 %3 to u64
    ret %4
bb2:
    %5 = extractfield u64 %1, 1
    %6 = extractfield u64 %0, 0
    %7 = add u64 %5, %6
    ret %7
bb3:
    unreachable
}
rustcc fn @gy(functy.1) {
bb0:
    %0 = const struct.0 { 5, { 1, 31337 } }
    %1 = call @func.0(%0)
    ret %1
}
rustcc fn @wrap(functy.2) {
bb0(%0: enum.0):
    %1 = const struct.0 { 1000, { 0, 0 } }
    %2 = insertfield struct.0 %1, 1, %0
    %3 = call @func.0(%2)
    ret %3
}
rustcc fn @gw(functy.1) {
bb0:
    %0 = const enum.0 { 1, 2 }
    %1 = call @func.2(%0)
    ret %1
}
"#;

/// REVIEW FIX (miscompile, SIGSEGV), the declared-offset twin: a struct whose
/// producer-declared field offsets put the enum at byte 0 and the `u64` at
/// byte 16. Both the explicit-offset `ExtractField` arm (a scalar load of the
/// enum) and the explicit-offset `InsertField` arm (a scalar STORE of the
/// enum's address into the struct) treated `Type::Enum` as a scalar.
#[test]
fn review_enum_field_of_a_declared_offset_struct_round_trips() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let mut module = parse_text("declared_struct", DECLARED_STRUCT);
    // Reordered, rustc-style: the enum at byte 0, the u64 at byte 16.
    module.structs[0].fields[0].offset = Some(16);
    module.structs[0].fields[1].offset = Some(0);
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "declared_struct with reordered offsets must be valid trust-ir"
    );
    assert_native_matches_interpreter(&module, &[("gy", 31_342), ("gw", 1002)]);
}

const REPR16: &str = r#"
module "repr16"
enum @R repr(u16) { a(u8), b(u64) } id=0
functy.0 = () -> (u64)
rustcc fn @g(functy.0) {
bb0:
    %0 = const enum.0 { 1, 4242 }
    %1 = extractfield u16 %0, 0
    %2 = zext u16 %1 to u64
    %3 = extractfield u64 %0, 1
    %4 = add u64 %2, %3
    ret %4
}
"#;
const WIDE: &str = r#"
module "wide"
enum @W { a(u8), b(i128) } id=0
functy.0 = () -> (u64)
rustcc fn @g(functy.0) {
bb0:
    %0 = const enum.0 { 1, 70000 }
    %1 = extractfield i128 %0, 1
    %2 = trunc i128 %1 to u64
    ret %2
}
"#;

/// A declared `repr(u16)` tag (read at `u16`, payload at byte 8), and an
/// `i128` payload (16-byte aligned on both sides of the boundary).
#[test]
fn review_wide_tag_and_i128_payload_match_the_interpreter() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    assert_native_matches_interpreter(&parse_text("repr16", REPR16), &[("g", 4243)]);
    assert_native_matches_interpreter(&parse_text("wide", WIDE), &[("g", 70_000)]);
}

const TUPLE_FIELD: &str = r#"
module "tuple_field"
enum @T { a(u8), b((u32, u64)) } id=0
functy.0 = () -> (u64)
rustcc fn @g(functy.0) {
bb0:
    %0 = const enum.0 { 1, { 3, 900 } }
    %1 = extractfield (u32, u64) %0, 1
    %2 = extractfield u64 %1, 1
    %3 = extractfield u32 %1, 0
    %4 = zext u32 %3 to u64
    %5 = add u64 %2, %4
    ret %5
}
"#;

/// A tuple payload field: trust-ir's `enum_layout_shape` states no layout for
/// a `Ty::Tuple` at the pinned trust-ir, so the two sides cannot be shown to
/// agree and the projection is refused BY NAME, never lowered on trust-cg's
/// word alone.
#[test]
fn review_tuple_payload_without_a_trust_ir_layout_is_refused_by_name() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_text("tuple_field", TUPLE_FIELD);
    assert_eq!(interpret0(&module, "g"), 903, "interpreter oracle");
    let message = refusal(&module);
    assert!(
        message.contains("canonical layout disagrees with trust-ir's `enum_layout_shape`")
            && message.contains("availability"),
        "a tuple payload must be refused as EnumCanonicalLayoutDisagrees: {message}"
    );
}
