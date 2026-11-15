// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The x86-64 JIT's System V ABI envelope, measured through the JIT's own
//! compile path (`Compiler::compile_x86_64_to_jit`: its host-JIT pipeline
//! profile, LinearScan with the Greedy fallback, frame lowering, branch
//! resolution and encoding) rather than a hand-configured pipeline.
//!
//! The capture below records the exact inputs of the certification boundary
//! (`x86_jit_certify_functions`): the normalized pre-relocation bytes of each
//! function and its symbolic fixup manifest. Those are the bytes the
//! certificate-cache key binds and the bytes the envelope owner judges.

use std::cell::RefCell;

// The shapes below are hand-built and carry no codegen license
// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
// DG-73); they translate through the main test module's Permit helper, so no
// shape is measured (or refused) because the license silently refused it.
use super::tests::permit_translate_module_for_arch;
use super::*;

/// One function's certification inputs, as the JIT handed them over.
#[derive(Debug, Clone)]
pub(super) struct CapturedCertifyInput {
    pub(super) name: String,
    pub(super) code: Vec<u8>,
    pub(super) manifest: Vec<u8>,
    pub(super) isel: trust_cg_lower::x86_64_isel::X86ISelFunction,
    pub(super) lir: (trust_cg_lower::Function, trust_cg_lower::ProofContext),
}

thread_local! {
    static CAPTURE: RefCell<Option<Vec<CapturedCertifyInput>>> = const { RefCell::new(None) };
}

/// Called by `x86_jit_certify_functions` (test builds only). Records nothing
/// unless a test on this thread armed the capture.
pub(super) fn record_certify_inputs(
    isel_funcs: &[trust_cg_lower::x86_64_isel::X86ISelFunction],
    lir_functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
    code: &[u8],
    ranges: &[std::ops::Range<usize>],
    manifests: &[Vec<u8>],
) {
    CAPTURE.with(|capture| {
        if let Some(captured) = capture.borrow_mut().as_mut() {
            for (((func, lir), range), manifest) in isel_funcs
                .iter()
                .zip(lir_functions)
                .zip(ranges)
                .zip(manifests)
            {
                captured.push(CapturedCertifyInput {
                    name: func.name.clone(),
                    code: code.get(range.clone()).unwrap_or_default().to_vec(),
                    manifest: manifest.clone(),
                    isel: func.clone(),
                    lir: lir.clone(),
                });
            }
        }
    });
}

fn with_capture<T>(run: impl FnOnce() -> T) -> (T, Vec<CapturedCertifyInput>) {
    CAPTURE.with(|capture| *capture.borrow_mut() = Some(Vec::new()));
    let result = run();
    let captured = CAPTURE.with(|capture| capture.borrow_mut().take().unwrap_or_default());
    (result, captured)
}

/// A one-function module `subject` of `shape`, calling the extern
/// `abort_probe` where the shape calls.
pub(super) fn envelope_shape_module(shape: &str) -> trust_ir::Module {
    use trust_ir_build::ModuleBuilder;
    let mut mb = ModuleBuilder::new("x86_envelope_shapes");
    let void_ty = mb.add_func_type(vec![], vec![]);
    let params = if shape.contains("param") {
        vec![trust_ir::Ty::I64]
    } else {
        vec![]
    };
    let ty = mb.add_func_type(params.clone(), vec![]);
    let abort = shape
        .contains("call")
        .then(|| mb.declare_function("abort_probe", void_ty));
    let mut fb = mb.function("subject", ty);
    let entry = fb.create_block();
    for param in &params {
        fb.add_block_param(entry, param.clone());
    }
    if shape.starts_with("jump_") {
        let next = fb.create_block();
        fb.switch_to_block(entry);
        fb.br(next, vec![]);
        fb.switch_to_block(next);
    } else {
        fb.switch_to_block(entry);
    }
    if let Some(abort) = abort {
        fb.call_void(abort, vec![]);
    }
    if shape.starts_with("return") {
        fb.ret(vec![]);
    } else {
        fb.unreachable();
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

extern "C" fn abort_probe_stand_in() {}

/// Run the JIT's own x86-64 compile path for `shape` under `config`, with
/// `mode` and `profile_hooks`, and return its result plus the captured
/// certification inputs of `subject`.
pub(super) fn jit_compile_shape(
    config: CompilerConfig,
    shape: &str,
    mode: JitValidationMode,
    profile_hooks: crate::jit::ProfileHookMode,
) -> (
    Result<JitCompilationResult, CompileError>,
    Option<CapturedCertifyInput>,
) {
    let module = envelope_shape_module(shape);
    let lir =
        permit_translate_module_for_arch(&module, guard_carrier_arch_for_target(Target::X86_64))
            .expect("the shape translates");
    let mut externs: HashMap<String, *const u8> = HashMap::new();
    externs.insert(
        "abort_probe".to_owned(),
        abort_probe_stand_in as extern "C" fn() as *const u8,
    );
    let compiler = Compiler::new(config);
    let definitions = x86_test_module_definitions(lir.iter().map(|(function, _)| function));
    let (result, captured) = with_capture(|| {
        compiler.compile_x86_64_to_jit(
            lir,
            &externs,
            JitExternalSymbolResolutionPolicy::ExplicitOnly,
            profile_hooks,
            mode,
            Instant::now(),
            false,
            Vec::new(),
            &definitions,
        )
    });
    let subject = captured.into_iter().find(|input| input.name == "subject");
    (result, subject)
}

fn hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The configurations the pinned bytes are measured under: the production
/// `jit_fast` profile (LinearScan), the same at O0, and the Greedy profile at
/// O2 (the JIT's fallback allocator core).
fn envelope_probe_configs() -> [(&'static str, CompilerConfig); 3] {
    [
        ("jit_fast", CompilerConfig::jit_fast(Target::X86_64)),
        (
            "jit_fast_o0",
            CompilerConfig {
                opt_level: OptLevel::O0,
                ..CompilerConfig::jit_fast(Target::X86_64)
            },
        ),
        (
            "greedy_o2",
            CompilerConfig {
                opt_level: OptLevel::O2,
                enable_jit_fast_regalloc: false,
                ..CompilerConfig::jit_fast(Target::X86_64)
            },
        ),
    ]
}

/// The canonical symbolic fixup manifest encoding, spelled out independently
/// of `x86_symbolic_fixup_manifest`: magic, row count, then per call row the
/// certificate-relative disp32 offset, kind 0, the length-prefixed callee and
/// the exact-module flag.
pub(super) fn expected_call_manifest(rows: &[(u64, &str, bool)]) -> Vec<u8> {
    let mut out = b"trust-cg.jit.x86_64-symbolic-fixups.v1\0".to_vec();
    out.extend_from_slice(&(rows.len() as u64).to_be_bytes());
    for (offset, callee, exact) in rows {
        out.extend_from_slice(&offset.to_be_bytes());
        out.push(0);
        out.extend_from_slice(&6u64.to_be_bytes());
        out.extend_from_slice(b"callee");
        out.extend_from_slice(&(callee.len() as u64).to_be_bytes());
        out.extend_from_slice(callee.as_bytes());
        out.push(u8::from(*exact));
    }
    out
}

/// The profile call-counter trampoline this host's JIT prepends inside the
/// certified range (`emit_x86_64_profile_counter_trampoline`, non-Windows):
/// `push rax; pushfq; movabs rax, imm64; lock inc qword [rax]; popfq; pop rax`,
/// with the imm64 still zero before the counter pointer is patched in.
const CALL_COUNTER_PREFIX: [u8; 18] = [
    0x50, 0x9c, 0x48, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0xf0, 0x48, 0xff, 0x00, 0x9d, 0x58,
];

/// T1: the exact bytes and fixups the x86-64 JIT hands its certification
/// boundary for every envelope shape, measured through the JIT's own compile
/// path. These fix the envelope recognizer's closed opcode set: every
/// admitted shape is `push rbp; mov rbp, rsp` then either `pop rbp; ret` or
/// `call rel32; ud2` with one call row at the rel32 hole. The one- and
/// two-block panic entries encode identically (branch resolution elides the
/// fallthrough `jmp`). A dead parameter copy survives (`mov rax, rdi`,
/// `48 89 f8`), and profile call counters prepend a trampoline inside the
/// certified range; neither is in the envelope's closed set. The bytes are
/// the same under every probed configuration.
#[test]
fn x86_jit_envelope_shapes_have_pinned_bytes() {
    let frame = [0x55, 0x48, 0x89, 0xe5];
    let call = [0xe8, 0, 0, 0, 0, 0x0f, 0x0b];
    let expected: [(&str, Vec<u8>, Vec<(u64, &str, bool)>); 7] = [
        ("return", [&frame[..], &[0x5d, 0xc3]].concat(), vec![]),
        (
            "return_unused_param",
            [&frame[..], &[0x48, 0x89, 0xf8, 0x5d, 0xc3]].concat(),
            vec![],
        ),
        (
            "call_trap",
            [&frame[..], &call[..]].concat(),
            vec![(5, "abort_probe", false)],
        ),
        (
            "jump_call_trap",
            [&frame[..], &call[..]].concat(),
            vec![(5, "abort_probe", false)],
        ),
        (
            "dead_param_call_trap",
            [&frame[..], &[0x48, 0x89, 0xf8], &call[..]].concat(),
            vec![(8, "abort_probe", false)],
        ),
        ("trap", [&frame[..], &[0x0f, 0x0b]].concat(), vec![]),
        ("jump_trap", [&frame[..], &[0x0f, 0x0b]].concat(), vec![]),
    ];
    for (label, config) in envelope_probe_configs() {
        for (shape, code, rows) in &expected {
            for hooks in [
                crate::jit::ProfileHookMode::None,
                crate::jit::ProfileHookMode::CallCounts,
            ] {
                let (_, captured) = jit_compile_shape(
                    config.clone(),
                    shape,
                    JitValidationMode::CachedVerified,
                    hooks,
                );
                let captured = captured.unwrap_or_else(|| {
                    panic!("{label} {shape} {hooks:?}: certification inputs were not captured")
                });
                let (code, rows): (Vec<u8>, Vec<(u64, &str, bool)>) = match hooks {
                    crate::jit::ProfileHookMode::CallCounts => (
                        [&CALL_COUNTER_PREFIX[..], code].concat(),
                        rows.iter()
                            .map(|(offset, callee, exact)| {
                                (offset + CALL_COUNTER_PREFIX.len() as u64, *callee, *exact)
                            })
                            .collect(),
                    ),
                    _ => (code.clone(), rows.clone()),
                };
                assert_eq!(
                    hex(&captured.code),
                    hex(&code),
                    "{label} {shape} {hooks:?}: certified bytes"
                );
                assert_eq!(
                    captured.manifest,
                    expected_call_manifest(&rows),
                    "{label} {shape} {hooks:?}: symbolic fixup manifest"
                );
            }
        }
    }
}

/// T5(a): the codegen manifest encoder and the verify-owned parser agree, row
/// for row, for call rows and every symbol kind, so the envelope judges
/// exactly the fixups the cache key binds.
#[test]
fn x86_symbolic_fixup_manifest_round_trips_through_the_envelope_parser() {
    use crate::x86_64::pipeline::{X86CallFixup, X86GlobalRefFixup, X86SymbolRefFixupKind};
    use trust_cg_verify::x86_source_bound_envelope::{
        X86FixupRow, parse_x86_symbolic_fixup_manifest,
    };
    let calls = [
        X86CallFixup {
            offset: 1,
            callee: "a".into(),
            exact_module: false,
        },
        X86CallFixup {
            offset: 30,
            callee: "local".into(),
            exact_module: true,
        },
    ];
    let symbols = [
        (X86SymbolRefFixupKind::GlobalRef, 0u8),
        (X86SymbolRefFixupKind::ExternRefGot, 1),
        (X86SymbolRefFixupKind::TlsTlv, 2),
        (X86SymbolRefFixupKind::ExactFunctionAddr, 3),
    ];
    let globals: Vec<X86GlobalRefFixup> = symbols
        .iter()
        .enumerate()
        .map(|(i, (kind, _))| X86GlobalRefFixup {
            offset: 10 + 4 * i,
            symbol: format!("g{i}"),
            kind: *kind,
        })
        .collect();
    for body_offset in [0u64, 18] {
        let manifest =
            crate::jit_cert::x86_symbolic_fixup_manifest(&calls, &globals, body_offset).unwrap();
        let mut expected: Vec<X86FixupRow> = calls
            .iter()
            .map(|call| X86FixupRow::Call {
                offset: body_offset + call.offset as u64,
                callee: call.callee.clone(),
                exact_module: call.exact_module,
            })
            .chain(
                globals
                    .iter()
                    .zip(symbols)
                    .map(|(global, (_, kind))| X86FixupRow::Symbol {
                        offset: body_offset + global.offset as u64,
                        symbol: global.symbol.clone(),
                        kind,
                    }),
            )
            .collect();
        expected.sort_by_key(|row| row.offset());
        assert_eq!(parse_x86_symbolic_fixup_manifest(&manifest), Ok(expected));
    }
    let empty = crate::jit_cert::x86_symbolic_fixup_manifest(&[], &[], 0).unwrap();
    assert_eq!(parse_x86_symbolic_fixup_manifest(&empty), Ok(vec![]));
}

/// T5(i): with replay refused, the verifying JIT refuses the empty void body
/// and both panic-entry spellings BY THE ENVELOPE'S NAME, on its real compile
/// path, in both verifying modes. Before the envelope existed the reason was
/// the generic "the emitted stream produced none". The trap-only shapes and
/// the call-counter spelling (outside the closed byte set) keep their
/// previous refusals.
#[test]
fn x86_jit_envelope_refusal_names_the_missing_replay() {
    use trust_cg_verify::x86_source_bound_envelope::{
        X86_DIVERGING_CALL_ENVELOPE_NAME, X86_ENVELOPE_NEEDS_REPLAY, X86_VOID_RETURN_ENVELOPE_NAME,
    };
    let generic = "the emitted stream produced none (every function needs non-vacuous evidence)";
    crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
        for mode in [
            JitValidationMode::CachedVerified,
            JitValidationMode::AlwaysVerify,
        ] {
            for (shape, hooks, expected) in [
                (
                    "return",
                    crate::jit::ProfileHookMode::None,
                    vec![
                        X86_VOID_RETURN_ENVELOPE_NAME,
                        X86_ENVELOPE_NEEDS_REPLAY,
                        "| return target byte 0`; 0 of 18 parts Valid; replay refused: TCG_REFINE_SOLVER=0)",
                    ],
                ),
                (
                    "call_trap",
                    crate::jit::ProfileHookMode::None,
                    vec![
                        X86_DIVERGING_CALL_ENVELOPE_NAME,
                        X86_ENVELOPE_NEEDS_REPLAY,
                        "| callee-entry alignment`; 0 of 10 parts Valid; replay refused: TCG_REFINE_SOLVER=0)",
                    ],
                ),
                (
                    "jump_call_trap",
                    crate::jit::ProfileHookMode::None,
                    vec![
                        X86_DIVERGING_CALL_ENVELOPE_NAME,
                        X86_ENVELOPE_NEEDS_REPLAY,
                        "| callee-entry alignment`; 0 of 10 parts Valid; replay refused: TCG_REFINE_SOLVER=0)",
                    ],
                ),
                ("trap", crate::jit::ProfileHookMode::None, vec![generic]),
                (
                    "jump_trap",
                    crate::jit::ProfileHookMode::None,
                    vec!["non_vacuous_function_evidence"],
                ),
                (
                    "call_trap",
                    crate::jit::ProfileHookMode::CallCounts,
                    vec![generic],
                ),
            ] {
                let (result, _) =
                    jit_compile_shape(CompilerConfig::jit_fast(Target::X86_64), shape, mode, hooks);
                let error = match result {
                    Ok(_) => {
                        panic!("{shape} {hooks:?} {mode:?}: published without a replayed proof")
                    }
                    Err(error) => error.to_string(),
                };
                for needle in expected {
                    assert!(
                        error.contains(needle),
                        "{shape} {hooks:?} {mode:?}: `{needle}` missing from: {error}"
                    );
                }
            }
        }
    });
}

/// A PARTLY replayed envelope is refused as a whole: an outcome with every
/// part but one Valid (whatever the other verdict, at the first, a middle or
/// the last position) yields exactly ONE `verified: false` certificate, no
/// verified certificate and no export, naming the first part without a Valid
/// replay, the count of Valid parts and the replay's reason. (The verify-side
/// `envelope_credit_requires_a_valid_replay_of_every_part` pins the same rule
/// on reports whose outcome carries an export per part.)
#[test]
fn x86_jit_envelope_partly_valid_outcome_is_one_named_refusal() {
    use trust_cg_verify::VerificationResult as V;
    use trust_cg_verify::x86_source_bound_envelope::{
        X86_ENVELOPE_NEEDS_REPLAY, X86_VOID_RETURN_ENVELOPE_NAME, X86EnvelopeOutcome,
        X86EnvelopePartVerdict,
    };
    let names = ["return target byte 0", "rsp after ret", "rbp restored"];
    for missing in 0..names.len() {
        for other in [
            None,
            Some(V::Unknown {
                reason: "incomplete".into(),
            }),
        ] {
            let parts: Vec<X86EnvelopePartVerdict> = names
                .iter()
                .enumerate()
                .map(|(index, label)| X86EnvelopePartVerdict {
                    name: format!("{X86_VOID_RETURN_ENVELOPE_NAME} | {label}"),
                    verdict: if index == missing {
                        other.clone()
                    } else {
                        Some(V::Valid)
                    },
                    detail: (index == missing).then(|| "AY TIMEOUT".to_owned()),
                })
                .collect();
            let outcome = X86EnvelopeOutcome::Built {
                theorem_name: X86_VOID_RETURN_ENVELOPE_NAME,
                parts,
                exports: Vec::new(),
            };
            assert!(!outcome.is_credited());
            let certs = x86_64_abi_envelope_outcome_certificates("subject", &outcome);
            let label = format!("part {missing} is {other:?}");
            assert_eq!(certs.len(), 1, "{label}: {certs:?}");
            let cert = &certs[0];
            assert!(!cert.verified, "{label}");
            assert!(cert.source_bound_obligation.is_none(), "{label}");
            assert_eq!(cert.rule_name, X86_VOID_RETURN_ENVELOPE_NAME, "{label}");
            assert_eq!(
                cert.category,
                crate::proof_evidence::X86_ABI_ENVELOPE_CATEGORY,
                "{label}"
            );
            let expected = format!(
                "{X86_ENVELOPE_NEEDS_REPLAY} (first part without a Valid replay: \
                 `{X86_VOID_RETURN_ENVELOPE_NAME} | {}`; 2 of 3 parts Valid; AY TIMEOUT)",
                names[missing]
            );
            assert_eq!(cert.strength, expected, "{label}");
            assert!(!x86_certificates_show_verified_semantics(&certs), "{label}");
        }
    }
}

/// T5(ii): wrong final bytes or fixups on the real certification boundary
/// fail closed BY NAME, whether or not replay is available: the mismatch is
/// found before any theorem is replayed.
#[test]
fn x86_jit_envelope_mismatches_fail_closed_by_name() {
    let (_, void) = jit_compile_shape(
        CompilerConfig::jit_fast(Target::X86_64),
        "return",
        JitValidationMode::CachedVerified,
        crate::jit::ProfileHookMode::None,
    );
    let (_, call) = jit_compile_shape(
        CompilerConfig::jit_fast(Target::X86_64),
        "call_trap",
        JitValidationMode::CachedVerified,
        crate::jit::ProfileHookMode::None,
    );
    let (void, call) = (void.unwrap(), call.unwrap());
    let renamed = expected_call_manifest(&[(5, "abort_probf", false)]);
    let flipped = expected_call_manifest(&[(5, "abort_probe", true)]);
    let symbol_row = {
        // The call row plus a GlobalRef row the linker would also patch.
        let mut rows = crate::jit_cert::x86_symbolic_fixup_manifest(
            &[crate::x86_64::pipeline::X86CallFixup {
                offset: 5,
                callee: "abort_probe".into(),
                exact_module: false,
            }],
            &[crate::x86_64::pipeline::X86GlobalRefFixup {
                offset: 1,
                symbol: "g".into(),
                kind: crate::x86_64::pipeline::X86SymbolRefFixupKind::GlobalRef,
            }],
            0,
        )
        .unwrap();
        rows.shrink_to_fit();
        rows
    };
    let cases: Vec<(&str, &CapturedCertifyInput, Vec<u8>, Vec<u8>, &str)> = vec![
        (
            "renamed callee",
            &call,
            call.code.clone(),
            renamed,
            "is bound to `abort_probf`",
        ),
        (
            "flipped exact flag",
            &call,
            call.code.clone(),
            flipped,
            "the manifest binds `abort_probe` (exact module function)",
        ),
        (
            "extra symbol row",
            &call,
            call.code.clone(),
            symbol_row,
            "a body with one call has 2 fixup row(s)",
        ),
        (
            "dropped pop",
            &void,
            vec![0x55, 0x48, 0x89, 0xe5, 0xc3],
            void.manifest.clone(),
            "RSP is rsp0-8 where the return needs rsp0+0",
        ),
    ];
    for replay in ["0", "1"] {
        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", replay)], || {
            for (label, input, code, manifest, needle) in &cases {
                let compiler = Compiler::new(CompilerConfig::jit_fast(Target::X86_64));
                for mode in [
                    JitValidationMode::CachedVerified,
                    JitValidationMode::AlwaysVerify,
                ] {
                    let error = compiler
                        .x86_jit_certify_functions(
                            mode,
                            std::slice::from_ref(&input.isel),
                            std::slice::from_ref(&input.lir),
                            code,
                            std::slice::from_ref(&(0..code.len())),
                            std::slice::from_ref(manifest),
                            &x86_test_module_definitions([&input.lir.0]),
                        )
                        .expect_err("a wrong envelope must fail closed");
                    let error = error.to_string();
                    assert!(
                        error.contains("x86-64 ABI envelope mismatch") && error.contains(needle),
                        "{label} {mode:?} replay={replay}: {error}"
                    );
                }
            }
        });
    }
}

/// The cache never stores or serves an envelope verdict that is not bound to
/// the request's reusable authority. A report without a Valid replay (here,
/// replay refused) carries no reusable identity, exactly as a Valid but
/// unbound replay does, so the predicates refuse both; an entry with no
/// envelope serves only a function the owner does not admit.
#[test]
fn x86_jit_envelope_cache_predicates_require_a_bound_replay() {
    let (_, void) = jit_compile_shape(
        CompilerConfig::jit_fast(Target::X86_64),
        "return",
        JitValidationMode::CachedVerified,
        crate::jit::ProfileHookMode::None,
    );
    let void = void.unwrap();
    let (_, trap) = jit_compile_shape(
        CompilerConfig::jit_fast(Target::X86_64),
        "trap",
        JitValidationMode::CachedVerified,
        crate::jit::ProfileHookMode::None,
    );
    let trap = trap.unwrap();
    let abi = Some(trust_cg_verify::X86SourceBoundAbi::SystemV);
    let verification_policy = X86JitVerificationPolicy::capture();
    // The request captures the replay policy, so refuse replay while it is
    // captured (an authority-carrying host would otherwise replay Valid).
    let (request, report) =
        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            let request = shared_x86_64_function_verifier()
                .capture_request_with_mode(verification_policy.provenance_xcheck);
            let report = x86_jit_envelope_report(
                &void.lir.0,
                &void.name,
                &void.code,
                &void.manifest,
                abi,
                &request,
            );
            (request, report)
        });
    let report = report.expect("the empty void body is admitted");
    assert!(!report.is_valid());
    assert!(!x86_jit_envelope_is_storable(Some(&report), &request));
    let none: Option<&trust_cg_verify::x86_source_bound_envelope::X86EnvelopeReport> = None;
    assert!(x86_jit_envelope_is_storable(none, &request));
    assert!(!x86_jit_cached_envelope_admits(
        Some(&report),
        &request,
        &void.lir.0,
        &void.name,
        &void.code,
        &void.manifest,
        abi
    ));
    // An entry without an envelope cannot serve an admitted function.
    assert!(!x86_jit_cached_envelope_admits(
        none,
        &request,
        &void.lir.0,
        &void.name,
        &void.code,
        &void.manifest,
        abi
    ));
    // ...but serves one the owner does not admit.
    assert!(x86_jit_cached_envelope_admits(
        none,
        &request,
        &trap.lir.0,
        &trap.name,
        &trap.code,
        &trap.manifest,
        abi
    ));
}

/// A report state the cache predicates must refuse although it is Valid. The
/// verifier hands such reports out (a Valid replay through the fresh path is
/// unbound; a cached report meets requests of other authorities), but codegen
/// cannot construct an `X86EnvelopeReport`, so the predicates are driven here
/// through their [`X86EnvelopeReuse`] view.
struct EnvelopeState {
    valid: bool,
    bound_to_request: bool,
    same_input: bool,
}

impl X86EnvelopeReuse for EnvelopeState {
    fn is_valid(&self) -> bool {
        self.valid
    }
    fn reusable_for(&self, _: &trust_cg_verify::FunctionVerificationRequest) -> bool {
        self.valid && self.bound_to_request
    }
    fn matches_input(
        &self,
        _: &trust_cg_lower::Function,
        _: &str,
        _: &[u8],
        _: &[u8],
        _: Option<trust_cg_verify::X86SourceBoundAbi>,
    ) -> bool {
        self.same_input
    }
}

/// Critique gap 8, behaviourally: a VALID envelope that is not bound to the
/// request's reusable authority (or is bound to another authority) is never
/// stored and never serves a warm hit; only a Valid envelope bound to this
/// request's authority, for exactly this input, does. A predicate that asked
/// only `is_valid()` accepts the first two rows and fails here.
#[test]
fn x86_jit_envelope_cache_predicates_refuse_a_valid_but_unbound_envelope() {
    let (_, void) = jit_compile_shape(
        CompilerConfig::jit_fast(Target::X86_64),
        "return",
        JitValidationMode::CachedVerified,
        crate::jit::ProfileHookMode::None,
    );
    let void = void.unwrap();
    let abi = Some(trust_cg_verify::X86SourceBoundAbi::SystemV);
    let request = shared_x86_64_function_verifier()
        .capture_request_with_mode(X86JitVerificationPolicy::capture().provenance_xcheck);
    let admits = |state: &EnvelopeState| {
        x86_jit_cached_envelope_admits(
            Some(state),
            &request,
            &void.lir.0,
            &void.name,
            &void.code,
            &void.manifest,
            abi,
        )
    };
    // (valid, bound, same input) -> (storable, admits a hit)
    let rows = [
        ((true, false, true), (false, false)),
        ((true, false, false), (false, false)),
        ((true, true, false), (true, false)),
        ((true, true, true), (true, true)),
        ((false, false, true), (false, false)),
    ];
    for ((valid, bound_to_request, same_input), (storable, hit)) in rows {
        let state = EnvelopeState {
            valid,
            bound_to_request,
            same_input,
        };
        assert_eq!(
            x86_jit_envelope_is_storable(Some(&state), &request),
            storable,
            "store: valid={valid} bound={bound_to_request} same_input={same_input}"
        );
        assert_eq!(
            admits(&state),
            hit,
            "hit: valid={valid} bound={bound_to_request} same_input={same_input}"
        );
    }
}

/// Tool-gated: the same refusals on REAL reports. With a Valid envelope
/// replay available, a report replayed with the cache disabled
/// (`TCG_NO_PROOF_CACHE`, the fresh path) is Valid but unbound and is not
/// storable, and a report bound to one request's authority serves no hit for
/// a request of another authority (a different `TRUST_CG_AY_TIMEOUT_MS`).
/// SKIPS (printing why) without a Valid replay.
#[test]
fn x86_jit_envelope_cache_predicates_on_live_valid_reports() {
    let test = "x86_jit_envelope_cache_predicates_on_live_valid_reports";
    if crate::env_lock::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        eprintln!("SKIP {test}: TCG_REFINE_SOLVER=0");
        return;
    }
    let (_, void) = jit_compile_shape(
        CompilerConfig::jit_fast(Target::X86_64),
        "return",
        JitValidationMode::CachedVerified,
        crate::jit::ProfileHookMode::None,
    );
    let void = void.unwrap();
    let abi = Some(trust_cg_verify::X86SourceBoundAbi::SystemV);
    let mode = X86JitVerificationPolicy::capture().provenance_xcheck;
    let capture = || shared_x86_64_function_verifier().capture_request_with_mode(mode);
    let report_for = |request: &trust_cg_verify::FunctionVerificationRequest| {
        x86_jit_envelope_report(
            &void.lir.0,
            &void.name,
            &void.code,
            &void.manifest,
            abi,
            request,
        )
        .expect("the empty void body is admitted")
    };
    let request = capture();
    let report = report_for(&request);
    if !report.is_valid() || request.reuse_identity().is_none() {
        eprintln!(
            "SKIP {test}: no reusable Valid envelope replay on this host (valid={}, reusable \
             request={})",
            report.is_valid(),
            request.reuse_identity().is_some()
        );
        return;
    }
    let admits = |report, request| {
        x86_jit_cached_envelope_admits(
            Some(report),
            request,
            &void.lir.0,
            &void.name,
            &void.code,
            &void.manifest,
            abi,
        )
    };
    assert!(x86_jit_envelope_is_storable(Some(&report), &request));
    assert!(admits(&report, &request));
    let foreign =
        crate::env_lock::with_env_overrides(&[("TRUST_CG_AY_TIMEOUT_MS", "30001")], capture);
    assert!(
        foreign.reuse_identity().is_some() && foreign.reuse_identity() != request.reuse_identity()
    );
    assert!(!x86_jit_envelope_is_storable(Some(&report), &foreign));
    assert!(!admits(&report, &foreign));
    let (unbound, fresh) =
        crate::env_lock::with_env_overrides(&[("TCG_NO_PROOF_CACHE", "1")], || {
            let fresh = capture();
            (report_for(&fresh), fresh)
        });
    assert!(unbound.is_valid(), "the fresh path replays Valid too");
    assert!(!x86_jit_envelope_is_storable(Some(&unbound), &fresh));
    assert!(!x86_jit_envelope_is_storable(Some(&unbound), &request));
    assert!(!admits(&unbound, &request));
    eprintln!("X86_ENVELOPE_JIT cache predicates refused a live Valid but unbound envelope");
}

/// T5(iii), tool-gated: with an admitted AY and a capable Clean, the
/// verifying JIT publishes the empty void body and the panic entry EXACTLY
/// when every part of their envelope theorem has a Valid replay, and
/// otherwise refuses them naming the missing replay. A published function
/// carries one verified `x86_abi_envelope` certificate per part, each whose
/// `source_bound_obligation` is that non-degenerate part, and its bundle has
/// discharge evidence. SKIPS
/// without authority. On a host whose admitted pair cannot certify the
/// envelope (recorded in the verify crate's qualification test), only the
/// refusal direction is exercised, and the test says so.
#[test]
fn x86_verifying_jit_publishes_exactly_on_a_valid_envelope_replay() {
    use trust_cg_verify::x86_source_bound_envelope::X86_ENVELOPE_NEEDS_REPLAY;
    if crate::env_lock::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        eprintln!(
            "SKIP x86_verifying_jit_publishes_exactly_on_a_valid_envelope_replay: TCG_REFINE_SOLVER=0"
        );
        return;
    }
    if trust_cg_verify::ay_bridge::admitted_proof_solver().is_none() {
        eprintln!(
            "SKIP x86_verifying_jit_publishes_exactly_on_a_valid_envelope_replay: {}",
            trust_cg_verify::ay_bridge::proof_toolchain_unavailable_reason()
                .unwrap_or_else(|| "no admitted AY with a capable checker".into())
        );
        return;
    }
    for shape in ["return", "call_trap", "jump_call_trap"] {
        for mode in [
            JitValidationMode::AlwaysVerify,
            JitValidationMode::CachedVerified,
        ] {
            let (result, captured) = jit_compile_shape(
                CompilerConfig::jit_fast(Target::X86_64),
                shape,
                mode,
                crate::jit::ProfileHookMode::None,
            );
            let captured = captured.unwrap();
            // Re-derive the certificates at the boundary to inspect them.
            let compiler = Compiler::new(CompilerConfig {
                emit_proofs: true,
                ..CompilerConfig::jit_fast(Target::X86_64)
            });
            let certified = compiler.x86_jit_certify_functions(
                mode,
                std::slice::from_ref(&captured.isel),
                std::slice::from_ref(&captured.lir),
                &captured.code,
                std::slice::from_ref(&(0..captured.code.len())),
                std::slice::from_ref(&captured.manifest),
                &x86_test_module_definitions([&captured.lir.0]),
            );
            match certified {
                Ok((proofs, per_fn)) => {
                    let proofs = proofs.expect("a verifying mode returns certificates");
                    let envelopes: Vec<&ProofCertificate> = proofs
                        .iter()
                        .filter(|c| c.category == crate::proof_evidence::X86_ABI_ENVELOPE_CATEGORY)
                        .collect();
                    // One verified certificate per replayed part.
                    let parts = if shape == "return" { 18 } else { 10 };
                    assert_eq!(envelopes.len(), parts, "{shape} {mode:?}: {proofs:?}");
                    for envelope in &envelopes {
                        assert!(envelope.verified && envelope.strength == "Formal");
                        let bound = envelope
                            .source_bound_obligation
                            .as_ref()
                            .expect("a verified envelope part carries its theorem");
                        assert_eq!(bound.obligation().name, envelope.rule_name);
                        assert!(!bound.obligation().is_degenerate());
                        assert!(bound.matches_x86_envelope_input(
                            &captured.lir.0,
                            &captured.name,
                            &captured.code,
                            &captured.manifest,
                            Some(trust_cg_verify::X86SourceBoundAbi::SystemV)
                        ));
                    }
                    assert!(crate::proof_evidence::bundle_has_discharge_evidence(
                        &proofs
                    ));
                    assert!(per_fn.iter().all(|f| f.verified));
                    assert!(
                        result.is_ok(),
                        "{shape} {mode:?}: the JIT must publish: {:?}",
                        result.as_ref().err().map(ToString::to_string)
                    );
                    eprintln!("X86_ENVELOPE_JIT {shape} {mode:?} published on a Valid replay");
                }
                Err(error) => {
                    let error = error.to_string();
                    assert!(
                        error.contains(X86_ENVELOPE_NEEDS_REPLAY),
                        "{shape} {mode:?}: {error}"
                    );
                    assert!(
                        result.is_err(),
                        "{shape} {mode:?}: published without a proof"
                    );
                    eprintln!(
                        "X86_ENVELOPE_JIT {shape} {mode:?} refused (no Valid replay on this \
                         host's admitted pair): {error}"
                    );
                }
            }
        }
    }
}

/// Tool-gated: in `CachedVerified` mode an envelope-decided function is
/// never served from the certificate cache, even with a Valid, bound envelope
/// replay: the store also requires the function's x86 body report to be
/// reusable, and a body report is reusable only with at least one genuinely
/// verified row, which these bodies do not have. Each certification is a
/// miss that re-runs the verifier (the AY verdict for each part is then
/// cheap to repeat) and publishes again. SKIPS (printing why) without a Valid
/// replay.
#[test]
fn x86_verifying_jit_recertifies_envelope_shapes_on_every_cached_call() {
    let test = "x86_verifying_jit_recertifies_envelope_shapes_on_every_cached_call";
    if crate::env_lock::var_os("TCG_REFINE_SOLVER").is_some_and(|value| value == "0") {
        eprintln!("SKIP {test}: TCG_REFINE_SOLVER=0");
        return;
    }
    for shape in ["return", "call_trap"] {
        let (_, captured) = jit_compile_shape(
            CompilerConfig::jit_fast(Target::X86_64),
            shape,
            JitValidationMode::CachedVerified,
            crate::jit::ProfileHookMode::None,
        );
        let captured = captured.unwrap();
        let cache = std::sync::Arc::new(crate::jit_cert::JitCertCache::new());
        let compiler = Compiler::new(CompilerConfig {
            emit_proofs: true,
            ..CompilerConfig::jit_fast(Target::X86_64)
        })
        .with_jit_cert_cache(cache.clone());
        let certify = || {
            compiler.x86_jit_certify_functions(
                JitValidationMode::CachedVerified,
                std::slice::from_ref(&captured.isel),
                std::slice::from_ref(&captured.lir),
                &captured.code,
                std::slice::from_ref(&(0..captured.code.len())),
                std::slice::from_ref(&captured.manifest),
                &x86_test_module_definitions([&captured.lir.0]),
            )
        };
        if certify().is_err() {
            eprintln!("SKIP {test}: {shape}: no Valid envelope replay on this host");
            return;
        }
        let (_, per_fn) = certify().expect("the second certification publishes again");
        assert!(per_fn.iter().all(|f| f.verified));
        let (hits, misses, _, runs) = cache.stats();
        assert_eq!(
            (hits, misses, runs),
            (0, 2, 2),
            "{shape}: an envelope-decided function is re-verified, never served"
        );
        eprintln!("X86_ENVELOPE_JIT {shape} CachedVerified re-verified on the second call");
    }
}
