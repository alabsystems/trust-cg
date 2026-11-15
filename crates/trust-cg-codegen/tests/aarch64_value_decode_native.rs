// trust-cg-codegen/tests/aarch64_value_decode_native.rs - silicon differential for the decoded-word value model
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Native AArch64 differential for `trust_cg_verify::aarch64_value_decode_proofs`.
//!
//! The decoded-word obligations behind the MOV (register), scalar FMOV, SMULL,
//! BFM, RBIT and `ADD #imm12, LSL #12` coverage credits give each word its Arm
//! ARM semantics by TRANSCRIPTION; nothing in those obligations can catch a
//! transcription that is internally consistent and wrong. This target JITs the
//! real encoder's word for each form, executes it on the host CPU over a
//! deterministic sample of register values, and requires the silicon result
//! to equal BOTH the decoded word's denotation and the machine-IR intent. The
//! result registers are read whole (X0 for general-register writes, D0 for FP
//! writes), so a W write that failed to clear bits 63:32, or an S write that
//! left D0[63:32], disagrees.
//!
//! Runs on AArch64 macOS and AArch64 Linux. It samples one CPU, finitely: it
//! is a differential control, not a proof. SP forms and MRS are not executed
//! here (MRS TPIDR_EL0 has its own native control in `jit_mrs_tpidr`).

#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::collections::HashMap;

use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{D0, D1, H0, PReg, S0, S1, W0, W1, X0, X1};
use trust_cg_verify::aarch64_value_decode_proofs::{
    FieldOverrides, a64_value_intent, decode_a64_value_word, denote_a64_value_word,
};
use trust_cg_verify::smt::{EvalEnv, EvalResult, SmtExpr};

/// Argument/result register bank of a test function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bank {
    Gpr,
    Fpr,
}

struct Case {
    name: String,
    params: Vec<Bank>,
    result: Bank,
    inst: MachInst,
}

fn preg(p: PReg) -> MachOperand {
    MachOperand::PReg(p)
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn case(name: impl Into<String>, params: &[Bank], result: Bank, inst: MachInst) -> Case {
    Case {
        name: name.into(),
        params: params.to_vec(),
        result,
        inst,
    }
}

fn cases() -> Vec<Case> {
    use AArch64Opcode as O;
    use Bank::{Fpr, Gpr};
    let mk = MachInst::new;
    let mut cases = vec![
        case(
            "mov_w",
            &[Gpr, Gpr],
            Gpr,
            mk(O::MovR, vec![preg(W0), preg(W1)]),
        ),
        case(
            "mov_x",
            &[Gpr, Gpr],
            Gpr,
            mk(O::MovR, vec![preg(X0), preg(X1)]),
        ),
        case(
            "fmov_s",
            &[Fpr, Fpr],
            Fpr,
            mk(O::FmovFprFpr, vec![preg(S0), preg(S1)]),
        ),
        case(
            "fmov_d",
            &[Fpr, Fpr],
            Fpr,
            mk(O::FmovFprFpr, vec![preg(D0), preg(D1)]),
        ),
        case(
            "fmov_w_s",
            &[Fpr],
            Gpr,
            mk(O::FmovFprGpr, vec![preg(W0), preg(S0)]),
        ),
        case(
            "fmov_x_d",
            &[Fpr],
            Gpr,
            mk(O::FmovFprGpr, vec![preg(X0), preg(D0)]),
        ),
        case(
            "fmov_s_w",
            &[Gpr],
            Fpr,
            mk(O::FmovGprFpr, vec![preg(S0), preg(W0)]),
        ),
        case(
            "fmov_d_x",
            &[Gpr],
            Fpr,
            mk(O::FmovGprFpr, vec![preg(D0), preg(X0)]),
        ),
        case(
            "smull",
            &[Gpr, Gpr],
            Gpr,
            mk(O::Smull, vec![preg(X0), preg(W0), preg(W1)]),
        ),
        case("rbit_w", &[Gpr], Gpr, mk(O::Rbit, vec![preg(W0), preg(W0)])),
        case("rbit_x", &[Gpr], Gpr, mk(O::Rbit, vec![preg(X0), preg(X0)])),
    ];
    if std::arch::is_aarch64_feature_detected!("fp16") {
        cases.push(case(
            "fmov_w_h",
            &[Fpr],
            Gpr,
            mk(O::FmovFprGpr, vec![preg(W0), preg(H0)]),
        ));
        cases.push(case(
            "fmov_h_x",
            &[Gpr],
            Fpr,
            mk(O::FmovGprFpr, vec![preg(H0), preg(X0)]),
        ));
    }
    for (datasize, dst, src) in [(32u32, W0, W1), (64, X0, X1)] {
        for (lsb, width) in [
            (0, 1),
            (0, datasize),
            (8, 5),
            (datasize - 1, 1),
            (3, datasize - 3),
        ] {
            let immr = i64::from((datasize - lsb) % datasize);
            let imms = i64::from(width - 1);
            cases.push(case(
                format!("bfm_w{datasize}_lsb{lsb}_width{width}"),
                &[Gpr, Gpr],
                Gpr,
                mk(O::Bfm, vec![preg(dst), preg(src), imm(immr), imm(imms)]),
            ));
        }
        for imm12 in [0, 1, 0x123, 0xFFF] {
            cases.push(case(
                format!("add_lsl12_w{datasize}_{imm12:#x}"),
                &[Gpr],
                Gpr,
                mk(O::AddRIShift12, vec![preg(dst), preg(dst), imm(imm12)]),
            ));
        }
    }
    cases
}

fn function(case: &Case) -> MachFunction {
    let ty = |bank: Bank| match bank {
        Bank::Gpr => Type::I64,
        Bank::Fpr => Type::F64,
    };
    let sig = Signature::new(
        case.params.iter().map(|&b| ty(b)).collect(),
        vec![ty(case.result)],
    );
    let mut func = MachFunction::new(case.name.clone(), sig);
    let entry = func.entry;
    let id = func.push_inst(case.inst.clone());
    func.append_inst(entry, id);
    const RETURNS_X0: &[PReg] = &[X0];
    const RETURNS_D0: &[PReg] = &[D0];
    let result = match case.result {
        Bank::Gpr => RETURNS_X0,
        Bank::Fpr => RETURNS_D0,
    };
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(result);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);
    func
}

/// Deterministic 64-bit LCG.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ (self.0 >> 31)
    }
}

fn evaluate(expr: &SmtExpr, env: &EvalEnv) -> u128 {
    match expr.try_eval(env).expect("model evaluates") {
        EvalResult::Bv(value) => u128::from(value),
        EvalResult::Bv128(value) => value,
        other => panic!("non-bitvector model result {other:?}"),
    }
}

/// Bind argument `i` of `bank` to its register-file variables. Only the low
/// doubleword of an FP argument register is defined by the ABI; the model's
/// view of the upper half is set to zero and never read by these forms.
fn bind(env: &mut EvalEnv, params: &[Bank], values: &[u64]) {
    let (mut gpr, mut fpr) = (0, 0);
    for (&bank, &value) in params.iter().zip(values) {
        match bank {
            Bank::Gpr => {
                env.insert(format!("x{gpr}"), value);
                gpr += 1;
            }
            Bank::Fpr => {
                env.insert(format!("v{fpr}_lo"), value);
                env.insert(format!("v{fpr}_hi"), 0);
                fpr += 1;
            }
        }
    }
}

#[test]
fn silicon_agrees_with_the_decoded_word_and_the_intent() {
    let cases = cases();
    let functions: Vec<MachFunction> = cases.iter().map(function).collect();
    let jit = JitCompiler::new(JitConfig::default());
    let buffer = jit
        .compile_raw(&functions, &HashMap::new())
        .expect("compile_raw must accept every single-instruction probe");
    let mut rng = Lcg(0xA64_DEC0DE);
    let edges = [
        0u64,
        1,
        u64::MAX,
        0x8000_0000,
        0x7FFF_FFFF,
        0xFFFF_FFFF,
        0x1_0000_0000,
        0x8000_0000_0000_0000,
        0x7FFF_FFFF_FFFF_FFFF,
    ];
    let mut executed = 0usize;
    let mut upper_half_cleared: HashMap<&str, usize> = HashMap::new();
    for case in &cases {
        let word = encode_instruction(&case.inst).expect("encodes");
        let decoded = decode_a64_value_word(word)
            .unwrap_or_else(|error| panic!("{}: {word:#010x}: {error}", case.name));
        let effect = denote_a64_value_word(&decoded, &FieldOverrides::default())
            .unwrap_or_else(|error| panic!("{}: {error}", case.name));
        let intent =
            a64_value_intent(&case.inst).unwrap_or_else(|error| panic!("{}: {error}", case.name));
        assert_eq!(effect.dest, intent.dest, "{}", case.name);
        for sample in 0..600 {
            let values: Vec<u64> = (0..case.params.len())
                .map(|i| {
                    if sample < edges.len() * edges.len() && case.params.len() <= 2 {
                        let pick = if i == 0 {
                            sample / edges.len()
                        } else {
                            sample % edges.len()
                        };
                        edges[pick % edges.len()]
                    } else {
                        rng.next()
                    }
                })
                .collect();
            // SAFETY: each probe was built with exactly this signature; the
            // AAPCS64 passes i64 in X0/X1 and f64 in D0/D1, returning in X0 or
            // D0. The function pointers do not outlive `buffer`.
            let silicon: u64 = unsafe {
                match (case.params.as_slice(), case.result) {
                    ([Bank::Gpr], Bank::Gpr) => {
                        let f = buffer
                            .get_fn_bound::<extern "C" fn(u64) -> u64>(&case.name)
                            .unwrap();
                        (*f.as_ref())(values[0])
                    }
                    ([Bank::Gpr, Bank::Gpr], Bank::Gpr) => {
                        let f = buffer
                            .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(&case.name)
                            .unwrap();
                        (*f.as_ref())(values[0], values[1])
                    }
                    ([Bank::Fpr], Bank::Gpr) => {
                        let f = buffer
                            .get_fn_bound::<extern "C" fn(f64) -> u64>(&case.name)
                            .unwrap();
                        (*f.as_ref())(f64::from_bits(values[0]))
                    }
                    ([Bank::Gpr], Bank::Fpr) => {
                        let f = buffer
                            .get_fn_bound::<extern "C" fn(u64) -> f64>(&case.name)
                            .unwrap();
                        (*f.as_ref())(values[0]).to_bits()
                    }
                    ([Bank::Fpr, Bank::Fpr], Bank::Fpr) => {
                        let f = buffer
                            .get_fn_bound::<extern "C" fn(f64, f64) -> f64>(&case.name)
                            .unwrap();
                        (*f.as_ref())(f64::from_bits(values[0]), f64::from_bits(values[1]))
                            .to_bits()
                    }
                    other => panic!("{}: unsupported probe shape {other:?}", case.name),
                }
            };
            let mut env = EvalEnv::default();
            bind(&mut env, &case.params, &values);
            // Only the observable low 64 bits of a 128-bit V write are read back.
            let low64 = |value: u128| value as u64;
            let model = low64(evaluate(&effect.value, &env));
            let intended = low64(evaluate(&intent.value, &env));
            assert_eq!(
                silicon, model,
                "{} ({word:#010x}) inputs {values:x?}: silicon {silicon:#x} vs decoded-word model \
                 {model:#x}",
                case.name
            );
            assert_eq!(
                silicon, intended,
                "{} inputs {values:x?}: silicon {silicon:#x} vs machine-IR intent {intended:#x}",
                case.name
            );
            // Teeth: the narrow copies must observably CLEAR the upper half.
            // A model that copied the whole source register would have been
            // indistinguishable if the probe could not see bits 63:32.
            if matches!(
                case.name.as_str(),
                "mov_w" | "fmov_s" | "fmov_w_s" | "fmov_s_w"
            ) {
                let source = *values.last().unwrap();
                if source >> 32 != 0 && silicon != source {
                    *upper_half_cleared.entry(case.name.as_str()).or_default() += 1;
                }
            }
            executed += 1;
        }
    }
    eprintln!(
        "aarch64 decoded-value silicon differential: {} probes, {executed} executions",
        cases.len()
    );
    assert!(executed >= cases.len() * 600);
    for name in ["mov_w", "fmov_s", "fmov_w_s", "fmov_s_w"] {
        assert!(
            upper_half_cleared.get(name).copied().unwrap_or(0) > 0,
            "{name}: no sample distinguished a zero-extending write from a full copy"
        );
    }
}
