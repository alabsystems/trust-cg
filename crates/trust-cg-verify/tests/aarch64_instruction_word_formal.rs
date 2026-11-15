// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Can the external solver lane (AY, with Clean checking its proof) discharge
//! the instruction-derived obligations of `aarch64_instruction_word_proofs`?
//!
//! The always-on test builds the probe set and checks every obligation holds
//! in-process. The solver probe runs only with
//! `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` (the strict proof lane's gate): it sends
//! each probe location obligation to `ay_bridge::verify_with_ay` and prints the
//! outcome. It fails only on a counterexample, which would be a soundness
//! finding. Every other answer (a solver or admission error, a timeout, an
//! `unknown`, or an unsat the checker did not accept) is printed, not
//! asserted: a stock-Rust build admits no AY and answers an error for every
//! location.
//!
//! A location whose two terms are syntactically identical
//! (`ProofObligation::is_degenerate`) asks the solver only `t != t`: a checked
//! certificate of it shows the solver lane works, not that the word does what
//! the instruction names (the in-process decision already did that, by term
//! identity). Both the probe and the query dump mark those locations.
//!
//! Whatever the probe prints, no row is credited: an instruction-derived
//! obligation binds the word to the instruction's operands, not to a source
//! instruction, so even a checked certificate of it is not proof of the
//! lowering (see the module documentation).

use trust_cg_ir::{AArch64Opcode as O, BlockId, MachInst, MachOperand as Arg, PReg, SpecialReg};
use trust_cg_verify::aarch64_instruction_word_proofs::{
    InstructionWordVerdict, Outcome, instruction_word_verdict,
};
use trust_cg_verify::ay_bridge::{AYConfig, AYResult, lane_smt2_query, verify_with_ay};
use trust_cg_verify::lowering_proof::VerificationConfig;

fn preg(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}

/// One instruction per admitted family, with its register views and
/// immediates as the Darwin corpus emits them.
fn probes() -> Vec<MachInst> {
    vec![
        MachInst::new(O::Movz, vec![preg(0), Arg::Imm(0x1234)]),
        MachInst::new(O::Movk, vec![preg(8), Arg::Imm(0xbeef), Arg::Imm(16)]),
        MachInst::new(O::Movn, vec![preg(37), Arg::Imm(7)]),
        MachInst::new(O::MOVXrr, vec![preg(1), preg(2)]),
        MachInst::new(O::MovR, vec![preg(29), Arg::Special(SpecialReg::SP)]),
        MachInst::new(O::SubRI, vec![preg(31), preg(31), Arg::Imm(48)]),
        MachInst::new(O::CmpRI, vec![preg(34), Arg::Imm(64)]),
        MachInst::new(O::CmpRR, vec![preg(3), preg(4)]),
        MachInst::new(
            O::AddRRShiftLsr,
            vec![preg(9), preg(10), preg(11), Arg::Imm(2)],
        ),
        MachInst::new(O::SubRRShift, vec![preg(6), preg(7), preg(8), Arg::Imm(3)]),
        MachInst::new(O::Umulh, vec![preg(3), preg(4), preg(5)]),
        MachInst::new(O::BCond, vec![Arg::Imm(13), Arg::Block(BlockId(1))]),
        MachInst::new(O::Bl, vec![Arg::Symbol("callee".into())]),
        MachInst::new(O::TailCall, vec![Arg::Symbol("callee".into())]),
        MachInst::new(
            O::LdrRI,
            vec![
                preg(1),
                Arg::MemOp {
                    base: PReg::new(31),
                    offset: 16,
                },
            ],
        ),
        MachInst::new(O::StrbRI, vec![preg(40), preg(9), Arg::Imm(3)]),
    ]
}

fn verdicts() -> Vec<(MachInst, InstructionWordVerdict)> {
    let config = VerificationConfig::default();
    probes()
        .into_iter()
        .map(|inst| {
            let verdict = instruction_word_verdict(&inst, &config)
                .unwrap_or_else(|| panic!("{inst:?} must be an admitted shape"));
            (inst, verdict)
        })
        .collect()
}

#[test]
fn every_probe_holds_in_process() {
    for (inst, verdict) in verdicts() {
        assert!(
            matches!(verdict.outcome, Outcome::Holds(_)),
            "{inst:?}: {:?}",
            verdict.outcome
        );
        assert!(!verdict.locations.is_empty(), "{inst:?}");
    }
}

/// `INSTRUCTION_WORD_SMT2_DIR=<dir>`: write each probe location's SMT-LIB2
/// query to `<dir>`, exactly the bytes `verify_with_ay` sends
/// (`ay_bridge::lane_smt2_query`: the raw formula wherever the local
/// simplifier alone would fold it to `false`), so the solver and checker a
/// build does not admit can be run on them by hand. `manifest.tsv` lists each
/// file with its obligation name and whether its two terms are syntactically
/// identical. Writes nothing otherwise.
#[test]
fn dump_probe_queries() {
    let Some(dir) = std::env::var_os("INSTRUCTION_WORD_SMT2_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).expect("create the query directory");
    let config = AYConfig::default();
    let mut manifest = String::from("file\tobligation\tdegenerate\n");
    for (index, (inst, verdict)) in verdicts().into_iter().enumerate() {
        for (location, obligation) in &verdict.locations {
            let query = lane_smt2_query(obligation, &config);
            let name =
                format!("{index:02}-{:?}-{location:?}.smt2", inst.opcode).replace(['(', ')'], "");
            std::fs::write(dir.join(&name), query).expect("write a query");
            manifest.push_str(&format!(
                "{name}\t{}\t{}\n",
                obligation.name,
                obligation.is_degenerate()
            ));
        }
    }
    std::fs::write(dir.join("manifest.tsv"), manifest).expect("write the manifest");
}

/// The probe set's shape as the report states it: 16 instructions, 21
/// locations, 14 of them syntactically identical on both sides, and the 7 that
/// are not (the ones whose solver answer could say anything about the word).
#[test]
fn probe_locations_and_degenerate_split() {
    let mut locations = 0;
    let mut nontrivial = Vec::new();
    for (inst, verdict) in verdicts() {
        for (location, obligation) in &verdict.locations {
            locations += 1;
            if !obligation.is_degenerate() {
                nontrivial.push(format!("{:?} {location:?}", inst.opcode));
            }
        }
    }
    assert_eq!(locations, 21);
    assert_eq!(
        nontrivial,
        [
            "Movk Gpr(8)",
            "Movn Gpr(5)",
            "MOVXrr Gpr(1)",
            "MovR Gpr(29)",
            "CmpRI Nzcv",
            "CmpRR Nzcv",
            "BCond BranchTaken",
        ]
    );
}

#[test]
fn solver_lane_probe() {
    if std::env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref() != Ok("1") {
        eprintln!("solver_lane_probe: set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run");
        return;
    }
    let config = AYConfig::default();
    let mut tally = std::collections::BTreeMap::<&'static str, usize>::new();
    for (inst, verdict) in verdicts() {
        for (location, obligation) in &verdict.locations {
            let result = verify_with_ay(obligation, &config);
            let class = match &result {
                AYResult::Verified => "checked-proof",
                AYResult::SolverUnsat => "unsat-not-checked",
                AYResult::Timeout => "timeout",
                AYResult::Unknown(_) => "unknown",
                AYResult::CounterExample(_) => "counterexample",
                AYResult::Error(_) => "error",
            };
            *tally.entry(class).or_default() += 1;
            println!(
                "SOLVER_LANE_PROBE {:?} {location:?} inputs={} degenerate={} -> {result}",
                inst.opcode,
                obligation.inputs.len(),
                obligation.is_degenerate()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{inst:?} {location:?}: a counterexample to an obligation that holds in-process"
            );
        }
    }
    println!("SOLVER_LANE_PROBE_TALLY {tally:?}");
}
