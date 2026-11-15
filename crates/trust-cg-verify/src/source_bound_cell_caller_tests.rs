// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The scalar-cell caller owner over the 24 retained captures (six families,
//! O0-O3), prepared by today's real pipeline. Solver-free unless
//! `TCG_A64_CELL_QUALIFY=1`, which puts every theorem, perturbation and
//! mutation to the identity-admitted AY and Clean.

use super::*;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::regs::{PReg, X0, X1, X20, X29};

#[derive(Clone, serde::Deserialize)]
struct Capture {
    case: String,
    module: trust_ir::Module,
    lir: Function,
}

fn captures() -> Vec<Capture> {
    serde_json::from_str(include_str!("source_bound_cell_sources.json")).unwrap()
}

fn prepare(capture: &Capture) -> MachFunction {
    let opt_level = match capture.case.rsplit_once('-').unwrap().1 {
        "O0" => OptLevel::O0,
        "O1" => OptLevel::O1,
        "O2" => OptLevel::O2,
        "O3" => OptLevel::O3,
        other => panic!("unexpected optimization level: {other}"),
    };
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        verify: false,
        ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
    });
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &capture.lir,
            None,
            &capture.module,
            &capture.module.functions[0],
        )
        .unwrap()
        .0
}

/// Run `test` on a thread with the production verifier's stack budget or
/// more (a debug build's evaluator and serializer frames are large).
fn on_big_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(test)
        .unwrap()
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

/// The capture prepared as the rustc bridge's object compile prepares it on
/// Linux AArch64 (`Compiler::build_pipeline`): PIC, frames that cannot
/// unwind past the module's nounwind callees, and proof-grade publication.
fn prepare_as_bridge(capture: &Capture) -> MachFunction {
    let opt_level = match capture.case.rsplit_once('-').unwrap().1 {
        "O0" => OptLevel::O0,
        "O1" => OptLevel::O1,
        "O2" => OptLevel::O2,
        "O3" => OptLevel::O3,
        other => panic!("unexpected optimization level: {other}"),
    };
    let nounwind: std::collections::BTreeSet<String> = capture
        .module
        .functions
        .iter()
        .map(|function| function.name.clone())
        .collect();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        verify: false,
        relocation_model: trust_cg_lower::RelocationModel::Pic,
        ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
    })
    .with_eh_frames_cannot_unwind(Some(std::sync::Arc::new(nounwind)))
    .with_proof_grade_aarch64_publication_if(true);
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &capture.lir,
            None,
            &capture.module,
            &capture.module.functions[0],
        )
        .unwrap()
        .0
}

/// Every row of `machine` outside the laid-out chain that the ownership
/// rule does not excuse (diagnostics).
fn unowned_rows(machine: &MachFunction) -> Vec<String> {
    let Ok(chain) = super::super::linear::machine_chain(machine) else {
        return vec![format!(
            "no chain: block_order={:?} blocks={:?}",
            machine.block_order,
            machine
                .blocks
                .iter()
                .map(|b| (b.insts.clone(), b.preds.clone(), b.succs.clone()))
                .collect::<Vec<_>>()
        )];
    };
    machine
        .insts
        .iter()
        .enumerate()
        .filter(|(i, inst)| {
            !chain.live.contains(&InstId(*i as u32))
                && !(super::super::cell_frame::inert(inst, machine.next_vreg)
                    && inst.implicit_uses.is_empty())
                && !super::super::linear::inactive_branch_tombstone(inst, machine)
        })
        .map(|(i, inst)| format!("{i}: {inst:?}"))
        .collect()
}

/// The 24 captures prepared as the bridge prepares them are admitted and
/// credited like the test pipeline's: the qualification must not rest on a
/// preparation production never runs.
#[test]
fn bridge_preparation_is_admitted_at_every_level() {
    on_big_stack(|| {
        for c in captures() {
            let machine = prepare_as_bridge(&c);
            match source_bound_scalar_cell_caller(&c.module, &c.lir, &machine) {
                Ok(owner) => {
                    assert_eq!(
                        owner.covered().len(),
                        expected_credit(&c.case),
                        "{}",
                        c.case
                    );
                    println!(
                        "CELL_CALLER_BRIDGE_PREPARATION {} covered={} parts={} statement_sha256={}",
                        c.case,
                        owner.covered().len(),
                        owner.parts().len(),
                        query_sha(owner.obligation())
                    );
                }
                Err(refusal) => panic!(
                    "{}: {refusal}; unowned rows {:?}; block_order {:?}",
                    c.case,
                    unowned_rows(&machine),
                    machine.block_order
                ),
            }
        }
    });
}

fn query_sha(obligation: &ProofObligation) -> String {
    use sha2::{Digest, Sha256};
    let query = crate::ay_bridge::generate_smt2_query_raw(
        obligation,
        &crate::verdict_db::live_source_bound_config(),
    );
    format!("{:x}", Sha256::digest(query.as_bytes()))
}

fn opcodes(machine: &MachFunction, rows: &[InstId]) -> Vec<String> {
    rows.iter()
        .map(|id| format!("{:?}", machine.insts[id.0 as usize].opcode))
        .collect()
}

/// The credited set the disassembly predicts (design section 2, corrected by
/// the census: the O1-O3 write families keep one `NeonOrrV`).
fn expected_credit(case: &str) -> usize {
    // (O0, O1-O3): O0 adds the chain's fall-through B.
    let (o0, optimized) = if case.starts_with("aliased") && case.contains("_read-") {
        (8, 7)
    } else if case.starts_with("aliased") && case.contains("_write-") {
        (9, 7)
    } else if case.starts_with("local_cell_read_f32-") {
        (10, 9)
    } else if case.starts_with("local_cell_read-") {
        (11, 10)
    } else {
        panic!("unexpected case {case}")
    };
    if case.ends_with("O0") { o0 } else { optimized }
}

#[test]
fn all_24_captured_callers_build_one_theorem_with_the_expected_credit() {
    on_big_stack(all_24_captured_callers);
}

fn all_24_captured_callers() {
    let cases = captures();
    assert_eq!(cases.len(), 24);
    for c in cases {
        let machine = prepare(&c);
        let owner = source_bound_scalar_cell_caller(&c.module, &c.lir, &machine)
            .unwrap_or_else(|e| panic!("{}: {e}", c.case));
        let covered = owner.covered();
        let names = opcodes(&machine, &covered);
        println!(
            "CELL_CALLER {} covered={} [{}] inputs={} query_sha256={}",
            c.case,
            covered.len(),
            names.join(","),
            owner.obligation().inputs.len(),
            query_sha(owner.obligation())
        );
        assert_eq!(
            covered.len(),
            expected_credit(&c.case),
            "{}: {names:?}",
            c.case
        );
        for inst in machine.insts.iter().filter(|inst| inst.opcode == M::B) {
            println!("CELL_CALLER_B {} operands={:?}", c.case, inst.operands);
        }
        for id in &covered {
            let opcode = machine.insts[id.0 as usize].opcode;
            assert!(
                !matches!(
                    opcode,
                    M::Ret
                        | M::StpPreIndex
                        | M::StpRI
                        | M::LdpRI
                        | M::LdpPostIndex
                        | M::StrRI
                        | M::LdrRI
                ),
                "{}: {opcode:?} is credited",
                c.case
            );
        }
        assert!(!owner.obligation().is_degenerate());
    }
}

/// The theorem-level non-vacuity control, solver-free half: for every
/// captured function, the unperturbed theorem holds on every sample and the
/// theorem with any credited row's stated value changed (`x ^ 1`) is
/// falsified by a concrete sample; a candidate the owner did not credit is
/// one whose perturbation no sample falsifies.
#[test]
fn every_credited_row_is_load_bearing_in_the_theorem() {
    on_big_stack(every_credited_row_is_load_bearing);
}

fn every_credited_row_is_load_bearing() {
    let mut perturbed = 0;
    for c in captures() {
        let machine = prepare(&c);
        let owner = source_bound_scalar_cell_caller(&c.module, &c.lir, &machine).unwrap();
        assert!(!concretely_falsified(&c.module, &c.lir, &machine, None).unwrap());
        for (row, _) in candidate_rows(&c.module, &c.lir, &machine).unwrap() {
            let falsified = concretely_falsified(&c.module, &c.lir, &machine, Some(row)).unwrap();
            assert_eq!(falsified, owner.covers(row), "{} row {row:?}", c.case);
            let theorem = perturbed_obligation(&c.module, &c.lir, &machine, row).unwrap();
            assert_ne!(
                query_sha(&theorem),
                query_sha(owner.obligation()),
                "{} row {row:?}: the perturbation does not change the theorem",
                c.case
            );
            perturbed += usize::from(falsified);
        }
    }
    println!("CELL_CALLER_NON_VACUITY perturbed_and_falsified={perturbed}");
    // read 2 x (8 + 3 x 7), write 2 x (9 + 3 x 7), local f64 11 + 3 x 10,
    // local f32 10 + 3 x 9.
    assert_eq!(perturbed, 58 + 60 + 41 + 37);
}

/// Opt-in qualification with the admitted proof tools: every captured
/// theorem must certify (`AYResult::Verified`: AY's proof accepted by
/// Clean), within the live budget.
#[test]
fn qualification_with_the_admitted_proof_tools() {
    if std::env::var_os("TCG_A64_CELL_QUALIFY").is_none() {
        println!("SKIP A64_CELL_QUALIFY (set TCG_A64_CELL_QUALIFY=1 with admitted AY and Clean)");
        return;
    }
    on_big_stack(qualification);
}

fn qualification() {
    use crate::ay_bridge::{AYResult, verify_with_cli_raw};
    if let Some(reason) = crate::ay_bridge::proof_toolchain_unavailable_reason() {
        panic!("PROOF_TOOLS_MISSING: {reason}");
    }
    let config = crate::verdict_db::live_source_bound_config();
    let filter = std::env::var("TCG_A64_CELL_QUALIFY_CASE").ok();
    let mut verified = 0;
    let mut total = 0;
    for c in captures() {
        if filter.as_deref().is_some_and(|f| !c.case.contains(f)) {
            continue;
        }
        let machine = prepare(&c);
        let owner = source_bound_scalar_cell_caller(&c.module, &c.lir, &machine)
            .unwrap_or_else(|e| panic!("{}: {e}", c.case));
        owner.check_parts().unwrap();
        let statement = crate::ay_bridge::generate_smt2_query_raw(owner.obligation(), &config);
        if let Some(dir) = std::env::var_os("TCG_A64_CELL_DUMP") {
            let path = std::path::Path::new(&dir).join(format!("{}.smt2", c.case));
            std::fs::write(&path, &statement).unwrap();
            for (k, part) in owner.parts().iter().enumerate() {
                let query = crate::ay_bridge::generate_smt2_query_raw(part, &config);
                let path =
                    std::path::Path::new(&dir).join(format!("{}.part{}.smt2", c.case, k + 1));
                std::fs::write(&path, &query).unwrap();
            }
            println!("A64_CELL_DUMP {} parts={}", c.case, owner.parts().len());
            continue;
        }
        let start = std::time::Instant::now();
        let mut all = true;
        for (k, part) in owner.parts().iter().enumerate() {
            let query = crate::ay_bridge::generate_smt2_query_raw(part, &config);
            let part_start = std::time::Instant::now();
            let result = verify_with_cli_raw(part, &config);
            all &= matches!(result, AYResult::Verified);
            println!(
                "A64_CELL_QUALIFY {} part {}/{} result={result} seconds={:.2} query_bytes={} \
                 query_sha256={}",
                c.case,
                k + 1,
                owner.parts().len(),
                part_start.elapsed().as_secs_f64(),
                query.len(),
                query_sha(part)
            );
        }
        if all && (c.case.ends_with("O0") || c.case.ends_with("O2")) {
            corrupted_proofs_are_rejected(&c.case, owner.parts(), &config);
        }
        total += 1;
        verified += usize::from(all);
        println!(
            "A64_CELL_QUALIFY {} theorem_in_parts={} parts={} seconds={:.2} statement_bytes={} \
             statement_sha256={}",
            c.case,
            if all { "Verified" } else { "NOT-VERIFIED" },
            owner.parts().len(),
            start.elapsed().as_secs_f64(),
            statement.len(),
            query_sha(owner.obligation())
        );
        if std::env::var_os("TCG_A64_CELL_QUALIFY_REFUTE").is_none() {
            continue;
        }
        // The solver-backed halves of the non-vacuity and mutation controls:
        // the part holding the conjunct a concrete sample falsifies must be
        // refuted by AY (a counterexample), for every credited row's
        // perturbation and every mutant the constructor builds a theorem for.
        let refute = |label: String, part: Option<ProofObligation>| {
            let part = part.unwrap_or_else(|| panic!("{label}: no falsified conjunct"));
            let start = std::time::Instant::now();
            let result = verify_with_cli_raw(&part, &config);
            println!(
                "A64_CELL_REFUTE {label} part=\"{}\" result={} seconds={:.2}",
                part.name,
                if matches!(result, AYResult::CounterExample(_)) {
                    "CounterExample".to_owned()
                } else {
                    format!("{result}")
                },
                start.elapsed().as_secs_f64()
            );
            assert!(
                matches!(result, AYResult::CounterExample(_)),
                "{label}: AY did not refute: {result}"
            );
        };
        for row in owner.covered() {
            refute(
                format!(
                    "{} perturb {:?}",
                    c.case, machine.insts[row.0 as usize].opcode
                ),
                falsified_part(&c.module, &c.lir, &machine, Some(row)).unwrap(),
            );
        }
        for (label, mutant) in mutants(&c, &machine) {
            if diagnostic_scalar_cell_caller_obligation(&c.module, &c.lir, &mutant).is_err() {
                println!(
                    "A64_CELL_REFUTE {} mutant {label} refused by the constructor",
                    c.case
                );
                continue;
            }
            refute(
                format!("{} mutant {label}", c.case),
                falsified_part(&c.module, &c.lir, &mutant, None).unwrap(),
            );
        }
    }
    println!("A64_CELL_QUALIFY verified={verified}/{total}");
    if std::env::var_os("TCG_A64_CELL_DUMP").is_none() {
        assert_eq!(verified, total);
    }
}

/// The corrupted-proof control: the admitted AY's own Alethe proof of the
/// first two parts is accepted by the admitted Clean against its part's
/// exact query, and Clean rejects that proof with its final refutation step
/// removed, with a Boolean proof-local macro negated (where the proof has
/// one), and as a proof of the other part's query.
fn corrupted_proofs_are_rejected(
    case: &str,
    parts: &[ProofObligation],
    config: &crate::ay_bridge::AYConfig,
) {
    let checker = crate::obligation_cert_store::clean_checker_path().expect("an admitted Clean");
    let solver = crate::ay_identity::resolve_for_process().expect("an admitted AY");
    let dir = tempfile::tempdir().unwrap();
    let mut proved: Vec<(String, String)> = Vec::new();
    for (k, part) in parts.iter().take(2).enumerate() {
        let smt2 = crate::ay_bridge::generate_smt2_query_raw(part, config);
        let query = dir.path().join(format!("part{k}.smt2"));
        let proof = dir.path().join(format!("part{k}.alethe"));
        std::fs::write(&query, &smt2).unwrap();
        let output = solver
            .command()
            .unwrap()
            .arg("-smt2")
            .arg(&query)
            .args(["--strict-proofs", "--proof"])
            .arg(&proof)
            .args(["--proof-format", "alethe"])
            .output()
            .unwrap();
        assert!(
            String::from_utf8_lossy(&output.stdout).starts_with("unsat"),
            "{case} part {k}: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        let proof = std::fs::read_to_string(&proof).unwrap();
        assert!(
            crate::obligation_cert_store::carcara_verify(&checker, &smt2, &proof),
            "{case} part {k}: Clean rejects AY's own proof"
        );
        proved.push((smt2, proof));
    }
    for (k, (smt2, proof)) in proved.iter().enumerate() {
        let mut lines: Vec<&str> = proof.lines().collect();
        lines.pop();
        let truncated = lines.join("\n");
        assert!(
            !crate::obligation_cert_store::carcara_verify(&checker, smt2, &truncated),
            "{case} part {k}: a proof without its final step is accepted"
        );
        let negated = proof
            .lines()
            .find(|line| line.starts_with("(define-fun ") && line.contains(" () Bool "))
            .map(|line| {
                let (header, definition) = line.split_once(" () Bool ").unwrap();
                let definition = definition.strip_suffix(')').unwrap();
                proof.replacen(line, &format!("{header} () Bool (not {definition}))"), 1)
            });
        if let Some(negated) = &negated {
            assert!(
                !crate::obligation_cert_store::carcara_verify(&checker, smt2, negated),
                "{case} part {k}: a proof with a negated Boolean macro is accepted"
            );
        }
        let (_, other) = &proved[1 - k];
        assert!(
            !crate::obligation_cert_store::carcara_verify(&checker, smt2, other),
            "{case} part {k}: the other part's proof is accepted"
        );
        println!(
            "A64_CELL_CORRUPTED_PROOF {case} part {} truncated=rejected negated_macro={} \
             foreign=rejected",
            k + 1,
            if negated.is_some() {
                "rejected"
            } else {
                "absent"
            }
        );
    }
}

/// The first row of `machine.insts` satisfying `pred`.
fn find(machine: &MachFunction, pred: impl Fn(&MachInst) -> bool) -> Option<usize> {
    machine.insts.iter().position(pred)
}

fn names_sp(operand: &O) -> bool {
    matches!(operand, O::Special(SpecialReg::SP))
        || matches!(operand, O::PReg(reg) if reg.encoding() == 31)
}

/// Replace the immediate operand of row `index`.
fn set_imm(machine: &mut MachFunction, index: usize, operand: usize, value: i64) {
    machine.insts[index].operands[operand] = O::Imm(value);
}

/// The design's mutation table (sections 2 and 7) applied to a captured
/// machine function PAST the Rust admission filter: frame, cell-address,
/// argument-copy, constant, call and branch rows.
fn mutants(c: &Capture, machine: &MachFunction) -> Vec<(&'static str, MachFunction)> {
    let wide = !c.case.contains("f32");
    let mut out: Vec<(&'static str, MachFunction)> = Vec::new();
    let mut with = |label: &'static str, change: &dyn Fn(&mut MachFunction) -> bool| {
        let mut mutant = machine.clone();
        if change(&mut mutant) {
            out.push((label, mutant));
        }
    };
    let fp = |m: &MachFunction| {
        find(m, |i| {
            i.opcode == M::AddRI && i.operands[0] == O::PReg(X29) && names_sp(&i.operands[1])
        })
    };
    let sub_sp = |m: &MachFunction| find(m, |i| i.opcode == M::SubRI && names_sp(&i.operands[0]));
    let add_sp = |m: &MachFunction| find(m, |i| i.opcode == M::AddRI && names_sp(&i.operands[0]));
    let cell =
        |m: &MachFunction| find(m, |i| i.opcode == M::SubRI && i.operands[1] == O::PReg(X29));
    let copy =
        |m: &MachFunction| find(m, |i| i.opcode == M::MOVXrr && i.operands[0] == O::PReg(X0));
    let call = |m: &MachFunction| find(m, |i| i.opcode == M::Bl);
    with("fp-establish #16->#24", &|m| {
        fp(m).map(|i| set_imm(m, i, 2, 24)).is_some()
    });
    with("sp-adjust #16->#8", &|m| {
        sub_sp(m).map(|i| set_imm(m, i, 2, 8)).is_some()
    });
    with("sp-restore #16->#32", &|m| {
        add_sp(m).map(|i| set_imm(m, i, 2, 32)).is_some()
    });
    with("cell-address overlaps the x20/x19 slot", &|m| {
        cell(m).map(|i| set_imm(m, i, 2, 12)).is_some()
    });
    with("cell-address misaligned", &|m| {
        cell(m)
            .map(|i| set_imm(m, i, 2, if wide { 28 } else { 22 }))
            .is_some()
    });
    with("argument copy reads x20", &|m| {
        copy(m)
            .map(|i| m.insts[i].operands[1] = O::PReg(X20))
            .is_some()
    });
    with("argument copy writes x1", &|m| {
        copy(m)
            .map(|i| m.insts[i].operands[0] = O::PReg(X1))
            .is_some()
    });
    with("fp argument copy reads v2", &|m| {
        let Some(call) = call(m) else { return false };
        let Some(orr) = (0..call).rev().find(|i| m.insts[*i].opcode == M::NeonOrrV) else {
            return false;
        };
        let v2 = O::PReg(PReg::new(if wide { 98 } else { 130 }));
        m.insts[orr].operands[1] = v2.clone();
        m.insts[orr].operands[2] = v2;
        true
    });
    with("movz immediate", &|m| {
        find(m, |i| i.opcode == M::Movz)
            .map(|i| set_imm(m, i, 1, 1))
            .is_some()
    });
    with("movk halfword", &|m| {
        find(m, |i| i.opcode == M::Movk)
            .map(|i| {
                let shift = match m.insts[i].operands.get(2) {
                    Some(O::Imm(shift)) => *shift,
                    _ => 0,
                };
                set_imm(m, i, 2, if shift == 0 { 16 } else { shift - 16 })
            })
            .is_some()
    });
    with("fmov source", &|m| {
        find(m, |i| i.opcode == M::FmovGprFpr)
            .map(|i| m.insts[i].operands[1] = O::PReg(PReg::new(if wide { 1 } else { 33 })))
            .is_some()
    });
    with("callee symbol", &|m| {
        call(m)
            .map(|i| m.insts[i].operands[0] = O::Symbol("other_callback".into()))
            .is_some()
    });
    // The call moved before the copy of the cell address into X0 (moving it
    // past a redundant second V0 copy, as in the O0 write families, would
    // leave an equivalent program).
    with("call before its argument copy", &|m| {
        let (Some(call), Some(copy)) = (call(m), copy(m)) else {
            return false;
        };
        let (call, copy) = (InstId(call as u32), InstId(copy as u32));
        let block = m
            .blocks
            .iter_mut()
            .find(|b| b.insts.contains(&call))
            .unwrap();
        let (Some(at), Some(before)) = (
            block.insts.iter().position(|i| *i == call),
            block.insts.iter().position(|i| *i == copy),
        ) else {
            return false;
        };
        if before > at {
            return false;
        }
        block.insts.remove(at);
        block.insts.insert(before, call);
        true
    });
    with("call implicit use x1", &|m| {
        call(m)
            .map(|i| {
                m.insts[i].implicit_uses = if wide {
                    &[X1, trust_cg_ir::regs::D0]
                } else {
                    &[X1, trust_cg_ir::regs::S0]
                }
            })
            .is_some()
    });
    with("dropped ldp x20, x19", &|m| {
        find(m, |i| i.opcode == M::LdpPostIndex)
            .map(|i| m.insts[i] = MachInst::new(M::Nop, Vec::new()))
            .is_some()
    });
    with("stp x20, x19, [sp, #-16]!", &|m| {
        find(m, |i| i.opcode == M::StpPreIndex)
            .map(|i| set_imm(m, i, 3, -16))
            .is_some()
    });
    // A chain B only: a B tombstone outside the layout executes nothing.
    with("B retargeted", &|m| {
        let laid_out = |index: usize| {
            m.block_order
                .iter()
                .any(|b| m.blocks[b.0 as usize].insts.contains(&InstId(index as u32)))
        };
        (0..m.insts.len())
            .find(|i| m.insts[*i].opcode == M::B && laid_out(*i))
            .map(|i| {
                m.insts[i].operands[0] = match m.insts[i].operands[0] {
                    O::Imm(displacement) => O::Imm(displacement + 1),
                    _ => O::Block(m.entry),
                }
            })
            .is_some()
    });
    out
}

/// End to end: the production owner builds no owner (so credits no row)
/// for any diagnosis mutation, nor for a Darwin triple.
#[test]
fn production_owner_refuses_the_diagnosis_mutations() {
    on_big_stack(|| {
        let mut refused = 0;
        for c in captures() {
            let machine = prepare(&c);
            for (label, mutant) in mutants(&c, &machine) {
                let refusal = source_bound_scalar_cell_caller(&c.module, &c.lir, &mutant)
                    .err()
                    .unwrap_or_else(|| panic!("{} {label}: the owner was built", c.case));
                println!(
                    "CELL_CALLER_PRODUCTION_REFUSAL {} {label}: {refusal}",
                    c.case
                );
                refused += 1;
            }
            let mut darwin = c.module.clone();
            darwin.target_info.as_mut().unwrap().triple = "aarch64-apple-darwin".into();
            assert!(matches!(
                source_bound_scalar_cell_caller(&darwin, &c.lir, &machine),
                Err(ScalarCellCallerRefusal::Source(_))
            ));
            refused += 1;
        }
        println!("CELL_CALLER_PRODUCTION_REFUSALS refused={refused}");
    });
}

/// The laid-out chain `B` of `machine` (its arena index), if any.
fn laid_out_branch(machine: &MachFunction) -> Option<usize> {
    machine
        .block_order
        .iter()
        .filter_map(|block| machine.blocks[block.0 as usize].insts.last())
        .map(|id| id.0 as usize)
        .find(|index| machine.insts[*index].opcode == M::B)
}

/// Ruling LD-90: a `B` is bound by its
/// operand in the theorem. Past the admission filter (whose chain walk
/// follows the branch and refuses these first in production), every O0
/// capture with its `B` displacement or `Block` target changed to land
/// anywhere but the next laid-out row still gets a theorem, and a concrete
/// sample falsifies it at a closed conjunct (CB), because the landing word
/// comes from the layout and never from the operand. A CB whose right-hand
/// side were `word + d` would hold for every `d` and fail this test.
#[test]
fn a_chain_branch_is_bound_by_its_operand_in_the_theorem() {
    on_big_stack(|| {
        let (mut mutants, mut falsified) = (0, 0);
        for c in captures().into_iter().filter(|c| c.case.ends_with("O0")) {
            for machine in [prepare(&c), prepare_as_bridge(&c)] {
                let b = laid_out_branch(&machine)
                    .unwrap_or_else(|| panic!("{}: no laid-out B", c.case));
                let position = machine
                    .block_order
                    .iter()
                    .position(|block| {
                        machine.blocks[block.0 as usize]
                            .insts
                            .contains(&InstId(b as u32))
                    })
                    .unwrap();
                let word: i64 = machine.block_order[..position]
                    .iter()
                    .flat_map(|block| &machine.blocks[block.0 as usize].insts)
                    .chain(&machine.blocks[machine.block_order[position].0 as usize].insts)
                    .take_while(|id| id.0 as usize != b)
                    .map(|id| i64::from(!machine.insts[id.0 as usize].is_pseudo()))
                    .sum();
                // The unmutated theorem holds on every sample.
                assert!(!concretely_falsified(&c.module, &c.lir, &machine, None).unwrap());
                let own = match machine.insts[b].operands.as_slice() {
                    [O::Imm(displacement)] => *displacement,
                    other => panic!("{}: B operands {other:?}", c.case),
                };
                let displacements: BTreeSet<i64> =
                    [own + 1, own + 7, own - 2, 0, -word, 1 << 20, -(1 << 20)]
                        .into_iter()
                        .filter(|d| *d != own)
                        .collect();
                let mut operands: Vec<O> = displacements.into_iter().map(O::Imm).collect();
                // Every laid-out block up to the B's own as a `Block` target
                // (the entry; the B's own block is a self loop).
                operands.extend(
                    machine.block_order[..=position]
                        .iter()
                        .map(|block| O::Block(*block)),
                );
                mutants += operands.len();
                for operand in operands {
                    let mut mutant = machine.clone();
                    mutant.insts[b].operands = vec![operand.clone()];
                    let label = format!("{} B {operand:?} (own Imm({own}))", c.case);
                    diagnostic_scalar_cell_caller_obligation(&c.module, &c.lir, &mutant)
                        .unwrap_or_else(|e| panic!("{label}: no theorem: {e}"));
                    assert!(
                        concretely_falsified(&c.module, &c.lir, &mutant, None).unwrap(),
                        "{label}: the theorem holds"
                    );
                    let part = falsified_part(&c.module, &c.lir, &mutant, None)
                        .unwrap()
                        .unwrap_or_else(|| panic!("{label}: no falsified part"));
                    let empty: HashMap<String, u64> = HashMap::new();
                    assert!(
                        conjuncts_of(&part.aarch64_expr).iter().any(|conjunct| {
                            conjunct.free_vars().is_empty()
                                && matches!(
                                    conjunct.try_eval(&empty),
                                    Ok(crate::smt::EvalResult::Bool(false))
                                )
                        }),
                        "{label}: the falsified part has no false closed (CB) conjunct"
                    );
                    assert!(
                        source_bound_scalar_cell_caller(&c.module, &c.lir, &mutant).is_err(),
                        "{label}: the production owner was built"
                    );
                    falsified += 1;
                }
            }
        }
        println!("CELL_CALLER_B_OPERAND mutants={mutants} falsified={falsified}");
        // Six O0 captures, two preparations, at least seven displacements
        // and one `Block` target each.
        assert_eq!(falsified, mutants);
        assert!(mutants >= 6 * 2 * 8, "{mutants}");
    });
}

/// The CB conjunct of one `B` as the walk states it holds exactly when the
/// row's displacement lands on the layout's continuation word, for
/// displacements 1, 8, -9, 2^20, 0, -1 and 2 against three layouts.
#[test]
fn the_transfer_conjunct_depends_on_the_displacement() {
    on_big_stack(|| {
        let c = captures()
            .into_iter()
            .find(|c| c.case == "aliased_f32_read-O0")
            .unwrap();
        let machine = prepare(&c);
        let b = InstId(laid_out_branch(&machine).unwrap() as u32);
        let empty: HashMap<String, u64> = HashMap::new();
        for (word, next) in [(9, 10), (0, 1), (40, 41)] {
            for displacement in [1, 8, -9, 1 << 20, 0, -1, 2] {
                let mut walk = Walk {
                    machine: &machine,
                    width: 32,
                    perturb: None,
                    inputs: Vec::new(),
                    x: vec![Slot::Entry; 31],
                    v: vec![[Slot::Entry, Slot::Entry]; 32],
                    sp: E::var("entry_sp", 64),
                    memory: StoreChain {
                        initial: E::const_array(crate::smt::SmtSort::BitVec(64), E::bv_const(0, 8)),
                        stores: Vec::new(),
                    },
                    calls: Vec::new(),
                    accesses: Vec::new(),
                    sp_values: Vec::new(),
                    written_x: BTreeSet::new(),
                    written_v_lo: BTreeSet::new(),
                    transfers: Vec::new(),
                    candidates: Vec::new(),
                    returned: None,
                };
                walk.step(
                    b,
                    &Contract {
                        width: 4,
                        parameters: 0,
                        calls: Vec::new(),
                        cell_after: Vec::new(),
                        result: Vec::new(),
                    },
                    Some(Transfer {
                        word,
                        displacement,
                        next,
                    }),
                )
                .unwrap();
                let [conjunct] = walk.transfers.as_slice() else {
                    panic!("one CB conjunct")
                };
                let holds = matches!(
                    conjunct.try_eval(&empty),
                    Ok(crate::smt::EvalResult::Bool(true))
                );
                assert_eq!(
                    holds,
                    word + displacement == next,
                    "word {word} displacement {displacement} next {next}: {conjunct}"
                );
            }
        }
    });
}

/// The mutation control, solver-free half: past the Rust admission filter,
/// every mutant's theorem is either refused by the constructor or falsified
/// by a concrete sample. Never does a mutant's theorem hold on every sample.
#[test]
fn operand_mutations_past_the_admission_filter_are_falsified_or_refused() {
    on_big_stack(|| {
        let (mut falsified, mut refused) = (0, 0);
        for c in captures() {
            let machine = prepare(&c);
            for (label, mutant) in mutants(&c, &machine) {
                match diagnostic_scalar_cell_caller_obligation(&c.module, &c.lir, &mutant) {
                    Err(refusal) => {
                        println!("CELL_CALLER_MUTANT {} {label}: refused ({refusal})", c.case);
                        refused += 1;
                    }
                    Ok(_) => {
                        assert!(
                            concretely_falsified(&c.module, &c.lir, &mutant, None).unwrap(),
                            "{} {label}: a mutant's theorem holds on every sample",
                            c.case
                        );
                        println!("CELL_CALLER_MUTANT {} {label}: falsified", c.case);
                        falsified += 1;
                    }
                }
            }
        }
        println!("CELL_CALLER_MUTANTS falsified={falsified} refused={refused}");
        assert!(falsified > 0 && refused > 0);
    });
}

/// A covered row's verdict is the theorem's replay and nothing else: only a
/// Valid replay is Formal credit (under the row's role category, never
/// degenerate); a refutation or an unknown fails the row; no independently
/// checked proof (AY absent or withdrawn, a corrupted proof Clean rejects,
/// `TCG_REFINE_SOLVER=0`) leaves it unverified with the owner's reason,
/// which the emitted-opcode inventory counts as blocking.
#[test]
fn a_covered_row_is_credited_only_by_a_valid_replay() {
    use crate::function_verifier::{
        FunctionVerificationReport, InstructionOpcode, InstructionReport,
        InstructionVerificationResult as R,
    };
    use crate::verify::VerificationResult as V;
    on_big_stack(|| {
        let c = captures().into_iter().next().unwrap();
        let machine = prepare(&c);
        let owner = source_bound_scalar_cell_caller(&c.module, &c.lir, &machine).unwrap();
        for id in owner.covered() {
            let role = owner.role(id).unwrap();
            let opcode = InstructionOpcode::AArch64(machine.insts[id.0 as usize].opcode);
            match scalar_cell_row_result(owner.obligation(), role, Some(&V::Valid), None) {
                R::Verified {
                    category,
                    strength: crate::verify::VerificationStrength::Formal,
                    degenerate: false,
                    proof_name,
                } => {
                    assert_eq!(category, role.category());
                    assert_eq!(proof_name, SCALAR_CELL_CALLER_OBLIGATION_NAME);
                }
                other => panic!("{other:?}"),
            }
            for (verdict, why) in [
                (None, None),
                (None, Some("AY TIMEOUT")),
                (
                    Some(V::Invalid {
                        counterexample: "x".into(),
                    }),
                    None,
                ),
                (Some(V::Unknown { reason: "y".into() }), None),
            ] {
                let row = scalar_cell_row_result(owner.obligation(), role, verdict.as_ref(), why);
                if let R::Unverified { reason } = &row {
                    assert!(
                        reason.starts_with(SCALAR_CELL_CALLER_NEEDS_REPLAY),
                        "{reason}"
                    );
                } else {
                    assert!(matches!(row, R::Failed { .. }), "{row:?}");
                }
                let report = FunctionVerificationReport {
                    function_name: c.lir.name.clone(),
                    precondition_failure: None,
                    instructions: vec![InstructionReport {
                        inst_index: id.0 as usize,
                        opcode,
                        result: row.clone(),
                    }],
                };
                assert!(
                    !report.emitted_opcode_inventory().is_promotable(),
                    "{row:?} promotes"
                );
            }
        }
    });
}

/// Ruling LD-92: an arena row no block
/// lists (left by a pass that removed it from its block, here a load with a
/// virtual destination, as measured in the bridge's O2 output, and a store)
/// is never emitted, so the owner states the same theorem with or without
/// it; the same row listed in the laid-out block is judged and refused.
#[test]
fn an_orphan_arena_row_is_retired_and_a_listed_one_is_judged() {
    on_big_stack(|| {
        let mut checked = 0;
        for c in captures() {
            let machine = prepare(&c);
            let owner = source_bound_scalar_cell_caller(&c.module, &c.lir, &machine).unwrap();
            let statement = query_sha(owner.obligation());
            let covered = owner.covered();
            let store = find(&machine, |i| i.opcode == M::StrRI).unwrap();
            let load = MachInst::new(
                M::LdrRI,
                vec![
                    O::VReg(trust_cg_ir::VReg::new(
                        machine.next_vreg,
                        trust_cg_ir::regs::RegClass::Fpr32,
                    )),
                    O::PReg(trust_cg_ir::regs::X19),
                    O::Imm(0),
                ],
            );
            for orphan in [machine.insts[store].clone(), load] {
                let mut with_orphan = machine.clone();
                with_orphan.insts.push(orphan.clone());
                let owner =
                    source_bound_scalar_cell_caller(&c.module, &c.lir, &with_orphan).unwrap();
                assert_eq!(query_sha(owner.obligation()), statement, "{}", c.case);
                assert_eq!(owner.covered(), covered, "{}", c.case);
                let mut listed = with_orphan.clone();
                let id = InstId((listed.insts.len() - 1) as u32);
                let block = listed.block_order[0];
                listed.blocks[block.0 as usize].insts.insert(1, id);
                assert!(
                    source_bound_scalar_cell_caller(&c.module, &c.lir, &listed).is_err(),
                    "{}: a listed extra row was admitted",
                    c.case
                );
                checked += 1;
            }
        }
        println!("CELL_CALLER_ORPHAN_ROWS checked={checked}");
        assert_eq!(checked, 48);
    });
}

/// The window the theorem lets a frame use is the frame lowering's probing
/// bound: the two cannot drift apart.
#[test]
fn stack_window_matches_frame_lowering() {
    assert_eq!(
        STACK_WINDOW_BYTES,
        u64::from(trust_cg_codegen::frame::STACK_PROBE_MAX_UNPROBED)
    );
}

/// The translator's reading of the two SIMD&FP rows no other source-bound
/// owner admits is the emitted word's: for every `NeonOrrV` and `FmovGprFpr`
/// of the 24 captures, the encoder's word passes ENC-5, and its Arm ARM
/// fields (ORR (vector, register) with Q = 1; FMOV (general) with sf/type of
/// the row's width) name exactly the registers the translator reads.
#[test]
fn neon_orr_and_fmov_readings_are_the_emitted_words() {
    use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
    on_big_stack(|| {
        let (mut orr, mut fmov) = (0, 0);
        for c in captures() {
            let machine = prepare(&c);
            for inst in &machine.insts {
                if !matches!(inst.opcode, M::NeonOrrV | M::FmovGprFpr) {
                    continue;
                }
                let word = encode_instruction(inst).unwrap();
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None),
                        DecodeCheckOutcome::Match
                    ),
                    "{}: ENC-5 does not match {inst:?}",
                    c.case
                );
                let field = |shift: u32| ((word >> shift) & 31) as u8;
                if inst.opcode == M::NeonOrrV {
                    let [d, n, m] = neon_orr_reading(inst).unwrap();
                    // 0 Q 0 01110 101 Rm 000111 Rn Rd, Q = 1.
                    assert_eq!(word & 0xffe0_fc00, 0x4ea0_1c00, "{}: {word:#x}", c.case);
                    assert_eq!([field(0), field(5), field(16)], [d, n, m]);
                    orr += 1;
                } else {
                    let (d, n, bytes) = fmov_general_reading(inst).unwrap();
                    // sf 0 0 11110 type 1 00 111 000000 Rn Rd.
                    let fixed = if bytes == 8 { 0x9e67_0000 } else { 0x1e27_0000 };
                    assert_eq!(word & 0xffff_fc00, fixed, "{}: {word:#x}", c.case);
                    assert_eq!([field(0), field(5)], [d, n]);
                    fmov += 1;
                }
            }
        }
        println!("CELL_CALLER_WORDS neon_orr={orr} fmov_general={fmov}");
        assert!(orr > 0 && fmov > 0);
    });
}

/// The cell contract's float constants are trust-ir's: for every literal
/// the source check admits, the bits it binds are the pinned interpreter's
/// `fconst` bits (zeros, subnormals, normals, extremes), and a literal it
/// cannot state exactly (non-finite, or inexact at F32) is refused.
#[test]
fn cell_float_constants_are_trust_irs() {
    use trust_ir::Ty;
    use trust_ir::interpret::{InterpretValueKind, Interpreter};
    use trust_ir_build::ModuleBuilder;
    let values = [
        0.0,
        -0.0,
        -21.5,
        1.5,
        f32::from_bits(1) as f64,
        f32::MIN_POSITIVE as f64,
        f32::MAX as f64,
        -(f32::MAX as f64),
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        f64::MAX,
        -f64::MAX,
        0.1,
        f64::INFINITY,
        f64::NAN,
    ];
    let mut builder = ModuleBuilder::new("cell_float_constants");
    for (k, value) in values.iter().enumerate() {
        for (ty, tag) in [(Ty::F32, "f32"), (Ty::F64, "f64")] {
            let signature = builder.add_func_type(vec![], vec![ty.clone()]);
            let mut f = builder.function(format!("const_{tag}_{k}"), signature);
            let entry = f.create_block();
            f.switch_to_block(entry);
            let constant = f.fconst(ty, *value);
            f.ret(vec![constant]);
            f.build();
        }
    }
    let reference = builder.build().expect("constant fixture");
    let interpreter = Interpreter::with_module(&reference);
    let (mut agreed, mut refused) = (0, 0);
    for c in captures()
        .into_iter()
        .filter(|c| c.case.starts_with("local_cell") && c.case.ends_with("O0"))
    {
        let tag = if c.case.contains("f32") { "f32" } else { "f64" };
        for (k, value) in values.iter().enumerate() {
            let mut c = c.clone();
            for node in c.module.functions[0]
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.body)
            {
                if let trust_ir::Inst::Const { value: literal, .. } = &mut node.inst {
                    *literal = trust_ir::Constant::Float(*value);
                }
            }
            for instruction in c.lir.blocks.values_mut().flat_map(|b| &mut b.instructions) {
                if let trust_cg_lower::instructions::Opcode::Fconst { imm, .. } =
                    &mut instruction.opcode
                {
                    *imm = *value;
                }
            }
            let checked = match super::super::check_aarch64_scalar_cell_source(&c.module, &c.lir) {
                Ok(checked) => checked,
                Err(_) => {
                    let narrowed = *value as f32;
                    assert!(
                        !value.is_finite() || (tag == "f32" && f64::from(narrowed) != *value),
                        "{} {value:e}: an exact finite literal was refused",
                        c.case
                    );
                    refused += 1;
                    continue;
                }
            };
            let bits: u64 = checked.contract().calls[0]
                .cell_before
                .iter()
                .enumerate()
                .map(|(b, byte)| match byte {
                    Byte::Constant(v) => u64::from(*v) << (8 * b),
                    other => panic!("{}: a non-constant byte {other:?}", c.case),
                })
                .sum();
            let function = reference
                .function_by_name(&format!("const_{tag}_{k}"))
                .unwrap();
            let outcome = interpreter.execute_function(function, Vec::new()).unwrap();
            let [returned] = &outcome.returns[..] else {
                panic!("one result")
            };
            let InterpretValueKind::FloatBits(expected) = returned.kind else {
                panic!("float bits")
            };
            assert_eq!(bits, expected, "{} {value:e}", c.case);
            agreed += 1;
        }
    }
    println!("CELL_CALLER_FLOAT_CONSTANTS agreed={agreed} refused={refused}");
    assert!(agreed > 0 && refused > 0);
}

/// The call model past one call (critique B4): the 2- and 16-call variants
/// of the aliased read captures, prepared by the real pipeline, give
/// theorems that hold on every sample and whose second `MOV X0` (C2) and
/// every call are load-bearing; the production owner refuses them as
/// outside the qualified domain.
#[test]
fn multi_call_fixtures_bind_but_stay_outside_the_qualified_domain() {
    on_big_stack(|| {
        use trust_cg_lower::instructions::{Opcode as L, Value};
        let mut checked = 0;
        for original in captures().into_iter().filter(|c| {
            c.case.starts_with("aliased_f")
                && c.case.contains("_read-")
                && (c.case.ends_with("O0") || c.case.ends_with("O3"))
        }) {
            for count in [2, 16] {
                let mut c = original.clone();
                for occurrence in 1..count {
                    let value = 42 + occurrence as u32;
                    let mut load = c.module.functions[0]
                        .blocks
                        .iter()
                        .flat_map(|b| &b.body)
                        .find(|n| matches!(n.inst, trust_ir::Inst::Load { .. }))
                        .unwrap()
                        .clone();
                    let mut call = c.module.functions[0].blocks[0]
                        .body
                        .iter()
                        .find(|n| matches!(n.inst, trust_ir::Inst::Call { .. }))
                        .unwrap()
                        .clone();
                    load.results = vec![trust_ir::ValueId::new(value)];
                    let trust_ir::Inst::Call { args, .. } = &mut call.inst else {
                        unreachable!()
                    };
                    args[1] = trust_ir::ValueId::new(value);
                    let body = &mut c.module.functions[0].blocks[0].body;
                    let at = body.len() - 1;
                    body.splice(at..at, [load, call]);
                    let mut load = c
                        .lir
                        .blocks
                        .values()
                        .flat_map(|b| &b.instructions)
                        .find(|i| matches!(i.opcode, L::Load { .. }))
                        .unwrap()
                        .clone();
                    let mut call = c.lir.blocks[&c.lir.entry_block]
                        .instructions
                        .iter()
                        .find(|i| matches!(i.opcode, L::Call { .. }))
                        .unwrap()
                        .clone();
                    load.results = vec![Value(value)];
                    call.args[1] = Value(value);
                    let body = &mut c
                        .lir
                        .blocks
                        .get_mut(&c.lir.entry_block)
                        .unwrap()
                        .instructions;
                    let at = body.len() - 1;
                    body.splice(at..at, [load, call]);
                }
                let machine = prepare(&c);
                assert!(matches!(
                    source_bound_scalar_cell_caller(&c.module, &c.lir, &machine),
                    Err(ScalarCellCallerRefusal::Domain(_))
                ));
                diagnostic_scalar_cell_caller_obligation(&c.module, &c.lir, &machine).unwrap();
                assert!(!concretely_falsified(&c.module, &c.lir, &machine, None).unwrap());
                let rows = candidate_rows(&c.module, &c.lir, &machine).unwrap();
                let calls: Vec<_> = rows
                    .iter()
                    .filter(|(_, role)| *role == CellRowRole::Call)
                    .collect();
                assert_eq!(calls.len(), count);
                for (row, _) in &calls {
                    assert!(
                        concretely_falsified(&c.module, &c.lir, &machine, Some(*row)).unwrap(),
                        "{}-calls{count}: call {row:?} is not load-bearing",
                        c.case
                    );
                }
                // The X0 copy before the second call carries C2.
                let second = machine
                    .insts
                    .iter()
                    .enumerate()
                    .filter(|(_, i)| i.opcode == M::Bl)
                    .nth(1)
                    .unwrap()
                    .0;
                let copy = (0..second)
                    .rev()
                    .find(|i| {
                        machine.insts[*i].opcode == M::MOVXrr
                            && machine.insts[*i].operands[0] == O::PReg(X0)
                    })
                    .unwrap();
                assert!(
                    concretely_falsified(&c.module, &c.lir, &machine, Some(InstId(copy as u32)))
                        .unwrap(),
                    "{}-calls{count}: the second X0 copy is not load-bearing",
                    c.case
                );
                checked += 1;
            }
        }
        println!("CELL_CALLER_MULTI_CALL checked={checked}");
        assert_eq!(checked, 8);
    });
}

/// The architectural state the Arm ARM reference executes on: X0-X30, SP and
/// V0-V31 as (bits 63:0, bits 127:64).
#[derive(Clone, Debug, PartialEq, Eq)]
struct ArmState {
    x: [u64; 31],
    sp: u64,
    v: [(u64, u64); 32],
}

impl ArmState {
    /// A random state: every register its own value, or (`distinct ==
    /// false`) one value per bank, which cannot tell registers apart.
    fn sample(next: &mut impl FnMut() -> u64, distinct: bool) -> Self {
        let (x_all, lo_all, hi_all) = (next(), next(), next());
        let mut x = [0; 31];
        for value in &mut x {
            *value = if distinct { next() } else { x_all };
        }
        let mut v = [(0, 0); 32];
        for value in &mut v {
            *value = if distinct {
                (next(), next())
            } else {
                (lo_all, hi_all)
            };
        }
        Self {
            x,
            sp: next() & !15,
            v,
        }
    }
}

/// One A64 instruction word executed per the Arm ARM pseudocode (DDI 0487,
/// C6.2 ADD/SUB (immediate), ORR (shifted register), MOVN/MOVZ/MOVK, C7.2
/// FMOV (general) and ORR (vector, register)), decoded from the word's own
/// fields and nothing else; `None` for a word outside those classes.
/// Register 31 is SP in ADD/SUB (immediate) and XZR elsewhere.
fn arm_arm_execute(word: u32, state: &ArmState) -> Option<ArmState> {
    let field = |shift: u32, bits: u32| (word >> shift) & ((1u32 << bits) - 1);
    let (rd, rn, rm) = (
        field(0, 5) as usize,
        field(5, 5) as usize,
        field(16, 5) as usize,
    );
    let xzr = |r: usize| if r == 31 { 0 } else { state.x[r] };
    let mut out = state.clone();
    let write_x = |out: &mut ArmState, r: usize, value: u64| {
        if r != 31 {
            out.x[r] = value;
        }
    };
    // ADD/SUB (immediate), 64-bit, no flags: sf=1 op S=0 100010 sh imm12 Rn Rd.
    if word & 0xbf80_0000 == 0x9100_0000 {
        let imm = u64::from(field(10, 12)) << (12 * field(22, 1));
        let operand = if rn == 31 { state.sp } else { state.x[rn] };
        let result = if field(30, 1) == 1 {
            operand.wrapping_sub(imm)
        } else {
            operand.wrapping_add(imm)
        };
        if rd == 31 {
            out.sp = result;
        } else {
            out.x[rd] = result;
        }
        return Some(out);
    }
    // ORR (shifted register), 64-bit, LSL: sf=1 opc=01 01010 shift=00 N=0
    // Rm imm6 Rn Rd (MOV Xd, Xm is Rn = 31).
    if word & 0xffe0_0000 == 0xaa00_0000 {
        let amount = field(10, 6);
        write_x(&mut out, rd, xzr(rn) | (xzr(rm) << amount));
        return Some(out);
    }
    // MOVN/MOVZ/MOVK: sf opc 100101 hw imm16 Rd.
    if word & 0x1f80_0000 == 0x1280_0000 {
        let (sf, opc, hw) = (field(31, 1), field(29, 2), field(21, 2));
        if (sf == 0 && hw > 1) || opc == 0b01 {
            return None;
        }
        let pos = 16 * hw;
        let imm = u64::from(field(5, 16)) << pos;
        let mask = if sf == 1 {
            u64::MAX
        } else {
            u64::from(u32::MAX)
        };
        let result = match opc {
            0b00 => !imm,
            0b10 => imm,
            _ => (xzr(rd) & !(0xffffu64 << pos)) | imm,
        } & mask;
        write_x(&mut out, rd, result);
        return Some(out);
    }
    // FMOV (general) to SIMD&FP: sf 0 0 11110 ftype 1 rmode=00 opcode=111
    // 000000 Rn Rd, with (sf, ftype) = (0, 00) for Sd <- Wn and (1, 01) for
    // Dd <- Xn; every bit of Vd above the integer's width is zeroed.
    if word & 0xffff_fc00 == 0x1e27_0000 || word & 0xffff_fc00 == 0x9e67_0000 {
        let mask = if field(31, 1) == 1 {
            u64::MAX
        } else {
            u64::from(u32::MAX)
        };
        out.v[rd] = (xzr(rn) & mask, 0);
        return Some(out);
    }
    // ORR (vector, register), Q = 1: 0 1 0 01110 10 1 Rm 000111 Rn Rd.
    if word & 0xffe0_fc00 == 0x4ea0_1c00 {
        out.v[rd] = (state.v[rn].0 | state.v[rm].0, state.v[rn].1 | state.v[rm].1);
        return Some(out);
    }
    None
}

/// The translator's reading of row `index` of `machine`, executed on
/// `state`: the register file after `Walk::step`, read back through the
/// theorem's own terms.
fn translate(
    machine: &MachFunction,
    index: usize,
    state: &ArmState,
) -> Result<ArmState, ScalarCellCallerRefusal> {
    let mut walk = Walk {
        machine,
        width: 32,
        perturb: None,
        inputs: Vec::new(),
        x: state
            .x
            .iter()
            .map(|value| Slot::Value(E::bv_const(*value, 64)))
            .collect(),
        v: state
            .v
            .iter()
            .map(|(lo, hi)| {
                [
                    Slot::Value(E::bv_const(*lo, 64)),
                    Slot::Value(E::bv_const(*hi, 64)),
                ]
            })
            .collect(),
        sp: E::bv_const(state.sp, 64),
        memory: StoreChain {
            initial: E::const_array(crate::smt::SmtSort::BitVec(64), E::bv_const(0, 8)),
            stores: Vec::new(),
        },
        calls: Vec::new(),
        accesses: Vec::new(),
        sp_values: Vec::new(),
        written_x: BTreeSet::new(),
        written_v_lo: BTreeSet::new(),
        transfers: Vec::new(),
        candidates: Vec::new(),
        returned: None,
    };
    walk.step(
        InstId(index as u32),
        &Contract {
            width: 4,
            parameters: 0,
            calls: Vec::new(),
            cell_after: Vec::new(),
            result: Vec::new(),
        },
        None,
    )?;
    let env: HashMap<String, u64> = HashMap::new();
    let value = |term: &E| match term.try_eval(&env).unwrap() {
        crate::smt::EvalResult::Bv(v) => v,
        other => panic!("{other:?}"),
    };
    let mut out = state.clone();
    for r in 0..31u8 {
        out.x[r as usize] = value(&walk.read_x(r));
    }
    for r in 0..32u8 {
        out.v[r as usize] = (value(&walk.read_v(r, 0)), value(&walk.read_v(r, 1)));
    }
    out.sp = value(&walk.sp);
    assert!(walk.inputs.is_empty(), "a concrete state created an input");
    Ok(out)
}

/// Every variant of `inst` with one register operand moved to the next
/// register of its own bank (X/W 0-30 cyclically, S/D 0-31, SP and XZR to
/// X0/X29), each a wrong register index the reference must expose.
fn register_mutants(inst: &MachInst) -> Vec<MachInst> {
    let moved = |operand: &O| -> Option<O> {
        let bank = |encoding: u16, base: u16, size: u16| {
            O::PReg(PReg::new(base + (encoding - base + 1) % size))
        };
        match operand {
            O::PReg(reg) => Some(match reg.encoding() {
                n @ 0..=30 => bank(n, 0, 31),
                31 => O::PReg(X29),
                n @ 32..=62 => bank(n, 32, 31),
                n @ 96..=127 => bank(n, 96, 32),
                n @ 128..=159 => bank(n, 128, 32),
                160 => O::PReg(X0),
                161 => O::PReg(PReg::new(32)),
                _ => return None,
            }),
            O::Special(SpecialReg::SP) => Some(O::PReg(X29)),
            O::Special(SpecialReg::XZR) => Some(O::PReg(X0)),
            O::Special(SpecialReg::WZR) => Some(O::PReg(PReg::new(32))),
            _ => None,
        }
    };
    (0..inst.operands.len())
        .filter_map(|k| {
            let operand = moved(&inst.operands[k])?;
            let mut mutant = inst.clone();
            mutant.operands[k] = operand;
            Some(mutant)
        })
        .collect()
}

/// The register model against an independent reference written from the
/// Arm ARM pseudocode. For every
/// general-purpose and SIMD&FP row of the 24 captures, the encoder's word
/// passes ENC-5, the reference decodes that word's own fields and executes
/// it on a state in which every register holds its own random value, and
/// the translator's whole register file after the row (every X, SP and both
/// halves of every V register, so a wrong destination shows too) equals the
/// reference's. Every wrong register index (each register operand moved to
/// another register of its bank) is exposed: the translator either refuses
/// the mutant or disagrees with the reference of the original word. The
/// control's own control: with one value per bank some of those wrong
/// indices go unseen, so the reference must give every register its own
/// value.
#[test]
fn row_terms_match_an_independent_arm_arm_reference() {
    use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
    on_big_stack(|| {
        let mut seed = 0x1234_5678_9abc_def1u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let (mut checked, mut mutants, mut exposed, mut unseen_flat) = (0, 0, 0, 0);
        let mut classes = BTreeSet::new();
        for c in captures() {
            let machine = prepare(&c);
            for (index, inst) in machine.insts.iter().enumerate() {
                if !matches!(
                    inst.opcode,
                    M::AddRI
                        | M::SubRI
                        | M::MOVXrr
                        | M::Movz
                        | M::Movn
                        | M::Movk
                        | M::FmovGprFpr
                        | M::NeonOrrV
                ) {
                    continue;
                }
                let word = encode_instruction(inst).unwrap();
                assert!(
                    matches!(
                        A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None),
                        DecodeCheckOutcome::Match
                    ),
                    "{}: ENC-5 does not match {inst:?}",
                    c.case
                );
                let state = ArmState::sample(&mut next, true);
                let expected = arm_arm_execute(word, &state)
                    .unwrap_or_else(|| panic!("{}: {word:#010x} outside the reference", c.case));
                let stated = translate(&machine, index, &state)
                    .unwrap_or_else(|e| panic!("{}: {inst:?}: {e}", c.case));
                assert_eq!(stated, expected, "{} {inst:?} {word:#010x}", c.case);
                classes.insert(format!("{:?}", inst.opcode));
                checked += 1;
                let flat = ArmState::sample(&mut next, false);
                let flat_expected = arm_arm_execute(word, &flat).unwrap();
                for mutant in register_mutants(inst) {
                    let mut wrong = machine.clone();
                    wrong.insts[index] = mutant.clone();
                    mutants += 1;
                    match translate(&wrong, index, &state) {
                        Err(_) => exposed += 1,
                        Ok(stated) => {
                            assert_ne!(
                                stated, expected,
                                "{}: the reference does not expose {mutant:?} (original {inst:?})",
                                c.case
                            );
                            exposed += 1;
                        }
                    }
                    if translate(&wrong, index, &flat).is_ok_and(|stated| stated == flat_expected) {
                        unseen_flat += 1;
                    }
                }
            }
        }
        println!(
            "CELL_CALLER_ROW_REFERENCE checked={checked} classes={classes:?} \
             register_mutants={mutants} exposed={exposed} unseen_with_one_value_per_bank={unseen_flat}"
        );
        assert!(checked > 100);
        assert_eq!(exposed, mutants);
        assert!(mutants > checked, "{mutants}");
        assert!(
            unseen_flat > 0,
            "the one-value-per-bank control sees every mutant"
        );
    });
}

/// Callee-contract item 3 (ruling LD-89)
/// lets the callee depend on processor state the caller never writes (NZCV,
/// FPCR, FPSR, TPIDR_EL0 and the other system registers), because that
/// state then holds its value from the caller's entry at the call, in both
/// executions.
/// This pins the precondition: every row the theorem interprets in the 24
/// captures (as the test pipeline and as the bridge prepare them) is an
/// inert NOP, one of the translator's register classes, `BL`, `B`, `RET` or a
/// memory row, none of which writes such state (Arm ARM); only `BL` has
/// implicit definitions, all caller-saved; and a row that writes NZCV
/// (`ADDS`, `CMP`) or FPSR (`FADD`), or reads TPIDR_EL0 (`MRS`), put into a
/// capture's first block, is refused by the translator. The IR has no `MSR`
/// opcode, so nothing the backend emits writes FPCR or TPIDR_EL0.
#[test]
fn no_interpreted_row_writes_processor_state_outside_the_model() {
    on_big_stack(|| {
        let mut rows = 0;
        let mut refused = 0;
        for c in captures() {
            for machine in [prepare(&c), prepare_as_bridge(&c)] {
                let view = emitted_view(&machine);
                let machine = view.as_ref().unwrap_or(&machine);
                for (id, _) in laid_out_rows(machine).unwrap() {
                    let inst = &machine.insts[id.0 as usize];
                    let register_class = matches!(
                        inst.opcode,
                        M::AddRI
                            | M::SubRI
                            | M::MOVXrr
                            | M::Movz
                            | M::Movn
                            | M::Movk
                            | M::FmovGprFpr
                            | M::NeonOrrV
                            | M::B
                            | M::Ret
                    );
                    assert!(
                        super::super::cell_frame::inert(inst, machine.next_vreg)
                            || register_class
                            || inst.opcode == M::Bl
                            || memory_access(inst).is_some(),
                        "{}: {inst:?} is outside the modelled classes",
                        c.case
                    );
                    if inst.opcode == M::Bl {
                        assert!(inst.implicit_defs.iter().copied().all(caller_saved));
                    } else {
                        assert!(inst.implicit_defs.is_empty(), "{}: {inst:?}", c.case);
                    }
                    rows += 1;
                }
                let x9 = O::PReg(PReg::new(9));
                let d8 = O::PReg(PReg::new(104));
                for writer in [
                    MachInst::new(M::AddsRI, vec![x9.clone(), x9.clone(), O::Imm(1)]),
                    MachInst::new(M::CmpRI, vec![x9.clone(), O::Imm(0)]),
                    MachInst::new(M::FaddRR, vec![d8.clone(), d8.clone(), d8]),
                    MachInst::new(M::Mrs, vec![x9, O::Imm(0xde82)]),
                ] {
                    let mut with_writer = machine.clone();
                    let id = InstId(with_writer.insts.len() as u32);
                    with_writer.insts.push(writer.clone());
                    let first = with_writer.block_order[0];
                    with_writer.blocks[first.0 as usize].insts.insert(1, id);
                    match diagnostic_scalar_cell_caller_obligation(&c.module, &c.lir, &with_writer)
                    {
                        Err(ScalarCellCallerRefusal::Row { inst, .. }) if inst == id => {
                            refused += 1;
                        }
                        other => panic!(
                            "{}: {:?} was not refused by the translator: {:?}",
                            c.case,
                            writer.opcode,
                            other.map(|_| "a theorem")
                        ),
                    }
                    assert!(
                        source_bound_scalar_cell_caller(&c.module, &c.lir, &with_writer).is_err()
                    );
                }
            }
        }
        println!("CELL_CALLER_PROCESSOR_STATE rows={rows} refused_writers={refused}");
        assert_eq!(refused, 24 * 2 * 4);
    });
}
