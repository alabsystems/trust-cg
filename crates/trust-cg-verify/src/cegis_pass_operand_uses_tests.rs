// trust-cg-verify/cegis_pass_operand_uses_tests.rs - CEGIS operand-role regressions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The CEGIS payload layers splice a constant materializer out of its block
//! when the rewritten consumer is its only reader. Search revision 2 counted
//! reads as "every operand after operand 0", so a compare, store or `Movk`
//! reading the constant at operand 0 left it looking single-use and the
//! rewrite deleted a live definition (wrong code). These rows pin the fix:
//! reads and definitions follow the shared operand-role model, in the search,
//! in its indexed facts and in cache replay, for every opcode whose operand 0
//! is a read and every opcode that defines a register after operand 0.

use super::*;
use crate::coverage_gate::ALL_AARCH64_OPCODES;
use trust_cg_ir::function::Signature;
use trust_cg_opt::effects::OperandRole;

const GPR32: RegClass = RegClass::Gpr32;

fn vreg(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, GPR32))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

/// A single-block function of `insts`, then `Ret`.
fn function(name: &str, insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    for inst in insts {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    }
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(entry, ret);
    func
}

fn config() -> CegisSuperoptConfig {
    CegisSuperoptConfig {
        budget_sec: 3_600,
        per_query_ms: 1_000,
        target_triple: "aarch64-apple-darwin".to_string(),
        cpu: "apple-m1".to_string(),
        features: Vec::new(),
        opt_level: 2,
        search_schedule: CegisSearchScheduleIdentity::serial(),
        cache: None,
        trace: None,
    }
}

/// Every matched candidate of a search whose verifier accepts everything, the
/// searched function, and whether the search rewrote anything. Any candidate
/// the matchers admit would be committed, so an unchanged function means no
/// layer admitted a rewrite.
struct Search {
    candidates: Vec<String>,
    committed: bool,
    function: MachFunction,
}

fn search(func: &MachFunction, indexed: bool) -> Search {
    let mut pass = CegisSuperoptPass::new(config());
    pass.test_walk_script = Some(WalkScript {
        verdict: Box::new(|_, _| CegisResult::Equivalent {
            proof_hash: 0x486,
            iterations: 1,
        }),
        events: Vec::new(),
    });
    let mut searched = func.clone();
    let (committed, _, completion, _) = if indexed {
        let mut facts = IndexedWalkFacts::for_search(&searched);
        pass.search_layers(&mut searched, &mut facts, None)
    } else {
        pass.search_layers(&mut searched, &mut DirectWalkFacts, None)
    };
    assert_eq!(completion, CegisSearchCompletion::Complete);
    let candidates = pass
        .test_walk_script
        .take()
        .expect("script")
        .events
        .into_iter()
        .filter(|event| event.starts_with("candidate"))
        .collect();
    Search {
        candidates,
        committed,
        function: searched,
    }
}

/// Both kinds of walk facts must leave `func` exactly as it was.
fn assert_untouched(label: &str, func: &MachFunction) {
    for indexed in [false, true] {
        let result = search(func, indexed);
        assert!(
            !result.committed && format!("{:?}", result.function) == format!("{func:?}"),
            "{label} (indexed={indexed}): rewritten; candidates {:?}",
            result.candidates
        );
    }
}

/// Both kinds of walk facts must commit one rewrite of `layer`.
fn assert_rewritten(label: &str, func: &MachFunction, layer: &str) {
    for indexed in [false, true] {
        let result = search(func, indexed);
        assert!(
            result.committed
                && result
                    .candidates
                    .iter()
                    .any(|event| event.starts_with(&format!("candidate {layer} "))),
            "{label} (indexed={indexed}): no Layer {layer} rewrite; candidates {:?}",
            result.candidates
        );
    }
}

/// Revision 2's read count: every vreg operand after operand 0.
fn legacy_reads(func: &MachFunction, id: u32) -> usize {
    func.insts
        .iter()
        .flat_map(|inst| inst.operands.iter().skip(1))
        .filter(|operand| operand.as_vreg().is_some_and(|vreg| vreg.id == id))
        .count()
}

fn roles(opcode: AArch64Opcode, count: usize) -> Vec<OperandRole> {
    trust_cg_opt::effects::aarch64_operand_roles(opcode, count)
}

/// The operand positions the CEGIS helpers read and write, recovered by
/// giving each position its own vreg.
fn positions(opcode: AArch64Opcode, count: usize) -> (Vec<usize>, Vec<usize>) {
    let inst = MachInst::new(
        opcode,
        (0..count as u32)
            .map(|id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64)))
            .collect(),
    );
    let mut reads = Vec::new();
    for_each_vreg_read(&inst, |vreg| reads.push(vreg.id as usize));
    let mut defs = Vec::new();
    for_each_vreg_def(&inst, |vreg| defs.push(vreg.id as usize));
    (reads, defs)
}

/// The CEGIS read set must cover every read the register allocator's operand
/// partition sees (it treats every operand of a store, branch, return, call or
/// compare as a read), and every operand must be a read or a definition.
#[test]
fn cegis_reads_and_defs_cover_the_allocator_partition_for_every_opcode() {
    let mut operand_zero_reads = 0usize;
    for &opcode in ALL_AARCH64_OPCODES {
        for count in 1..=6usize {
            let (reads, defs) = positions(opcode, count);
            let inst = MachInst::new(
                opcode,
                (0..count as u32)
                    .map(|id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64)))
                    .collect(),
            );
            let allocator = crate::post_ra_reaching_def::operand_roles(&inst);
            for (pos, role) in allocator.iter().enumerate() {
                if role.is_use() {
                    assert!(
                        reads.contains(&pos),
                        "{opcode:?}/{count}: the allocator reads operand {pos}, CEGIS does not"
                    );
                }
            }
            for pos in 0..count {
                assert!(
                    reads.contains(&pos) || defs.contains(&pos),
                    "{opcode:?}/{count}: operand {pos} is neither read nor written"
                );
            }
            if count == 3 && reads.contains(&0) {
                operand_zero_reads += 1;
            }
        }
    }
    // Compares, stores, branches, traps, tied forms and atomics.
    eprintln!(
        "operand-role cross-check: {} opcodes x 6 arities; {operand_zero_reads} read operand 0 \
         of a 3-operand form",
        ALL_AARCH64_OPCODES.len()
    );
    assert!(operand_zero_reads > 60, "{operand_zero_reads}");
}

// ---------------------------------------------------------------------------
// The two reproducers
// ---------------------------------------------------------------------------

/// `Movz v10, #7; AddRR v11, v0, v10; CmpRR v10, v1`: revision 2 rewrote the
/// add to `AddRI #7` and spliced out the Movz the compare still reads.
#[test]
fn layer_b_keeps_a_movz_a_compare_still_reads() {
    let func = function(
        "repro_cmp",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(7)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(10), vreg(1)]),
        ],
    );
    assert_eq!(legacy_reads(&func, 10), 1, "revision 2 saw a single read");
    assert_eq!(count_vreg_uses(&func, VReg::new(10, GPR32)), 2);
    assert_untouched("Movz+AddRR+CmpRR", &func);
}

/// `Movz v10, #0xFF; AndRR v11, v0, v10; StrRI v10, [v2, #8]`: revision 2
/// rewrote the and to `AndRI #0xFF` and dropped the Movz the store reads.
#[test]
fn layer_c_keeps_a_mask_a_store_still_reads() {
    let func = function(
        "repro_str",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0xFF)]),
            MachInst::new(AArch64Opcode::AndRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(10), vreg(2), imm(8)]),
        ],
    );
    assert_eq!(legacy_reads(&func, 10), 1, "revision 2 saw a single read");
    assert_untouched("Movz+AndRR+StrRI", &func);
}

/// The fix must not cost the layers their ordinary rewrites, including a
/// Layer C chain whose `Movk`s read the mask they extend.
#[test]
fn single_reader_windows_are_still_rewritten() {
    let layer_b = function(
        "control_b",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0xFFF)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(11), vreg(1)]),
        ],
    );
    assert_rewritten("Movz #0xFFF + AddRR", &layer_b, "B");
    let layer_c = function(
        "control_c",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0x5555)]),
            MachInst::new(AArch64Opcode::Movk, vec![vreg(10), imm(0x5555), imm(16)]),
            MachInst::new(AArch64Opcode::AndRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(11), vreg(2), imm(8)]),
        ],
    );
    assert_rewritten("Movz+Movk+AndRR", &layer_c, "C");
    let layer_a = function(
        "control_a",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0)]),
            MachInst::new(AArch64Opcode::MulRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(10), vreg(2), imm(8)]),
        ],
    );
    assert_rewritten("Movz #0 + MulRR", &layer_a, "A");
}

/// `AddRI` is emitted as `ADD #imm12`; a larger Movz immediate would have
/// produced an unencodable instruction.
#[test]
fn layer_b_admits_only_encodable_add_immediates() {
    let window = |value| {
        function(
            "imm12",
            vec![
                MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(value)]),
                MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
            ],
        )
    };
    assert_rewritten("Movz #0xFFF", &window(0xFFF), "B");
    assert_untouched("Movz #0x1000", &window(0x1000));
    assert_untouched("Movz #0xFFFF", &window(0xFFFF));
}

// ---------------------------------------------------------------------------
// Every opcode whose operand 0 is a read
// ---------------------------------------------------------------------------

/// Opcodes whose operand 0 the shared role model reads, in a three-operand
/// shape.
fn operand_zero_readers() -> Vec<AArch64Opcode> {
    ALL_AARCH64_OPCODES
        .iter()
        .copied()
        .filter(|&opcode| roles(opcode, 3)[0].is_use())
        .collect()
}

/// For every opcode that reads operand 0, a later instruction of that opcode
/// reading the constant keeps the materializer: no layer rewrites the window.
#[test]
fn every_operand_zero_reader_keeps_the_materializer() {
    let readers = operand_zero_readers();
    for family in [
        AArch64Opcode::CmpRR,
        AArch64Opcode::CmpRI,
        AArch64Opcode::Tst,
        AArch64Opcode::StrRI,
        AArch64Opcode::StrbRI,
        AArch64Opcode::StrhRI,
        AArch64Opcode::StrRO,
        AArch64Opcode::StpRI,
        AArch64Opcode::StrPreIndex,
        AArch64Opcode::Cbz,
        AArch64Opcode::Cbnz,
        AArch64Opcode::Tbz,
        AArch64Opcode::Tbnz,
        AArch64Opcode::Br,
        AArch64Opcode::Blr,
        AArch64Opcode::Stlr,
        AArch64Opcode::VolatileStrRI,
        AArch64Opcode::Movk,
        AArch64Opcode::Bfm,
        AArch64Opcode::Retain,
        AArch64Opcode::Release,
    ] {
        assert!(readers.contains(&family), "{family:?} must read operand 0");
    }

    let mut rows = 0usize;
    for &opcode in &readers {
        let reader = |constant: u32| MachInst::new(opcode, vec![vreg(constant), vreg(1), vreg(2)]);
        let layer_b = function(
            "reader_b",
            vec![
                MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(7)]),
                MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
                reader(10),
            ],
        );
        let layer_c = function(
            "reader_c",
            vec![
                MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0xFF)]),
                MachInst::new(AArch64Opcode::AndRR, vec![vreg(11), vreg(0), vreg(10)]),
                reader(10),
            ],
        );
        for (label, func) in [("Layer B", &layer_b), ("Layer C", &layer_c)] {
            // Unless the reader also reads the constant after operand 0,
            // revision 2 saw one read and spliced the materializer out.
            let label = format!("{label} then {opcode:?} v10");
            assert_untouched(&label, func);
            rows += 1;
        }
    }
    eprintln!(
        "operand-0 readers: {} opcodes, {rows} Layer B/C rows keep the materializer",
        readers.len()
    );
    assert!(rows > 120, "{rows}");
}

/// The cache replay path applies the same rules: a recorded Layer B or C
/// rewrite of a window whose constant a compare or store still reads is
/// refused on the current body.
#[test]
fn cache_replay_refuses_rewrites_of_a_still_read_constant() {
    let replay = |func: &MachFunction, layer, replacement: MachInst, window_len| {
        let target = func
            .block(func.entry)
            .insts
            .iter()
            .copied()
            .find(|id| {
                matches!(
                    func.inst(*id).opcode,
                    AArch64Opcode::AddRR | AArch64Opcode::AndRR
                )
            })
            .expect("consumer");
        let entry = CegisCacheEntry {
            version: CegisCacheEntry::VERSION,
            completion: CegisSearchCompletion::Complete,
            proven_rewrites: vec![ProvenRewrite {
                inst_index: target.0,
                proof_hash: 0x486,
                iterations: 1,
                window_len,
                replacement: vec![MachInstBlob::from_inst(&replacement)],
                layer,
            }],
            attempted: 1,
            verified: 1,
            rejected: 0,
        };
        let mut replayed = func.clone();
        let (committed, ..) = CegisSuperoptPass::replay_cached_rewrites(&mut replayed, &entry);
        (committed, replayed)
    };

    let compare = function(
        "replay_cmp",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(7)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::CmpRR, vec![vreg(10), vreg(1)]),
        ],
    );
    let addri = MachInst::new(AArch64Opcode::AddRI, vec![vreg(11), vreg(0), imm(7)]);
    let (committed, replayed) = replay(&compare, RewriteLayer::B, addri.clone(), 2);
    assert!(!committed);
    assert_eq!(format!("{replayed:?}"), format!("{compare:?}"));

    let store = function(
        "replay_str",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0xFF)]),
            MachInst::new(AArch64Opcode::AndRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::StrRI, vec![vreg(10), vreg(2), imm(8)]),
        ],
    );
    let andri = MachInst::new(AArch64Opcode::AndRI, vec![vreg(11), vreg(0), imm(0xFF)]);
    let (committed, replayed) = replay(&store, RewriteLayer::C, andri.clone(), 2);
    assert!(!committed);
    assert_eq!(format!("{replayed:?}"), format!("{store:?}"));

    // Controls: without the extra reader both replays apply.
    let single = function(
        "replay_single",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(7)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
        ],
    );
    assert!(replay(&single, RewriteLayer::B, addri, 2).0);
    let single_mask = function(
        "replay_single_mask",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(0xFF)]),
            MachInst::new(AArch64Opcode::AndRR, vec![vreg(11), vreg(0), vreg(10)]),
        ],
    );
    assert!(replay(&single_mask, RewriteLayer::C, andri, 2).0);
}

/// Replay splices out only the window the matcher admits on the current body,
/// over the window length it implies, with a single replacement instruction:
/// a stale or corrupted entry cannot remove more of the block or insert more
/// instructions. (The body must also be the one the matcher rebuilds, which
/// `replay_tests` pins.)
#[test]
fn cache_replay_splices_only_the_matchers_window() {
    let func = function(
        "replay_exact",
        vec![
            MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(7)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(11), vreg(0), vreg(10)]),
            MachInst::new(AArch64Opcode::AddRR, vec![vreg(12), vreg(11), vreg(0)]),
        ],
    );
    let add = func.block(func.entry).insts[1];
    let replay = |replacement: Vec<MachInst>, window_len| {
        let entry = CegisCacheEntry {
            version: CegisCacheEntry::VERSION,
            completion: CegisSearchCompletion::Complete,
            proven_rewrites: vec![ProvenRewrite {
                inst_index: add.0,
                proof_hash: 0x486,
                iterations: 1,
                window_len,
                replacement: replacement.iter().map(MachInstBlob::from_inst).collect(),
                layer: RewriteLayer::B,
            }],
            attempted: 1,
            verified: 1,
            rejected: 0,
        };
        let mut replayed = func.clone();
        let (committed, ..) = CegisSuperoptPass::replay_cached_rewrites(&mut replayed, &entry);
        assert_eq!(
            committed,
            format!("{replayed:?}") != format!("{func:?}"),
            "a refused replay leaves the function untouched"
        );
        committed
    };
    let addri = |source: u32, value: i64| {
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(11), vreg(source), imm(value)],
        )
    };
    assert!(replay(vec![addri(0, 7)], 2), "the matcher's own window");
    assert!(!replay(vec![addri(0, 7)], 3), "a longer window");
    assert!(!replay(vec![addri(0, 7)], 1), "a shorter window");
    assert!(
        !replay(vec![addri(0, 7), addri(0, 7)], 2),
        "extra replacement instructions"
    );
}

// ---------------------------------------------------------------------------
// Definitions after operand 0, and under another register class
// ---------------------------------------------------------------------------

/// `(opcode, position)` for every opcode and operand position after 0 that
/// the shared role model defines (without reading), in a four-operand shape.
fn later_definitions() -> Vec<(AArch64Opcode, usize)> {
    let mut rows = Vec::new();
    for &opcode in ALL_AARCH64_OPCODES {
        for (pos, role) in roles(opcode, 4).into_iter().enumerate().skip(1) {
            if role == OperandRole::Def {
                rows.push((opcode, pos));
            }
        }
    }
    rows
}

/// Revision 2 counted such a definition as a read, which happened to keep the
/// materializer; with reads counted exactly, only the def-side rule keeps a
/// constant that was overwritten before its consumer from being folded in.
#[test]
fn a_later_definition_of_the_constant_hides_the_materializer() {
    let rows = later_definitions();
    eprintln!(
        "later definitions: {} (opcode, operand) rows x Layers A, B and C",
        rows.len()
    );
    for family in [
        AArch64Opcode::LdpRI,
        AArch64Opcode::LdpPostIndex,
        AArch64Opcode::Ldxp,
    ] {
        assert!(
            rows.iter().any(|(opcode, _)| *opcode == family),
            "{family:?} defines operand 1"
        );
    }

    for &(opcode, pos) in &rows {
        let mut operands = vec![vreg(20), vreg(21), vreg(22), vreg(23)];
        operands[pos] = vreg(10);
        let clobber = MachInst::new(opcode, operands);
        for (layer, materializer, consumer) in [
            ("A", 0, AArch64Opcode::MulRR),
            ("B", 7, AArch64Opcode::AddRR),
            ("C", 0xFF, AArch64Opcode::AndRR),
        ] {
            let func = function(
                "clobbered",
                vec![
                    MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(materializer)]),
                    clobber.clone(),
                    MachInst::new(consumer, vec![vreg(11), vreg(0), vreg(10)]),
                ],
            );
            assert_untouched(
                &format!("Layer {layer}: {opcode:?} defines v10 at operand {pos}"),
                &func,
            );
        }
    }
}

/// Vreg identity is the id: a write to the same id under another class is a
/// definition of the constant's register.
#[test]
fn a_definition_under_another_class_hides_the_materializer() {
    let wide = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
    for (materializer, consumer) in [
        (7, AArch64Opcode::AddRR),
        (0xFF, AArch64Opcode::AndRR),
        (0, AArch64Opcode::MulRR),
    ] {
        let func = function(
            "reclassed",
            vec![
                MachInst::new(AArch64Opcode::Movz, vec![vreg(10), imm(materializer)]),
                MachInst::new(AArch64Opcode::AddRR, vec![wide(10), wide(20), wide(21)]),
                MachInst::new(consumer, vec![vreg(11), vreg(0), vreg(10)]),
            ],
        );
        assert_untouched(&format!("{consumer:?} after a Gpr64 write of v10"), &func);
    }
}
