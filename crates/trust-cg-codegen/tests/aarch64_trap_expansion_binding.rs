// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The trap-expansion obligations (`trust_cg_verify::aarch64_trap_expansion`,
//! ledger L04-P12) against this backend's live expansion, encoder and ENC-5.
//!
//! For every modeled carrier form, `lower::expand_trap_*` must emit exactly
//! the expansion the verifier states and record it in
//! `MachFunction::trap_expansions`; the live encoder's words must be the
//! verifier's own encoding, each must pass its per-word ENC-5 arm, and the
//! words together must trap exactly when the carrier's condition holds. The
//! final encoder must refuse a recorded expansion whose emitted words do not
//! (a tampered carrier, a partial expansion) or are not contiguous (an
//! instruction placed inside it). Host-neutral: nothing executes.
//! The native execution of every trap and non-trap path is
//! `e2e_aarch64_trap_expansion_native`.

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_codegen::lower;
use trust_cg_ir::aarch64_regs::{X2, X3, X4, X5};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature};
use trust_cg_verify::aarch64_trap_expansion::{
    TrapKind, carrier_instruction, check_emitted_trap_expansion, expansion_word, stated_expansion,
    trap_battery,
};

fn expand_all(func: &mut MachFunction) {
    lower::expand_trap_bounds_check_exact(func);
    lower::expand_trap_null_if_zero(func);
    lower::expand_trap_div_zero_if_zero(func);
    lower::expand_trap_shift_range_if_oob(func);
    lower::expand_trap_overflow_exact(func);
}

fn single(inst: MachInst, tail: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new("trap".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    for inst in std::iter::once(inst).chain(tail) {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    }
    func
}

fn same(a: &MachInst, b: &MachInst) -> bool {
    a.opcode == b.opcode && a.operands == b.operands
}

#[test]
fn the_live_expansion_is_the_stated_expansion_for_every_form() {
    let mut words_checked = 0usize;
    for carrier in trap_battery() {
        let carrier_inst = carrier_instruction(&carrier);
        let mut func = single(carrier_inst.clone(), Vec::new());
        expand_all(&mut func);
        let block = func.blocks[func.entry.0 as usize].insts.clone();
        let members: Vec<&MachInst> = block.iter().map(|&id| func.inst(id)).collect();
        if matches!(carrier.kind, TrapKind::Unconditional { .. }) {
            assert!(func.trap_expansions.is_empty(), "{carrier:?}");
            assert_eq!(members.len(), 1);
            let word = encode_instruction(members[0]).expect("a BRK encodes");
            assert_eq!(check_emitted_trap_expansion(&carrier_inst, &[word]), Ok(()));
            continue;
        }
        assert_eq!(func.trap_expansions.len(), 1, "{carrier:?}");
        let record = &func.trap_expansions[0];
        assert!(same(&record.carrier, &carrier_inst), "{carrier:?}");
        assert_eq!(
            record.insts, block,
            "{carrier:?}: the record is the whole expansion"
        );
        let stated = stated_expansion(&carrier);
        assert_eq!(members.len(), stated.len(), "{carrier:?}");
        let mut live = Vec::new();
        for (member, stated) in members.iter().zip(&stated) {
            assert!(
                same(member, stated),
                "{carrier:?}: {member:?} vs {stated:?}"
            );
            let word = encode_instruction(member)
                .unwrap_or_else(|error| panic!("{carrier:?}: {member:?}: {error}"));
            assert_eq!(
                Ok(word),
                expansion_word(member),
                "{carrier:?}: the live encoder and the verifier's encoder disagree on {member:?}"
            );
            let outcome = A64DecodeCheck.check_one(member, &word.to_le_bytes(), None);
            assert!(
                matches!(outcome, DecodeCheckOutcome::Match),
                "{carrier:?}: ENC-5 does not decode {member:?} = {word:#010x}: {outcome:?}"
            );
            live.push(word);
            words_checked += 1;
        }
        assert_eq!(
            check_emitted_trap_expansion(&record.carrier, &live),
            Ok(()),
            "{carrier:?}"
        );
    }
    assert!(words_checked > 100, "{words_checked}");
}

/// ENC-5 refuses a carrier itself: only its expansion is ever emitted.
#[test]
fn enc5_refuses_an_unexpanded_carrier_word() {
    for carrier in trap_battery()
        .into_iter()
        .filter(|carrier| carrier.is_conditional())
    {
        let inst = carrier_instruction(&carrier);
        assert!(
            matches!(
                A64DecodeCheck.check_one(&inst, &0xD420_0020u32.to_le_bytes(), None),
                DecodeCheckOutcome::Mismatch(_)
            ),
            "{carrier:?}"
        );
    }
}

fn div_guard() -> MachFunction {
    let mut func = single(
        MachInst::new(
            AArch64Opcode::TrapDivZeroIfZero,
            vec![MachOperand::PReg(X3)],
        ),
        vec![MachInst::new(AArch64Opcode::Ret, vec![])],
    );
    expand_all(&mut func);
    func
}

#[test]
fn the_final_encoder_binds_the_recorded_expansion() {
    // Faithful: encodes.
    let func = div_guard();
    let (code, _) = trust_cg_codegen::pipeline::encode_function_with_fixups(&func)
        .expect("the faithful expansion encodes");
    assert_eq!(
        &code[..8],
        &[0x43, 0x00, 0x00, 0xB5, 0x20, 0x00, 0x20, 0xD4]
    );

    // The record names another divisor register than the CBNZ tests.
    let mut tampered = div_guard();
    tampered.trap_expansions[0].carrier = MachInst::new(
        AArch64Opcode::TrapDivZeroIfZero,
        vec![MachOperand::PReg(X4)],
    );
    let error = trust_cg_codegen::pipeline::encode_function_with_fixups(&tampered)
        .expect_err("a word sequence that does not test the carrier's divisor is refused")
        .to_string();
    assert!(
        error.contains("ENC-5 trap expansion") && error.contains("counterexample"),
        "{error}"
    );

    // Only part of the expansion is left in the stream (its branch was
    // dropped, so the trap would fire unconditionally).
    let mut partial = div_guard();
    let entry = partial.entry.0 as usize;
    let branch = partial.trap_expansions[0].insts[0];
    partial.blocks[entry].insts.retain(|&id| id != branch);
    let error = trust_cg_codegen::pipeline::encode_function_with_fixups(&partial)
        .expect_err("a partial expansion is refused")
        .to_string();
    assert!(error.contains("only part of the expansion"), "{error}");
}

/// An instruction placed inside a recorded expansion is refused even when
/// every word still passes its own ENC-5 arm: here `CMP X5, #0` between the
/// bounds guard's `CMP X3, #10` and its `B.LO`, which makes the guard test the
/// wrong flags (it would trap for every index).
#[test]
fn the_final_encoder_refuses_a_non_contiguous_expansion() {
    let bounds_guard = || {
        let mut func = single(
            MachInst::new(
                AArch64Opcode::TrapBoundsCheckExact,
                vec![
                    MachOperand::PReg(X2),
                    MachOperand::PReg(X3),
                    MachOperand::Imm(10),
                ],
            ),
            vec![MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_all(&mut func);
        func
    };
    let (code, _) = trust_cg_codegen::pipeline::encode_function_with_fixups(&bounds_guard())
        .expect("the faithful expansion encodes");
    assert_eq!(
        &code[..12],
        &[
            0x7F, 0x28, 0x00, 0xF1, 0x43, 0x00, 0x00, 0x54, 0x20, 0x00, 0x20, 0xD4
        ]
    );

    let mut split = bounds_guard();
    assert_eq!(split.trap_expansions[0].insts.len(), 3);
    let clobber = split.push_inst(MachInst::new(
        AArch64Opcode::CmpRI,
        vec![MachOperand::PReg(X5), MachOperand::Imm(0)],
    ));
    let entry = split.entry.0 as usize;
    split.blocks[entry].insts.insert(1, clobber);
    let error = trust_cg_codegen::pipeline::encode_function_with_fixups(&split)
        .expect_err("an expansion with an instruction inside it is refused")
        .to_string();
    assert!(
        error.contains("ENC-5 trap expansion")
            && error.contains("not contiguous (offsets [0, 8, 12])"),
        "{error}"
    );
}
