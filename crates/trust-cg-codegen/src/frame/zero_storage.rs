// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.

//! Conservative eligibility for omitting a leaf's otherwise empty frame.
//! This changes frame selection only; normal instruction verification still runs.

use super::*;

fn needs_preservation(reg: PReg) -> bool {
    // Include W aliases of FP, LR and SP as well as every callee-saved bank.
    matches!(reg.encoding(), 29..=31 | 61..=63)
        || callee_saved_gpr_index(reg).is_some()
        || callee_saved_fpr_index(reg).is_some()
}

/// Whether the verifier's source-bound frame owner may bind this function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum OwnerEnvelopes {
    /// The owner may judge the source: keep the envelopes it binds through.
    Keep,
    /// No frame-bound evidence is needed: the source has a frameless route
    /// or lies outside the frame owner's domain. Normal proof checks remain.
    Independent,
}

pub(super) fn eligible(instructions: &FrameInstructions<'_>, owner: OwnerEnvelopes) -> bool {
    let func = instructions.function();
    let keep_owner_envelopes = owner == OwnerEnvelopes::Keep;
    // A fixed zero-byte slot reserves no storage: instruction selection
    // leaves one behind when it folds away every access to a private slot,
    // keeping the slot's id. Any instruction that addresses a slot is still
    // refused by the operand check below.
    if func
        .stack_slots
        .iter()
        .any(|slot| slot.is_runtime_sized() || slot.size != 0)
        || func.eh_metadata.has_eh_info()
    {
        return false;
    }
    // Scalar copies, constants and conditional returns need the checked frame
    // envelope to bind their complete source/return relation. A single instruction's
    // exhaustive machine theorem alone cannot replace that source evidence.
    // Keep the envelope until a frameless whole-body owner checks the return.
    if keep_owner_envelopes
        && !func.signature.returns.is_empty()
        && instructions.iter().all(|inst| {
            matches!(
                inst.opcode,
                AArch64Opcode::Nop
                    | AArch64Opcode::AlignNop
                    | AArch64Opcode::Ret
                    | AArch64Opcode::Copy
                    | AArch64Opcode::MovR
                    | AArch64Opcode::MOVWrr
                    | AArch64Opcode::MOVXrr
                    | AArch64Opcode::MovI
                    | AArch64Opcode::Movz
                    | AArch64Opcode::Movn
                    | AArch64Opcode::Movk
                    | AArch64Opcode::MOVZWi
                    | AArch64Opcode::MOVZXi
                    | AArch64Opcode::CmpRR
                    | AArch64Opcode::CmpRI
                    | AArch64Opcode::CMPWrr
                    | AArch64Opcode::CMPXrr
                    | AArch64Opcode::CMPWri
                    | AArch64Opcode::CMPXri
                    | AArch64Opcode::CSet
                    | AArch64Opcode::Csel
                    | AArch64Opcode::Csinc
                    | AArch64Opcode::Csinv
                    | AArch64Opcode::Csneg
                    | AArch64Opcode::B
                    | AArch64Opcode::BCond
                    | AArch64Opcode::Bcc
                    | AArch64Opcode::Cbz
                    | AArch64Opcode::Cbnz
                    | AArch64Opcode::Tbz
                    | AArch64Opcode::Tbnz
            )
        })
    {
        return false;
    }
    instructions.iter().all(|inst| {
        use AArch64Opcode::*;
        // These ALU operations obtain source-bound Formal evidence through
        // the checked sixteen-byte frame owner. Preserve that envelope until
        // the verifier has an independently checked frameless body owner too.
        // Frame omission must not turn supported proof exports into sampling.
        // A source the owner never judges has no such export to preserve.
        let owner_alu = matches!(
            inst.opcode,
            AddRR | AddRI | AddRIShift12 | SubRR | SubRI | LslRI
        );
        if owner_alu && keep_owner_envelopes {
            return false;
        }
        // This exact late-expanded guard only compares volatile 64-bit
        // registers and traps. Large constants use reserved scratch X16; no
        // SP/FP/LR access or call is introduced by its expansion. Restrict the
        // accepted shape here so malformed or wider carrier forms keep a frame.
        if inst.opcode == TrapBoundsCheckExact
            && !matches!(
                inst.operands.as_slice(),
                [MachOperand::PReg(base), MachOperand::PReg(index), MachOperand::Imm(bound)]
                    if base.encoding() < 16 && index.encoding() < 16
                        && (0..=i64::from(i32::MAX)).contains(bound)
            )
        {
            return false;
        }
        // Direct page/low-offset materialization has only its explicit volatile
        // register effects. It neither calls nor touches SP, FP or LR. Keep
        // malformed, GOT/TLS and wider register forms outside this policy;
        // ordinary instruction and object-relocation verification still apply.
        let direct_symbol = |operand: &MachOperand| {
            matches!(operand,
            MachOperand::Symbol(name) | MachOperand::ExactModuleSymbol(name) if !name.is_empty())
        };
        let symbol_address = match (inst.opcode, inst.operands.as_slice()) {
            (Adrp, [MachOperand::PReg(dst), symbol]) => {
                dst.encoding() < 16 && direct_symbol(symbol)
            }
            (AddPCRel, [MachOperand::PReg(dst), MachOperand::PReg(base), symbol]) => {
                dst.encoding() < 16 && base.encoding() < 16 && direct_symbol(symbol)
            }
            _ => false,
        };
        // Audit hardware operations with explicit register effects. New or
        // opaque opcodes keep the established frame until reviewed here.
        let explicit_effects = symbol_address
            || owner_alu
            || matches!(
                inst.opcode,
                MulRR
                    | Msub
                    | Smull
                    | Umull
                    | SDiv
                    | UDiv
                    | Neg
                    | AndRR
                    | AndRI
                    | OrrRR
                    | OrrRI
                    | EorRR
                    | EorRI
                    | EorRRShift
                    | AddRRShift
                    | SubRRShift
                    | EorRRLsl
                    | EorRRLsr
                    | AddRRShiftLsr
                    | OrnRR
                    | BicRR
                    | LslRR
                    | LsrRR
                    | AsrRR
                    | LsrRI
                    | AsrRI
                    | RorRI
                    | Rbit
                    | CmpRR
                    | CmpRI
                    | Tst
                    | Csel
                    | Csinc
                    | Csinv
                    | Csneg
                    | CSet
                    | MovR
                    | MovI
                    | Movz
                    | Movn
                    | Movk
                    | MOVWrr
                    | MOVXrr
                    | CMPWrr
                    | CMPXrr
                    | CMPWri
                    | CMPXri
                    | MOVZWi
                    | MOVZXi
                    | Sxtw
                    | Uxtw
                    | Sxtb
                    | Sxth
                    | Uxtb
                    | Uxth
                    | Ubfm
                    | Sbfm
                    | Bfm
                    | AddsRR
                    | AddsRI
                    | SubsRR
                    | SubsRI
                    | Adc
                    | Sbc
                    | Adcs
                    | Sbcs
                    | Umulh
                    | Smulh
                    | Madd
                    | LdrRI
                    | StrRI
                    | LdrbRI
                    | LdrhRI
                    | LdrsbRI
                    | LdrshRI
                    | StrbRI
                    | StrhRI
                    | LdpRI
                    | StpRI
                    | LdrRO
                    | StrRO
                    | LdrbRO
                    | LdrhRO
                    | StrbRO
                    | StrhRO
                    | LdrswRO
                    | STRWui
                    | STRXui
                    | STRSui
                    | STRDui
                    | VolatileLdrRI
                    | VolatileLdrbRI
                    | VolatileLdrhRI
                    | VolatileStrRI
                    | VolatileStrbRI
                    | VolatileStrhRI
                    | FaddRR
                    | FsubRR
                    | FmulRR
                    | FdivRR
                    | FmaddRR
                    | FminnmRR
                    | FmaxnmRR
                    | FnegRR
                    | FabsRR
                    | FsqrtRR
                    | FrintmRR
                    | FrintpRR
                    | FrintzRR
                    | Fcmp
                    | FcselRR
                    | FcvtzsRR
                    | FcvtzuRR
                    | ScvtfRR
                    | UcvtfRR
                    | FcvtSD
                    | FcvtDS
                    | FcvtHS
                    | FcvtHD
                    | FcvtSH
                    | FcvtDH
                    | FmovGprFpr
                    | FmovFprGpr
                    | FmovFprFpr
                    | FmovImm
                    | B
                    | BCond
                    | Bcc
                    | Cbz
                    | Cbnz
                    | Tbz
                    | Tbnz
                    | Ret
                    | Copy
                    | Nop
                    | AlignNop
                    | TrapBoundsCheckExact
            );
        if !explicit_effects || inst.is_call() || inst.opcode.default_flags().is_call() {
            return false;
        }
        if inst
            .implicit_defs
            .iter()
            .any(|&reg| needs_preservation(reg))
            || inst
                .implicit_uses
                .iter()
                .any(|&reg| needs_preservation(reg) && !(inst.opcode == Ret && reg == X30))
        {
            return false;
        }
        if inst.opcode == Ret {
            return inst.operands.is_empty()
                || matches!(inst.operands.as_slice(), [MachOperand::PReg(reg)] if *reg == X30);
        }
        inst.operands.iter().all(|operand| match operand {
            MachOperand::PReg(reg) | MachOperand::MemOp { base: reg, .. } => {
                !needs_preservation(*reg)
            }
            MachOperand::Special(SpecialReg::SP)
            | MachOperand::StackSlot(_)
            | MachOperand::FrameIndex(_)
            | MachOperand::IncomingArg(_)
            | MachOperand::JumpTableIndex(_) => false,
            MachOperand::Symbol(_) | MachOperand::ExactModuleSymbol(_) => symbol_address,
            // Deleted instructions can retain inert virtual operands.
            MachOperand::VReg(_) => inst.opcode == Nop,
            _ => true,
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::{StackProtectorMode, StackSlotSizeSource};
    use trust_cg_ir::inst::InstFlags;
    use trust_cg_ir::regs::{W29, W30, WSP, X1};

    fn make_func(name: &str, insts: Vec<MachInst>) -> MachFunction {
        let mut func =
            MachFunction::new(name.to_owned(), trust_cg_ir::Signature::new(vec![], vec![]));
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(func.entry, id);
        }
        func
    }

    fn layout(func: &MachFunction) -> FrameLayout {
        try_compute_frame_layout_with_leaf_policy(func, 0, false, LeafFramePolicy::OmitZeroStorage)
            .unwrap()
    }

    #[test]
    fn zero_storage_preserves_source_bound_constant_and_copy_returns() {
        for body in [
            vec![],
            vec![MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
            )],
            vec![MachInst::new(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(42),
                    MachOperand::Imm(0),
                ],
            )],
            vec![
                MachInst::new(
                    AArch64Opcode::Movn,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::Imm(7),
                        MachOperand::Imm(0),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::Movk,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::Imm(5),
                        MachOperand::Imm(16),
                    ],
                ),
            ],
        ] {
            let mut instructions = body;
            instructions.push(MachInst::new(AArch64Opcode::Ret, vec![]));
            let mut function = make_func("scalar_return", instructions);
            assert_eq!(layout(&function).total_frame_size, 0);
            function.signature.returns.push(trust_cg_ir::Type::I64);
            let frame = layout(&function);
            assert!(frame.uses_frame_pointer && !frame.uses_red_zone);
            assert_eq!(frame.total_frame_size, 16);
        }
    }

    #[test]
    fn zero_storage_output_leaf_omits_frame_without_red_zone() {
        let func = make_func(
            "writer",
            vec![
                MachInst::new(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::PReg(X0),
                        MachOperand::Imm(0),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        let frame = layout(&func);
        assert_eq!(frame.total_frame_size, 0);
        assert!(!frame.uses_red_zone && !frame.uses_frame_pointer);
        assert!(emit_prologue(&frame).is_empty());
        assert_eq!(emit_epilogue(&frame).len(), 1);
        assert!(
            crate::dwarf_cfi::DwarfFde::from_layout(&frame, 0, 8, 0)
                .instructions
                .is_empty()
        );
        assert_eq!(
            try_compute_frame_layout(&func, 0, false)
                .unwrap()
                .total_frame_size,
            16
        );
    }

    #[test]
    fn zero_storage_exact_bounds_guard_uses_no_stack_or_preserved_registers() {
        for bound in [0, 8, 4096, i64::from(i32::MAX)] {
            let mut function = make_func(
                "guard",
                vec![
                    MachInst::new(
                        AArch64Opcode::TrapBoundsCheckExact,
                        vec![
                            MachOperand::PReg(X0),
                            MachOperand::PReg(X1),
                            MachOperand::Imm(bound),
                        ],
                    ),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            let frame = layout(&function);
            assert_eq!(frame.total_frame_size, 0);
            assert!(!frame.uses_red_zone && !frame.uses_frame_pointer);
            assert!(
                crate::dwarf_cfi::DwarfFde::from_layout(&frame, 0, 20, 0)
                    .instructions
                    .is_empty()
            );
            crate::lower::expand_trap_bounds_check_exact(&mut function);
            assert!(
                function
                    .insts
                    .iter()
                    .any(|inst| inst.opcode == AArch64Opcode::Brk)
            );
            for inst in &function.insts {
                assert!(!inst.is_call());
                for operand in &inst.operands {
                    if let MachOperand::PReg(reg) = operand {
                        assert!(!needs_preservation(*reg));
                    }
                    assert!(!matches!(
                        operand,
                        MachOperand::StackSlot(_) | MachOperand::FrameIndex(_)
                    ));
                }
            }
        }
    }

    #[test]
    fn zero_storage_bounds_guard_requires_exact_allocated_volatile_shape() {
        let valid = vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
            MachOperand::Imm(8),
        ];
        let mut invalid = vec![vec![], valid[..2].to_vec()];
        let mut extra = valid.clone();
        extra.push(MachOperand::Imm(1));
        invalid.push(extra);
        for position in [0, 1] {
            for reg in [
                X19,
                X29,
                X30,
                SP,
                W29,
                W30,
                WSP,
                trust_cg_ir::regs::X16,
                trust_cg_ir::regs::X17,
                trust_cg_ir::regs::W0,
            ] {
                let mut changed = valid.clone();
                changed[position] = MachOperand::PReg(reg);
                invalid.push(changed);
            }
        }
        for bound in [
            MachOperand::Imm(-1),
            MachOperand::Imm(i64::from(i32::MAX) + 1),
            MachOperand::PReg(X0),
        ] {
            let mut changed = valid.clone();
            changed[2] = bound;
            invalid.push(changed);
        }
        for operands in invalid {
            let function = make_func(
                "invalid_guard",
                vec![MachInst::new(AArch64Opcode::TrapBoundsCheckExact, operands)],
            );
            assert!(layout(&function).uses_frame_pointer);
        }
        let inst =
            MachInst::new(AArch64Opcode::TrapBoundsCheckExact, valid).with_implicit_defs(&[X19]);
        assert!(layout(&make_func("implicit_guard", vec![inst])).uses_frame_pointer);
    }

    #[test]
    fn zero_storage_direct_global_address_has_no_frame_or_cfi_adjustment() {
        for symbol in [
            MachOperand::Symbol("data".into()),
            MachOperand::ExactModuleSymbol("data".into()),
        ] {
            let function = make_func(
                "address",
                vec![
                    MachInst::new(
                        AArch64Opcode::Adrp,
                        vec![MachOperand::PReg(X1), symbol.clone()],
                    ),
                    MachInst::new(
                        AArch64Opcode::AddPCRel,
                        vec![MachOperand::PReg(X0), MachOperand::PReg(X1), symbol],
                    ),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            let frame = layout(&function);
            assert_eq!(frame.total_frame_size, 0);
            assert!(!frame.uses_frame_pointer && !frame.uses_red_zone);
            assert!(emit_prologue(&frame).is_empty());
            assert_eq!(emit_epilogue(&frame).len(), 1);
            assert!(
                crate::dwarf_cfi::DwarfFde::from_layout(&frame, 0, 12, 0)
                    .instructions
                    .is_empty()
            );
            assert_eq!(
                try_compute_frame_layout(&function, 0, false)
                    .unwrap()
                    .total_frame_size,
                16
            );
        }
    }

    #[test]
    fn zero_storage_direct_address_requires_exact_shape_and_explicit_effects() {
        for (opcode, valid) in [
            (
                AArch64Opcode::Adrp,
                vec![MachOperand::PReg(X0), MachOperand::Symbol("data".into())],
            ),
            (
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Symbol("data".into()),
                ],
            ),
        ] {
            let mut malformed = vec![vec![], valid[..valid.len() - 1].to_vec()];
            let mut extra = valid.clone();
            extra.push(MachOperand::Imm(0));
            malformed.push(extra);
            for position in 0..valid.len() - 1 {
                for operand in [
                    MachOperand::PReg(X19),
                    MachOperand::PReg(X29),
                    MachOperand::PReg(X30),
                    MachOperand::PReg(SP),
                    MachOperand::PReg(W29),
                    MachOperand::PReg(W30),
                    MachOperand::PReg(WSP),
                    MachOperand::PReg(trust_cg_ir::regs::X16),
                    MachOperand::PReg(trust_cg_ir::regs::X17),
                    MachOperand::PReg(trust_cg_ir::regs::W0),
                    MachOperand::PReg(trust_cg_ir::regs::V0),
                    MachOperand::Imm(0),
                ] {
                    let mut operands = valid.clone();
                    operands[position] = operand;
                    malformed.push(operands);
                }
            }
            for symbol in [
                MachOperand::Symbol(String::new()),
                MachOperand::ExactModuleSymbol(String::new()),
                MachOperand::Imm(0),
                MachOperand::PReg(X0),
            ] {
                let mut operands = valid.clone();
                *operands.last_mut().unwrap() = symbol;
                malformed.push(operands);
            }
            for operands in malformed {
                assert!(
                    layout(&make_func(
                        "malformed",
                        vec![MachInst::new(opcode, operands)]
                    ))
                    .uses_frame_pointer
                );
            }
            for inst in [
                MachInst::new(opcode, valid.clone()).with_implicit_defs(&[X19]),
                MachInst::new(opcode, valid.clone()).with_implicit_uses(&[X29]),
            ] {
                assert!(layout(&make_func("implicit", vec![inst])).uses_frame_pointer);
            }
            let mut call = MachInst::new(opcode, valid);
            call.flags = AArch64Opcode::Bl.default_flags();
            assert!(layout(&make_func("call_flags", vec![call])).uses_frame_pointer);
        }
        for opcode in [
            AArch64Opcode::LdrGot,
            AArch64Opcode::LdrTlvp,
            AArch64Opcode::MovR,
        ] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Symbol("data".into()),
                ],
            );
            assert!(layout(&make_func("other_symbol_effects", vec![inst])).uses_frame_pointer);
        }
    }

    #[test]
    fn zero_storage_rejects_preserved_registers_and_stack_operands() {
        const REG_SETS: &[&[PReg]] = &[
            &[X19],
            &[X29],
            &[X30],
            &[SP],
            &[W29],
            &[W30],
            &[WSP],
            &[V8],
            &[PReg::new(173)],
        ];
        for &regs in REG_SETS {
            let reg = regs[0];
            for operand in [
                MachOperand::PReg(reg),
                MachOperand::MemOp {
                    base: reg,
                    offset: 0,
                },
            ] {
                let func = make_func(
                    "dependency",
                    vec![MachInst::new(
                        AArch64Opcode::MovR,
                        vec![MachOperand::PReg(X0), operand],
                    )],
                );
                assert!(layout(&func).uses_frame_pointer, "{reg:?}");
            }
            for inst in [
                MachInst::new(AArch64Opcode::Nop, vec![]).with_implicit_defs(regs),
                MachInst::new(AArch64Opcode::Nop, vec![]).with_implicit_uses(regs),
            ] {
                assert!(layout(&make_func("implicit", vec![inst])).uses_frame_pointer);
            }
        }
        for operand in [
            MachOperand::Special(SpecialReg::SP),
            MachOperand::StackSlot(trust_cg_ir::StackSlotId(0)),
            MachOperand::FrameIndex(trust_cg_ir::FrameIdx(0)),
            MachOperand::IncomingArg(0),
        ] {
            let func = make_func(
                "stack_operand",
                vec![MachInst::new(AArch64Opcode::MovR, vec![operand])],
            );
            assert!(layout(&func).uses_frame_pointer);
        }
    }

    #[test]
    fn zero_storage_rejects_calls_opaque_operations_and_nonstandard_returns() {
        for opcode in [
            AArch64Opcode::Bl,
            AArch64Opcode::BL,
            AArch64Opcode::Blr,
            AArch64Opcode::BLR,
            AArch64Opcode::TlsDescCall,
            AArch64Opcode::BlrTlsdesc,
            AArch64Opcode::TailCall,
            AArch64Opcode::StackAlloc,
            AArch64Opcode::LlscRmw64,
            AArch64Opcode::Release,
            AArch64Opcode::Br,
        ] {
            let mut inst = MachInst::new(opcode, vec![]);
            inst.flags = InstFlags::EMPTY;
            assert!(
                layout(&make_func("opaque", vec![inst])).uses_frame_pointer,
                "{opcode:?}"
            );
        }
        for reg in [X0, W30] {
            assert!(
                layout(&make_func(
                    "return",
                    vec![MachInst::new(
                        AArch64Opcode::Ret,
                        vec![MachOperand::PReg(reg)]
                    )]
                ))
                .uses_frame_pointer
            );
        }
        for ret in [
            MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
            MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X30]),
        ] {
            assert_eq!(layout(&make_func("return", vec![ret])).total_frame_size, 0);
        }
        assert!(
            layout(&make_func(
                "return_def",
                vec![MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_defs(&[X30])]
            ))
            .uses_frame_pointer
        );
    }

    #[test]
    fn zero_storage_preserves_frame_bound_arithmetic_evidence() {
        for opcode in [
            AArch64Opcode::AddRR,
            AArch64Opcode::AddRI,
            AArch64Opcode::AddRIShift12,
            AArch64Opcode::SubRR,
            AArch64Opcode::SubRI,
            AArch64Opcode::LslRI,
        ] {
            let rhs = if matches!(opcode, AArch64Opcode::AddRR | AArch64Opcode::SubRR) {
                MachOperand::PReg(X1)
            } else {
                MachOperand::Imm(1)
            };
            let func = make_func(
                "arithmetic",
                vec![
                    MachInst::new(
                        opcode,
                        vec![MachOperand::PReg(X0), MachOperand::PReg(X0), rhs],
                    ),
                    MachInst::new(AArch64Opcode::Ret, vec![]),
                ],
            );
            assert!(layout(&func).uses_frame_pointer, "{opcode:?}");
        }
    }

    /// Without a source the frame owner judges, the envelopes above earn
    /// nothing: the same ALU bodies and scalar returns are audited like any
    /// other explicit-effect leaf, as the red-zone lowering already treats them.
    /// Storage, preserved registers, SP operands and calls still keep a frame.
    #[test]
    fn zero_storage_unowned_source_audits_owner_envelopes() {
        let unowned = |func: &MachFunction| {
            try_compute_frame_layout_with_leaf_policy(
                func,
                0,
                false,
                LeafFramePolicy::OmitZeroStorageWithoutFrameOwner,
            )
            .unwrap()
        };
        let returning = |insts: Vec<MachInst>| {
            let mut func = make_func("unowned", insts);
            func.signature.returns.push(trust_cg_ir::Type::I64);
            func
        };
        let mut bodies = Vec::new();
        for opcode in [
            AArch64Opcode::AddRR,
            AArch64Opcode::AddRI,
            AArch64Opcode::AddRIShift12,
            AArch64Opcode::SubRR,
            AArch64Opcode::SubRI,
            AArch64Opcode::LslRI,
        ] {
            let rhs = if matches!(opcode, AArch64Opcode::AddRR | AArch64Opcode::SubRR) {
                MachOperand::PReg(X1)
            } else {
                MachOperand::Imm(1)
            };
            bodies.push(vec![MachInst::new(
                opcode,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X0), rhs],
            )]);
        }
        // The multiply-by-constant leaf: ADD, shifted ADD, SUB.
        bodies.push(vec![
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                ],
            ),
            MachInst::new(
                AArch64Opcode::AddRRShift,
                vec![
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                ],
            ),
            MachInst::new(
                AArch64Opcode::SubRR,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X0),
                ],
            ),
        ]);
        bodies.push(vec![MachInst::new(
            AArch64Opcode::Movz,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(42),
                MachOperand::Imm(0),
            ],
        )]);
        bodies.push(vec![MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        )]);
        for body in bodies {
            let mut insts = body;
            insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
            let func = returning(insts);
            let owned = layout(&func);
            assert!(owned.uses_frame_pointer, "{:?}", func.insts);
            assert_eq!(owned.total_frame_size, 16);
            let frame = unowned(&func);
            assert!(!frame.uses_frame_pointer && !frame.uses_red_zone);
            assert_eq!(frame.total_frame_size, 0);
            assert!(frame.callee_saved_pairs.is_empty());
            assert!(emit_prologue(&frame).is_empty());
            assert_eq!(emit_epilogue(&frame).len(), 1);
        }

        // Every other retention rule is unchanged.
        let mut slot = returning(vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        slot.alloc_stack_slot(StackSlot::new(8, 8));
        let mut guarded = returning(vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        guarded.stack_protector = StackProtectorMode::StackGuard;
        for func in [
            returning(vec![
                MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::Special(SpecialReg::SP),
                        MachOperand::Imm(16),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ]),
            returning(vec![
                MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::PReg(X19),
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ]),
            returning(vec![
                MachInst::new(
                    AArch64Opcode::AddRR,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X1),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::Bl,
                    vec![MachOperand::Symbol("callee".into())],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ]),
            slot,
            guarded,
        ] {
            assert!(unowned(&func).uses_frame_pointer, "{:?}", func.insts);
        }
    }

    #[test]
    fn zero_storage_keeps_slots_guards_dynamic_and_outgoing_storage() {
        let leaf = || make_func("leaf", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        for slot in [
            StackSlot::new(8, 8),
            StackSlot::new_dynamic(StackSlotSizeSource::Unknown, 16),
        ] {
            let mut func = leaf();
            func.alloc_stack_slot(slot);
            assert!(layout(&func).uses_frame_pointer);
        }
        let mut func = leaf();
        func.stack_protector = StackProtectorMode::StackGuard;
        assert!(layout(&func).uses_frame_pointer);
        let mut func = leaf();
        func.stack_protector_slot = Some(trust_cg_ir::StackSlotId(0));
        assert!(layout(&func).uses_frame_pointer);
        let frame = try_compute_frame_layout_with_leaf_policy(
            &leaf(),
            16,
            false,
            LeafFramePolicy::OmitZeroStorage,
        )
        .unwrap();
        assert!(frame.uses_frame_pointer);
    }

    /// A fixed zero-byte slot (what selection leaves after folding away every
    /// access to a private slot) reserves no storage, so it does not keep the
    /// frame. A slot that is addressed still does, whatever its size.
    #[test]
    fn zero_storage_omits_frame_for_fixed_zero_byte_slot_unless_addressed() {
        let mut func = make_func("folded", vec![MachInst::new(AArch64Opcode::Ret, vec![])]);
        func.alloc_stack_slot(StackSlot::new(0, 1));
        let frame = layout(&func);
        assert!(!frame.uses_frame_pointer);
        assert_eq!(frame.total_frame_size, 0);

        let mut func = make_func(
            "addressed",
            vec![
                MachInst::new(
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::StackSlot(trust_cg_ir::StackSlotId(0)),
                        MachOperand::Imm(0),
                    ],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        func.alloc_stack_slot(StackSlot::new(0, 1));
        assert!(layout(&func).uses_frame_pointer);
    }
}
