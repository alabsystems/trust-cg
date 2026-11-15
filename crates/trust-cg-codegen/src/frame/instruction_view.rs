// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Borrow the exact instruction domain used to calculate frame effects.
//! Arena compatibility queries deliberately retain detached instructions.
//! Production omission requires a closed, structurally validated code layout.

use super::*;

pub(super) struct FrameInstructions<'a> {
    function: &'a MachFunction,
    emitted: Option<Vec<bool>>,
}

impl<'a> FrameInstructions<'a> {
    pub(super) fn all(function: &'a MachFunction) -> Self {
        Self {
            function,
            emitted: None,
        }
    }

    pub(super) fn emitted(function: &'a MachFunction) -> Result<Self, crate::lower::LowerError> {
        // Validate entry/order, unique instruction ownership and all symbolic
        // CFG, jump-table and EH references before excluding any arena slot.
        // The immutable borrow keeps this view tied to the checked function.
        crate::pipeline::validate_aarch64_mach_function(function)
            .map_err(|error| crate::lower::LowerError::MalformedFunction(error.to_string()))?;
        let mut emitted = vec![false; function.insts.len()];
        for block in &function.block_order {
            for instruction in &function.block(*block).insts {
                emitted[instruction.0 as usize] = true;
            }
        }
        Ok(Self {
            function,
            emitted: Some(emitted),
        })
    }

    pub(super) fn function(&self) -> &'a MachFunction {
        self.function
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &'a MachInst> + '_ {
        self.function
            .insts
            .iter()
            .enumerate()
            .filter_map(|(index, instruction)| {
                self.emitted
                    .as_ref()
                    .is_none_or(|emitted| emitted[index])
                    .then_some(instruction)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::Signature;
    use trust_cg_ir::function::{JumpTableData, LandingPadEntry};
    use trust_cg_ir::regs::{D8, W19, X1, X2};

    fn fixture(effect: MachInst, live: bool) -> MachFunction {
        let mut function =
            MachFunction::new("frame_effects".into(), Signature::new(vec![], vec![]));
        if live {
            let outgoing_store = effect.opcode == AArch64Opcode::StrRI;
            let id = function.push_inst(effect);
            function.append_inst(BlockId(0), id);
            if outgoing_store {
                let call = function.push_inst(MachInst::new(
                    AArch64Opcode::Bl,
                    vec![MachOperand::Symbol("stack_callee".into())],
                ));
                function.append_inst(BlockId(0), call);
            }
        } else {
            let dead = function.create_block();
            let id = function.push_inst(effect);
            function.append_inst(dead, id);
            function.block_order.pop();
        }
        let ret = function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        function.append_inst(BlockId(0), ret);
        function
    }

    fn effect_cases() -> Vec<MachInst> {
        use AArch64Opcode::*;
        let reg = MachOperand::PReg;
        vec![
            MachInst::new(Bl, vec![MachOperand::Symbol("callee".into())]),
            MachInst::new(AddRR, vec![reg(X0), reg(X1), reg(X2)]),
            MachInst::new(MovR, vec![reg(X19), reg(X0)]),
            MachInst::new(MOVWrr, vec![reg(W19), reg(W0)]),
            MachInst::new(FmovFprFpr, vec![reg(D8), reg(D8)]),
            MachInst::new(Nop, vec![]).with_implicit_defs(&[X19]),
            MachInst::new(Nop, vec![]).with_implicit_uses(&[X29]),
            MachInst::new(StackAlloc, vec![reg(X0), reg(X1)]),
            MachInst::new(LdrRI, vec![reg(X0), MachOperand::IncomingArg(8)]),
            MachInst::new(StrRI, vec![reg(X0), reg(SP), MachOperand::Imm(64)]),
        ]
    }

    #[test]
    fn emitted_frame_ignores_only_unlinked_effects_and_preserves_arena_queries() {
        for effect in effect_cases() {
            let function = fixture(effect.clone(), false);
            let before = format!("{function:?}");
            let layout = try_compute_emitted_frame_layout(
                &function,
                false,
                LeafFramePolicy::OmitZeroStorage,
            )
            .unwrap();
            assert_eq!(layout.total_frame_size, 0, "{:?}", effect.opcode);
            assert!(layout.is_leaf && !layout.has_dynamic_alloc);
            assert!(layout.callee_saved_pairs.is_empty());
            let legacy = try_compute_frame_layout_with_leaf_policy(
                &function,
                compute_max_outgoing_arg_size(&function),
                false,
                LeafFramePolicy::OmitZeroStorage,
            )
            .unwrap();
            assert!(legacy.total_frame_size > 0, "{:?}", effect.opcode);
            assert_eq!(format!("{function:?}"), before);
            let live = fixture(effect.clone(), true);
            let live_layout =
                try_compute_emitted_frame_layout(&live, false, LeafFramePolicy::OmitZeroStorage)
                    .unwrap();
            assert!(live_layout.total_frame_size > 0, "{:?}", effect.opcode);
            if effect.opcode == AArch64Opcode::Bl {
                assert!(!live_layout.is_leaf);
            }
            if effect.opcode == AArch64Opcode::StackAlloc {
                assert!(live_layout.has_dynamic_alloc);
            }
            if effect.opcode == AArch64Opcode::StrRI {
                assert_eq!(live_layout.outgoing_arg_area_size, 80);
            }
        }
    }

    #[test]
    fn emitted_frame_retains_each_live_alu_owner_and_declared_storage() {
        use AArch64Opcode::*;
        for opcode in [AddRR, AddRI, AddRIShift12, SubRR, SubRI, LslRI] {
            let rhs = if matches!(opcode, AddRR | SubRR) {
                MachOperand::PReg(X2)
            } else {
                MachOperand::Imm(1)
            };
            let function = fixture(
                MachInst::new(
                    opcode,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(X1), rhs],
                ),
                true,
            );
            assert_eq!(
                try_compute_emitted_frame_layout(
                    &function,
                    false,
                    LeafFramePolicy::OmitZeroStorage
                )
                .unwrap()
                .total_frame_size,
                16
            );
        }
        let mut function = fixture(MachInst::new(Nop, vec![]), false);
        function.alloc_stack_slot(StackSlot::new(16, 16));
        let layout =
            try_compute_emitted_frame_layout(&function, false, LeafFramePolicy::OmitZeroStorage)
                .unwrap();
        assert!(layout.total_frame_size >= 32);
        assert!(layout.uses_frame_pointer);
    }

    #[test]
    fn emitted_frame_rejects_incomplete_cfg_instruction_and_eh_ownership() {
        for mutation in 0..11 {
            let mut function = fixture(MachInst::new(AArch64Opcode::Nop, vec![]), false);
            let ret = function.blocks[0].insts[0];
            match mutation {
                0 => function.block_order.clear(),
                1 => function.block_order.push(BlockId(0)),
                2 => function.block_order[0] = BlockId(9),
                3 => function.entry = BlockId(1),
                4 => function.blocks[0].insts[0] = InstId(99),
                5 => function.blocks[1].insts.push(ret),
                6 => function.blocks[0].succs.push(BlockId(1)),
                7 => {
                    let branch = function.push_inst(MachInst::new(
                        AArch64Opcode::B,
                        vec![MachOperand::Block(BlockId(1))],
                    ));
                    function.blocks[0].insts = vec![branch];
                }
                8 => function.jump_tables.push(JumpTableData {
                    min_val: 0,
                    targets: vec![BlockId(1)],
                }),
                9 => {
                    function.eh_metadata.personality = Some("__gxx_personality_v0".into());
                    function.eh_metadata.landing_pads.push(LandingPadEntry {
                        block: BlockId(1),
                        offset: 0,
                        catch_type_indices: vec![],
                        is_cleanup: true,
                    });
                }
                10 => function.blocks[0].preds.push(BlockId(0)),
                _ => unreachable!(),
            }
            let before = format!("{function:?}");
            assert!(
                matches!(
                    try_compute_emitted_frame_layout(
                        &function,
                        false,
                        LeafFramePolicy::OmitZeroStorage
                    ),
                    Err(crate::lower::LowerError::MalformedFunction(_))
                ),
                "mutation {mutation}"
            );
            assert_eq!(format!("{function:?}"), before);
        }
    }

    #[test]
    fn emitted_frame_keeps_calls_in_a_separately_laid_out_block() {
        let mut function = fixture(
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("callee".into())],
            ),
            false,
        );
        function.block_order.push(BlockId(1));
        let ret = function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        function.append_inst(BlockId(1), ret);
        let layout =
            try_compute_emitted_frame_layout(&function, false, LeafFramePolicy::OmitZeroStorage)
                .unwrap();
        assert!(!layout.is_leaf);
        assert!(layout.total_frame_size >= 16);
    }
}
