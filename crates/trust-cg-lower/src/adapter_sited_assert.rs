// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! IR §19.1 panic delivery. This is object lowering, not Rust-source fidelity
//! or a Core/JIT execution authorization. The producer owns entry and location
//! identity; the existing complete validator and canonical call ABI check it.

use super::*;
use trust_ir::{AssertKind, PanicLocation, PanicSite};

impl TrustIrAdapter<'_> {
    fn panic_delivery_error(reason: impl Into<String>) -> AdapterError {
        AdapterError::UnsupportedInstruction(format!("[TCG-PANIC-DELIVERY] {}", reason.into()))
    }

    fn panic_entry_signature(
        &self,
        kind: AssertKind,
        site: PanicSite,
    ) -> Result<(String, Ty, usize), AdapterError> {
        if kind.is_unspecified() {
            return Err(Self::panic_delivery_error("unspecified panic kind"));
        }
        let module = self.module.ok_or(AdapterError::ModuleNotSet)?;
        let entry = self
            .functions
            .unique(module, site.entry)
            .ok_or_else(|| Self::panic_delivery_error("unresolved or duplicate entry"))?;
        let signature = module
            .func_types
            .get(entry.ty.index() as usize)
            .ok_or_else(|| Self::panic_delivery_error("missing entry signature"))?;
        let operands = kind.operand_count();
        if signature.is_vararg
            || !signature.returns.is_empty()
            || signature.params.len() != operands + 1
            || signature.params[..operands]
                .iter()
                .any(|ty| *ty != Ty::Usize)
            || entry.attrs.params.iter().any(|p| p.byval || p.sret)
        {
            return Err(Self::panic_delivery_error(
                "entry is not operands ++ location -> ()",
            ));
        }
        let location_ty = signature.params[operands].clone();
        if !matches!(location_ty, Ty::Ptr | Ty::Ref(_) | Ty::PtrConst(_)) {
            return Err(Self::panic_delivery_error(
                "unsupported caller-location type",
            ));
        }
        // A named intrinsic must not replace the mandatory runtime call. A
        // local definition retains its own body under the existing rule.
        let name = self
            .functions
            .name(site.entry)
            .unwrap_or(&entry.name)
            .to_owned();
        if !is_module_local_function_definition(entry)
            && !matches!(classify_named_call(&name), NamedCallSemantics::Ordinary)
        {
            return Err(Self::panic_delivery_error(
                "entry would select an intrinsic replacement",
            ));
        }
        Ok((name, location_ty, operands))
    }

    /// Build only the failing-path data/call. Passing reads only the condition.
    /// The location is actual module storage or an existing SSA value, never a
    /// host address, diagnostic span, fabricated payload or guessed symbol.
    fn panic_delivery_call(
        &mut self,
        kind: AssertKind,
        site: PanicSite,
        source_block: BlockId,
        index: usize,
    ) -> Result<Vec<Instruction>, AdapterError> {
        let (name, location_ty, operands) = self.panic_entry_signature(kind, site)?;
        let module = self.module.ok_or(AdapterError::ModuleNotSet)?;
        let mut instructions = Vec::new();
        let location = match site.location {
            PanicLocation::Value(value) => value,
            PanicLocation::Global(global) => {
                let definition = module
                    .globals
                    .get(global.index() as usize)
                    .ok_or_else(|| Self::panic_delivery_error("missing location global"))?;
                if definition.mutable || definition.tls.is_some() {
                    return Err(Self::panic_delivery_error(
                        "location is mutable or thread-local",
                    ));
                }
                let value = self.fresh_synthetic_value_id()?;
                self.value_ty_map.insert(value, location_ty);
                instructions.extend(self.translate_global_addr(global, &[value])?);
                value
            }
        };
        let mut args = Vec::with_capacity(operands + 1);
        if let Some(payload) = kind.operands() {
            args.extend(payload);
        }
        args.push(location);
        // Panic delivery is effectful even if an erroneous purity annotation
        // or a structurally pure entry body would classify an ordinary call.
        Rc::make_mut(&mut self.pure_func_ids).remove(&site.entry);
        Rc::make_mut(&mut self.libm_pure_func_ids).remove(&site.entry);
        self.pure_callees.remove(&name);
        self.libm_pure_callees.remove(&name);
        let call = InstrNode::new(Inst::Call {
            callee: site.entry,
            args,
        });
        let lowered = self.translate_instruction(&call, source_block, index)?;
        if lowered.len() != 1 || !matches!(lowered[0].opcode, Opcode::Call { .. }) {
            return Err(Self::panic_delivery_error(
                "entry did not lower to one canonical direct call",
            ));
        }
        instructions.extend(lowered);
        Ok(instructions)
    }

    pub(super) fn translate_sited_assert(
        &mut self,
        cond: ValueId,
        kind: AssertKind,
        site: PanicSite,
        source_block: BlockId,
        index: usize,
    ) -> Result<Vec<Instruction>, AdapterError> {
        self.validate_bool_condition("Inst::Assert", cond)?;
        let mut failure = self.panic_delivery_call(kind, site, source_block, index)?;
        // A malformed/foreign entry that returns cannot resume the success path.
        failure.push(Instruction {
            opcode: Opcode::Trap,
            args: vec![],
            results: vec![],
        });
        let fail = self.fresh_block();
        let continuation = self.fresh_block();
        self.pending_block_split = Some(PendingBlockSplit {
            blocks: vec![(
                fail,
                BasicBlock {
                    instructions: failure,
                    ..Default::default()
                },
            )],
            continuation,
        });
        Ok(vec![Instruction {
            opcode: Opcode::Brif {
                cond: self.map_value(cond),
                then_dest: continuation,
                else_dest: fail,
            },
            args: vec![self.map_value(cond)],
            results: vec![],
        }])
    }

    // The nine operands are the invoke's own shape — condition, kind, site,
    // both edges with the normal edge's arguments, and the source
    // coordinates — not a signature that grew. Grouping them would move the
    // call sites of in-flight work for nothing. Red on `origin/main`
    // (4107645c3) under the workspace's deny-warnings lint gate; allowed here
    // so the gate can pass, to be removed if the signature is restructured.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn translate_sited_assert_invoke(
        &mut self,
        cond: ValueId,
        kind: AssertKind,
        site: PanicSite,
        normal: BlockId,
        normal_args: &[ValueId],
        unwind: BlockId,
        source_block: BlockId,
        index: usize,
    ) -> Result<Vec<Instruction>, AdapterError> {
        self.validate_bool_condition("Inst::AssertInvoke", cond)?;
        let mut failure = self.panic_delivery_call(kind, site, source_block, index)?;
        let call = failure
            .pop()
            .ok_or_else(|| Self::panic_delivery_error("missing failure call"))?;
        let Opcode::Call { name, binding } = call.opcode else {
            return Err(Self::panic_delivery_error("non-call failure edge"));
        };
        let fail = self.fresh_block();
        let unexpected_return = self.fresh_block();
        let unwind = self.map_block(unwind);
        if self.eh_info.personality.is_none() {
            self.eh_info.personality = Some(self.selected_eh_personality()?);
        }
        self.eh_info.call_sites.push(crate::function::EhCallSite {
            call_block: fail,
            landing_pad_block: unwind,
        });
        failure.push(Instruction {
            opcode: Opcode::Invoke {
                binding,
                name,
                normal_dest: unexpected_return,
                unwind_dest: unwind,
            },
            args: call.args,
            results: call.results,
        });
        self.panic_extra_block(fail, failure);
        self.panic_extra_block(
            unexpected_return,
            vec![Instruction {
                opcode: Opcode::Trap,
                args: vec![],
                results: vec![],
            }],
        );
        let mut copies = self.resolve_block_args(normal, normal_args)?;
        let normal = self.map_block(normal);
        let pass = if copies.is_empty() {
            normal
        } else {
            let edge = self.fresh_block();
            copies.push(Instruction {
                opcode: Opcode::Jump { dest: normal },
                args: vec![],
                results: vec![],
            });
            self.panic_extra_block(edge, copies);
            edge
        };
        Ok(vec![Instruction {
            opcode: Opcode::Brif {
                cond: self.map_value(cond),
                then_dest: pass,
                else_dest: fail,
            },
            args: vec![self.map_value(cond)],
            results: vec![],
        }])
    }

    fn panic_extra_block(&mut self, block: Block, instructions: Vec<Instruction>) {
        self.pending_extra_block_origins.insert(
            block,
            vec![self.current_trust_ir_origin; instructions.len()],
        );
        self.pending_extra_blocks.push((
            block,
            BasicBlock {
                source_locs: vec![self.current_source_loc; instructions.len()],
                instructions,
                ..Default::default()
            },
        ));
    }
}
