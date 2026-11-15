// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! OD-35 C: raw source/result replay over the return's backward slice.
//! Both sides start at ABI parameters. Source arithmetic uses widened wrapping
//! operations; machine arithmetic composes `aarch64_semantics` over the actual
//! allocated register file. Source comparisons use integer predicates, while
//! machine comparisons derive NZCV from subtraction and consume the actual
//! CSET/conditional-select condition and raw allocated arms. No affine result
//! or simplifier enters the query.
//! The checked/replayed frame is an outer prerequisite, not body evidence.
//! This owner admits bounded I32/I64 chains or one pure arithmetic diamond, or canonical B1
//! comparison returns, with copies, constants, add/sub, immediate shifts and
//! comparison-driven flat integer selects. Identity sources are refused.
//! Only live copies, CMP/CSET, conditional-select and conditional-branch rows can receive this
//! theorem's credit.

use std::collections::{HashMap, HashSet};

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::proof_database::ProofCategory;
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::{RawControl, SourceBoundFrame};
use trust_cg_ir::cc::OperandSize;
use trust_cg_ir::regs::SpecialReg;
use trust_cg_ir::{AArch64Opcode as M, InstId, MachOperand as O};
use trust_cg_lower::Type;
use trust_cg_lower::instructions::{IntCC, Opcode as L, Value};
use trust_cg_lower::isel::AArch64CC;

// Bound raw-tree expansion before cloning any potentially exponential operand.
// Exceeding this limit declines coverage; it never substitutes a normal form.
const MAX_NODES: usize = 4096;

#[path = "source_bound_body_control.rs"]
mod control;

#[path = "read_only_source.rs"]
pub(crate) mod read_only_source;

#[derive(Clone)]
struct Term {
    expr: E,
    nodes: usize,
}

impl Term {
    fn leaf(expr: E) -> Self {
        Self { expr, nodes: 1 }
    }

    fn unary(&self, extra: usize, build: impl FnOnce(E) -> E) -> Option<Self> {
        let nodes = self.nodes.checked_add(extra)?;
        (nodes <= MAX_NODES).then(|| Self {
            expr: build(self.expr.clone()),
            nodes,
        })
    }

    fn binary(&self, other: &Self, extra: usize, build: impl FnOnce(E, E) -> E) -> Option<Self> {
        let nodes = self.nodes.checked_add(other.nodes)?.checked_add(extra)?;
        (nodes <= MAX_NODES).then(|| Self {
            expr: build(self.expr.clone(), other.expr.clone()),
            nodes,
        })
    }

    fn ternary(
        &self,
        then_term: &Self,
        else_term: &Self,
        extra: usize,
        build: impl FnOnce(E, E, E) -> E,
    ) -> Option<Self> {
        let nodes = self
            .nodes
            .checked_add(then_term.nodes)?
            .checked_add(else_term.nodes)?
            .checked_add(extra)?;
        (nodes <= MAX_NODES).then(|| Self {
            expr: build(
                self.expr.clone(),
                then_term.expr.clone(),
                else_term.expr.clone(),
            ),
            nodes,
        })
    }
}

#[derive(Clone)]
struct Word {
    // Full X register state. Every W write zeroes the upper 32 bits.
    term: Term,
    slice: HashSet<InstId>,
}

#[derive(Clone)]
struct SourceValue {
    term: Term,
    boolean: bool,
}

// The dependency slice includes the exact latest CMP, not a comparison chosen
// from the source condition. Every modeled CMP replaces this state.
#[derive(Clone)]
struct ReachingFlags {
    flags: crate::nzcv::NzcvFlags,
    nodes: usize,
    slice: HashSet<InstId>,
}

impl ReachingFlags {
    fn cmp(mut lhs: Word, rhs: Word, bits: u32, id: InstId) -> Option<Self> {
        // Conservative tree bound for all four encode_cmp outputs together:
        // at most eight copies of either operand and 32 additional nodes.
        // Check before encode_cmp clones its operands into the flag formulas.
        let nodes = lhs
            .term
            .nodes
            .checked_add(rhs.term.nodes)?
            .checked_mul(8)?
            .checked_add(32)?;
        if nodes > MAX_NODES {
            return None;
        }
        lhs.slice.extend(rhs.slice);
        lhs.slice.insert(id);
        Some(Self {
            flags: crate::nzcv::encode_cmp(lhs.term.expr, rhs.term.expr, bits),
            nodes,
            slice: lhs.slice,
        })
    }

    fn cset(&self, cc: AArch64CC, bits: u32) -> Option<Word> {
        // ConditionHolds uses each needed flag at most once. Sixteen nodes
        // bound its Boolean glue, the 1-bit ITE and the destination extension.
        let nodes = self.nodes.checked_add(16)?;
        if nodes > MAX_NODES {
            return None;
        }
        Some(Word {
            term: Term {
                expr: crate::nzcv::encode_cset(cc, &self.flags).zero_ext(bits - 1),
                nodes,
            },
            slice: self.slice.clone(),
        })
    }

    fn select_nodes(&self, opcode: M, then_nodes: usize, else_nodes: usize) -> Option<usize> {
        let transform = match opcode {
            M::Csel => 0,
            M::Csinc | M::Csinv | M::Csneg => 2, // operator and width-sized constant
            _ => return None,
        };
        // Bound ConditionHolds glue and the ITE independently of either arm.
        // The flags' bound covers all flags once; every condition uses a
        // subset without duplicating one. Preflight before cloning any arm.
        let nodes = self
            .nodes
            .checked_add(then_nodes)?
            .checked_add(else_nodes)?
            .checked_add(16)?
            .checked_add(transform)?;
        (nodes <= MAX_NODES).then_some(nodes)
    }

    fn select(
        &self,
        opcode: M,
        cc: AArch64CC,
        bits: u32,
        mut left: Word,
        right: Word,
    ) -> Option<Word> {
        let nodes = self.select_nodes(opcode, left.term.nodes, right.term.nodes)?;
        left.slice.extend(right.slice);
        let right = match opcode {
            M::Csel => right.term.expr,
            M::Csinc => right.term.expr.bvadd(E::bv_const(1, bits)),
            M::Csinv => right.term.expr.bvxor(E::bv_const(
                if bits == 32 {
                    u32::MAX as u64
                } else {
                    u64::MAX
                },
                bits,
            )),
            M::Csneg => E::bv_const(0, bits).bvsub(right.term.expr),
            _ => return None,
        };
        left.term = Term {
            expr: E::ite(
                crate::nzcv::eval_condition(cc, &self.flags),
                left.term.expr,
                right,
            ),
            nodes,
        };
        left.slice.extend(self.slice.iter().copied());
        Some(left)
    }
}

#[derive(Clone)]
struct Registers([Option<Word>; 18]);

fn register(operand: &O) -> Option<(usize, u32)> {
    let O::PReg(reg) = operand else {
        return None;
    };
    match reg.encoding() {
        index @ 0..=17 => Some((usize::from(index), 64)),
        index @ 32..=49 => Some((usize::from(index - 32), 32)),
        _ => None,
    }
}

fn operand_bits(operand: &O) -> Option<u32> {
    match operand {
        O::Special(SpecialReg::XZR) => Some(64),
        O::Special(SpecialReg::WZR) => Some(32),
        _ => register(operand).map(|(_, bits)| bits),
    }
}

impl Registers {
    fn read_nodes(&self, operand: &O, bits: u32, typed_copy: bool) -> Option<usize> {
        match operand {
            O::Special(SpecialReg::XZR) if bits == 64 => return Some(1),
            O::Special(SpecialReg::WZR) if bits == 32 => return Some(1),
            _ => {}
        }
        let (index, encoded_bits) = register(operand)?;
        if !typed_copy && encoded_bits != bits {
            return None;
        }
        let nodes = self.0[index]
            .as_ref()?
            .term
            .nodes
            .checked_add(usize::from(bits == 32))?;
        (nodes <= MAX_NODES).then_some(nodes)
    }

    fn read(&self, operand: &O, bits: u32, typed_copy: bool) -> Option<Word> {
        self.read_nodes(operand, bits, typed_copy)?;
        match operand {
            O::Special(SpecialReg::XZR) if bits == 64 => {
                return Some(Word {
                    term: Term::leaf(E::bv_const(0, bits)),
                    slice: HashSet::new(),
                });
            }
            O::Special(SpecialReg::WZR) if bits == 32 => {
                return Some(Word {
                    term: Term::leaf(E::bv_const(0, bits)),
                    slice: HashSet::new(),
                });
            }
            _ => {}
        }
        let (index, encoded_bits) = register(operand)?;
        if !typed_copy && encoded_bits != bits {
            return None;
        }
        let mut word = self.0[index].as_ref()?.clone();
        if bits == 32 {
            word.term = word.term.unary(1, |e| e.extract(31, 0))?;
        }
        Some(word)
    }

    fn write(
        &mut self,
        dst: &O,
        bits: u32,
        typed_copy: bool,
        id: InstId,
        mut word: Word,
    ) -> Option<()> {
        let (index, encoded_bits) = register(dst)?;
        if !typed_copy && encoded_bits != bits {
            return None;
        }
        if bits == 32 {
            word.term = word.term.unary(1, |e| e.zero_ext(32))?;
        }
        word.slice.insert(id);
        self.0[index] = Some(word);
        Some(())
    }
}

pub(crate) struct SourceBoundBody<'owner, 'inputs> {
    frame: &'owner SourceBoundFrame<'inputs>,
    credited: HashSet<InstId>,
    obligation: ProofObligation,
}

impl<'owner, 'inputs> SourceBoundBody<'owner, 'inputs> {
    pub(crate) fn bind(frame: &'owner SourceBoundFrame<'inputs>) -> Option<Self> {
        let (obligation, credited) = raw_control_body(
            frame.source(),
            frame.machine(),
            frame.raw_control()?,
            frame.envelope_instructions(),
        )?;
        Some(Self {
            frame,
            credited,
            obligation,
        })
    }

    pub(crate) fn credits(&self, id: InstId) -> bool {
        self.credited.contains(&id)
    }
    pub(crate) fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }

    pub(crate) fn category(&self) -> ProofCategory {
        if self.frame.source().signature.returns == [Type::B1] {
            ProofCategory::Comparison
        } else {
            ProofCategory::Arithmetic
        }
    }
}

// This unbound model has no replay capability. Only bind can wrap it in an
// owner borrowing the exact checked frame. Tests can refute malformed raw
// dataflow here independently of the Rust frame gate's earlier refusal.
#[cfg(test)]
fn raw_body(
    source: &trust_cg_lower::Function,
    machine: &trust_cg_ir::MachFunction,
    chain: Vec<InstId>,
    envelope: [InstId; 3],
) -> Option<(ProofObligation, HashSet<InstId>)> {
    raw_control_body(source, machine, RawControl::Chain(chain), envelope)
}

fn raw_control_body(
    source: &trust_cg_lower::Function,
    machine: &trust_cg_ir::MachFunction,
    control: RawControl,
    envelope: [InstId; 3],
) -> Option<(ProofObligation, HashSet<InstId>)> {
    let source_view = crate::source_bound_frame::raw_source_view(source)?;
    // Normal forms can only refuse an identity; they supply neither term.
    if crate::aarch64_affine_lowering::affine_return_is_parameter(&source_view)? {
        return None;
    }
    let [return_type] = source.signature.returns.as_slice() else {
        return None;
    };
    let comparison = return_type == &Type::B1;
    let block = source_view.blocks.get(&source_view.entry_block)?;
    let integer_type = if comparison {
        source
            .signature
            .params
            .first()
            .or_else(|| {
                block
                    .instructions
                    .iter()
                    .find_map(|inst| match &inst.opcode {
                        L::Iconst {
                            ty: ty @ (Type::I32 | Type::I64),
                            ..
                        } => Some(ty),
                        _ => None,
                    })
            })
            // Match the existing frame's width-neutral Boolean-only domain.
            .unwrap_or(&Type::I64)
    } else {
        return_type
    };
    let bits = match integer_type {
        Type::I32 => 32,
        Type::I64 => 64,
        _ => return None,
    };
    if source.signature.params.len() > 8
        || source.signature.params.iter().any(|ty| ty != integer_type)
    {
        return None;
    }
    if block.instructions.len() > 256 {
        return None;
    }
    let mut inputs = Vec::new();
    let mut values: HashMap<Value, SourceValue> = HashMap::new();
    let mut registers = Registers(std::array::from_fn(|_| None));
    for (i, register) in registers.0[..source.signature.params.len()]
        .iter_mut()
        .enumerate()
    {
        let name = format!("abi_x{i}");
        inputs.push((name.clone(), 64));
        let input = Term::leaf(E::var(&name, 64));
        values.insert(
            Value(i as u32),
            SourceValue {
                term: if bits == 32 {
                    input.unary(1, |e| e.extract(31, 0))?
                } else {
                    input.clone()
                },
                boolean: false,
            },
        );
        *register = Some(Word {
            term: input,
            slice: HashSet::new(),
        });
    }

    let source_result =
        control::source_result(source, &source_view, integer_type, bits, comparison, values)?;
    let (result, all_credited) =
        control::machine_result(machine, control, envelope, registers, bits, comparison)?;
    let credited = all_credited
        .intersection(&result.slice)
        .copied()
        .collect::<HashSet<_>>();
    if credited.is_empty() {
        return None;
    }
    let obligation = ProofObligation {
        name: format!(
            "Source-bound AArch64 raw body (Rust frame/control binding; replayed return dataflow): i{bits}{}",
            if comparison { " -> canonical b1" } else { "" }
        ),
        trust_ir_expr: source_result.expr,
        aarch64_expr: result.term.expr,
        inputs,
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    if obligation.is_degenerate() {
        return None;
    }
    Some((obligation, credited))
}

fn source_run(
    instructions: &[trust_cg_lower::instructions::Instruction],
    integer_type: &Type,
    bits: u32,
    comparison: bool,
    values: &mut HashMap<Value, SourceValue>,
) -> Option<Option<Term>> {
    let mut source_result = None;
    for inst in instructions {
        if source_result.is_some() {
            return None;
        }
        let integer = |value: &Value| {
            let value = values.get(value)?;
            (!value.boolean).then_some(&value.term)
        };
        let value = match (&inst.opcode, inst.args.as_slice(), inst.results.as_slice()) {
            (L::Iconst { ty, imm }, [], [_]) if ty == integer_type => SourceValue {
                term: Term::leaf(E::bv_const(
                    if bits == 32 {
                        *imm as u32 as u64
                    } else {
                        *imm as u64
                    },
                    bits,
                )),
                boolean: false,
            },
            (L::Iconst { ty: Type::B1, imm }, [], [_]) if matches!(*imm, 0 | 1) => SourceValue {
                term: Term::leaf(E::bv_const(*imm as u64, 1)),
                boolean: true,
            },
            (L::Copy, [arg], [_]) => values.get(arg)?.clone(),
            (L::Iadd | L::Isub, [a, b], [_]) => SourceValue {
                term: raw_arithmetic(&inst.opcode, bits, integer(a)?, integer(b)?)?,
                boolean: false,
            },
            (L::Icmp { cond }, [a, b], [_]) => SourceValue {
                // This source predicate does not inspect machine CC or NZCV.
                term: raw_compare(cond, integer(a)?, integer(b)?)?,
                boolean: true,
            },
            (
                L::Select {
                    cond: cond @ (IntCC::Equal | IntCC::NotEqual),
                },
                [selector, a, b],
                [_],
            ) => {
                let selector = values.get(selector)?;
                if !selector.boolean {
                    return None;
                }
                SourceValue {
                    // Select observes the actual canonical source B1, not
                    // the allocated NZCV predicate. Eq selects on zero and
                    // Ne on nonzero; its two arms stay raw integer terms.
                    term: raw_select(
                        &selector.term,
                        integer(a)?,
                        integer(b)?,
                        *cond == IntCC::Equal,
                    )?,
                    boolean: false,
                }
            }
            (L::Return, [arg], []) => {
                let value = values.get(arg)?;
                if value.boolean != comparison {
                    return None;
                }
                source_result = Some(if comparison {
                    // A canonical B1 result must occupy the complete X0 ABI
                    // carrier as 0 or 1, not just agree in its low bit.
                    value.term.unary(1, |e| e.zero_ext(63))?
                } else {
                    value.term.clone()
                });
                continue;
            }
            _ => return None,
        };
        if values.insert(inst.results[0], value).is_some() {
            return None;
        }
    }

    Some(source_result)
}

// Shared raw scalar terms: the read-only source binder uses the same bounded
// semantics as the existing body owner, not another arithmetic interpreter.
fn raw_arithmetic(opcode: &L, bits: u32, a: &Term, b: &Term) -> Option<Term> {
    matches!(opcode, L::Iadd | L::Isub).then_some(())?;
    a.binary(b, 4, |a, b| {
        let a = a.zero_ext(1);
        let b = b.zero_ext(1);
        let wide = if *opcode == L::Isub {
            a.bvsub(b)
        } else {
            a.bvadd(b)
        };
        wide.extract(bits - 1, 0)
    })
}

fn raw_compare(condition: &IntCC, a: &Term, b: &Term) -> Option<Term> {
    a.binary(b, 5, |a, b| {
        crate::trust_ir_semantics::encode_trust_ir_icmp(condition, Type::I64, a, b)
    })
}

fn raw_select(condition: &Term, a: &Term, b: &Term, invert: bool) -> Option<Term> {
    condition.ternary(a, b, 4, |condition, a, b| {
        let zero = condition.eq_expr(E::bv_const(0, 1));
        E::ite(if invert { zero } else { zero.not_expr() }, a, b)
    })
}

fn machine_run(
    machine: &trust_cg_ir::MachFunction,
    chain: &[InstId],
    envelope: [InstId; 3],
    registers: &mut Registers,
    flags: &mut Option<ReachingFlags>,
    all_credited: &mut HashSet<InstId>,
) -> Option<bool> {
    let mut returned = false;
    for &id in chain {
        if returned {
            return None;
        }
        if envelope.contains(&id) {
            continue;
        }
        let inst = machine.insts.get(id.0 as usize)?;
        if inst.opcode == M::Nop {
            continue;
        } // Inertness already checked by the frame owner.
        if inst.opcode == M::Ret {
            returned = true;
            continue;
        }
        if matches!(inst.opcode, M::CmpRR | M::CmpRI) {
            let [lhs, rhs] = inst.operands.as_slice() else {
                return None;
            };
            let width = operand_bits(lhs)?;
            let left = registers.read(lhs, width, false)?;
            let right = if inst.opcode == M::CmpRR {
                registers.read(rhs, width, false)?
            } else {
                // CMP immediate encodes register 31 as SP, not ZR.
                register(lhs)?;
                let O::Imm(imm @ 0..=4095) = rhs else {
                    return None;
                };
                Word {
                    term: Term::leaf(E::bv_const(*imm as u64, width)),
                    slice: HashSet::new(),
                }
            };
            *flags = Some(ReachingFlags::cmp(left, right, width, id)?);
            all_credited.insert(id);
            continue;
        }
        let dst = inst.operands.first()?;
        let bits = match inst.opcode {
            M::MOVWrr => 32,
            M::MOVXrr => 64,
            _ => register(dst)?.1,
        };
        let size = if bits == 32 {
            OperandSize::S32
        } else {
            OperandSize::S64
        };
        let (word, typed_copy) = match (inst.opcode, inst.operands.as_slice()) {
            (M::MovR | M::MOVWrr | M::MOVXrr, [_, src]) => {
                let typed = inst.opcode != M::MovR;
                let mut word = registers.read(src, bits, typed)?;
                word.term = word
                    .term
                    .unary(0, |e| crate::aarch64_semantics::encode_mov_rr(size, e))?;
                all_credited.insert(id);
                (word, typed)
            }
            (M::Movz | M::Movn, [_, O::Imm(imm)]) => (constant(inst.opcode, bits, *imm, 0)?, false),
            (M::Movz | M::Movn, [_, O::Imm(imm), O::Imm(shift)]) => {
                (constant(inst.opcode, bits, *imm, *shift)?, false)
            }
            (M::AddRR | M::SubRR, [_, a, b]) => {
                let mut left = registers.read(a, bits, false)?;
                let right = registers.read(b, bits, false)?;
                left.term = left.term.binary(&right.term, 1, |a, b| {
                    if inst.opcode == M::SubRR {
                        crate::aarch64_semantics::encode_sub_rr(size, a, b)
                    } else {
                        crate::aarch64_semantics::encode_add_rr(size, a, b)
                    }
                })?;
                left.slice.extend(right.slice);
                (left, false)
            }
            (M::AddRI | M::SubRI | M::AddRIShift12, [_, a, O::Imm(imm @ 0..=4095)]) => {
                let mut word = registers.read(a, bits, false)?;
                let imm = (*imm as u64)
                    << if inst.opcode == M::AddRIShift12 {
                        12
                    } else {
                        0
                    };
                word.term = word
                    .term
                    .binary(&Term::leaf(E::bv_const(imm, bits)), 1, |a, b| {
                        if inst.opcode == M::SubRI {
                            crate::aarch64_semantics::encode_sub_rr(size, a, b)
                        } else {
                            crate::aarch64_semantics::encode_add_rr(size, a, b)
                        }
                    })?;
                (word, false)
            }
            (M::LslRI, [_, a, O::Imm(shift)]) if (0..i64::from(bits)).contains(shift) => {
                let mut word = registers.read(a, bits, false)?;
                word.term = word.term.binary(
                    &Term::leaf(E::bv_const(*shift as u64, bits)),
                    1,
                    |a, b| crate::aarch64_semantics::encode_lsl_rr(size, a, b),
                )?;
                (word, false)
            }
            (M::CSet, [_, O::Imm(cc)]) => {
                let cc = crate::aarch64_value_decode_proofs::cset_condition_from_encoding(*cc)?;
                let word = flags.as_ref()?.cset(cc, bits)?;
                all_credited.insert(id);
                (word, false)
            }
            (M::Csel | M::Csinc | M::Csinv | M::Csneg, [_, a, b, O::Imm(cc)]) => {
                let cc = crate::aarch64_value_decode_proofs::cset_condition_from_encoding(*cc)?;
                let flags = flags.as_ref()?;
                // Check the entire selection tree before register reads clone
                // either potentially large arm or ConditionHolds clones NZCV.
                flags.select_nodes(
                    inst.opcode,
                    registers.read_nodes(a, bits, false)?,
                    registers.read_nodes(b, bits, false)?,
                )?;
                let left = registers.read(a, bits, false)?;
                let right = registers.read(b, bits, false)?;
                let word = flags.select(inst.opcode, cc, bits, left, right)?;
                all_credited.insert(id);
                (word, false)
            }
            // MOVK, other flag writers and unsupported predicate operations
            // refuse; none can silently preserve an earlier CMP's flags.
            _ => return None,
        };
        registers.write(dst, bits, typed_copy, id, word)?;
    }
    Some(returned)
}

fn constant(opcode: M, bits: u32, imm: i64, shift: i64) -> Option<Word> {
    if !(0..=65535).contains(&imm) || !(0..i64::from(bits)).contains(&shift) || shift % 16 != 0 {
        return None;
    }
    let shifted = E::bv_const(imm as u64, bits).bvshl(E::bv_const(shift as u64, bits));
    let expr = if opcode == M::Movn {
        shifted.bvxor(E::bv_const(
            if bits == 32 {
                u32::MAX as u64
            } else {
                u64::MAX
            },
            bits,
        ))
    } else {
        shifted
    };
    Some(Word {
        term: Term {
            expr,
            nodes: if opcode == M::Movn { 5 } else { 3 },
        },
        slice: HashSet::new(),
    })
}

#[cfg(test)]
#[path = "source_bound_body_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "source_bound_body_predicate_tests.rs"]
mod predicate_tests;

#[cfg(test)]
#[path = "source_bound_body_select_tests.rs"]
mod select_tests;

#[cfg(test)]
#[path = "source_bound_body_bool_tests.rs"]
mod bool_tests;

#[cfg(test)]
#[path = "source_bound_body_diamond_tests.rs"]
mod diamond_tests;
