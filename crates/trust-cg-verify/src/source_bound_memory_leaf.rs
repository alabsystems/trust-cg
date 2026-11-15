// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A frameless straight-line AArch64 leaf whose loads and stores are bound,
//! access by access, to the LIR `Load`/`Store` instructions they implement.
//!
//! The source-bound frame owner ([`super::source_bound_frame`]) checks a
//! complete body inside the sixteen-byte FP/LR envelope, and its affine domain
//! has no memory. A proof-grade compile omits that envelope around a leaf
//! whose body loads or stores (`frame::zero_storage`), so such a leaf is
//! frameless. This checker binds that body instead: it interprets the LIR
//! source and the allocated machine body independently and requires them to
//! perform the SAME sequence of memory accesses (lock-step), then the same
//! returned value.
//!
//! # The interpretation
//!
//! Values are linear forms modulo 2^64 over symbols: each incoming argument
//! register's whole 64-bit content (a narrow source argument is its low bits),
//! and one symbol per load, named by the load's position in the access trace
//! and holding the zero-extended loaded value. A machine register holds
//! `zext_b(low_b(form))` for `b` in {8, 16, 32, 64}. Two values are equal when
//! their forms agree coefficient by coefficient modulo the compared width: a
//! sufficient condition for equality on every input, never a sample.
//!
//! Event `k` of each side is a load or a store with an address form, a width
//! and (stores) the stored value's low bits. The `k`-th machine access must be
//! the `k`-th source access: same direction, same width, the machine base
//! register's form plus the instruction's offset equal to the source pointer's
//! form, and (stores) the stored low bits equal. Both programs are straight-line
//! and read memory only through these accesses, so by induction over the trace
//! both start every access from the same memory, a matched load reads the same
//! bytes on both sides (one symbol serves both), and both leave the same
//! memory. The returned register must then hold the source's returned value.
//! The machine side of each access is [`memory_access`] of the instruction,
//! the operand reading the word-bound memory-effect decomposition
//! ([`crate::aarch64_memory_effect`]) proves the emitted word performs.
//!
//! # Domain
//!
//! Source: one block with at most 256 instructions, at most eight integer
//! arguments, no stack slot, EH, stack protector or aggregate ABI metadata;
//! `iconst` (8 to 64 bits),
//! `copy`, 64-bit `iadd`/`isub`, the byte-stride address `ArrayGep { elem_ty:
//! I8 }` of two 64-bit values (their sum), `uextend` of an exactly
//! zero-extended value,
//! `load`/`store` of 8, 16, 32 or 64 bits, and a return of nothing or of one
//! integer (an 8- or 16-bit return as the explicit 32-bit extension the
//! adapter returns, compared in full). Machine: an allocated chain (no FP/LR envelope, no SP,
//! FP or LR operand) of admitted scalar `LDR`/`STR{,B,H}` immediates, 64-bit
//! `ADD`/`SUB` immediates, `MOVZ`, `MOV` (`MOVXrr`/`MOVWrr`), `UXTB`/`UXTH`,
//! inert NOPs and a final `RET`, writing only X0 to X17.
//!
//! # What it is not
//!
//! An in-process, exact Rust check, the same standing as the affine checker the
//! frame owner runs: no certificate, and no claim about any instruction other
//! than the accesses it binds. It NEVER rejects a function. A lock-step trace
//! cannot tell a legal reordering of independent accesses from a miscompile,
//! so every disagreement withholds the binding with a named
//! [`MemoryLeafRefusal`] and the rows keep their ordinary lanes.
//! Assumptions A1 (little-endian data), A2 (no alignment fault), A3 (no
//! concurrent writer) and A5 (Normal memory) are the memory-effect module's;
//! they hold for both sides alike.

use std::collections::{BTreeMap, HashMap};

use trust_cg_ir::function::StackProtectorMode;
use trust_cg_ir::regs::X30;
use trust_cg_ir::{AArch64Opcode as M, InstId, LoweringProvenance, MachFunction, MachInst};
use trust_cg_ir::{MachOperand as O, SpecialReg};
use trust_cg_lower::Function;
use trust_cg_lower::Type;
use trust_cg_lower::instructions::{Opcode as L, Value};

use crate::aarch64_memory_effect::memory_access;
use crate::aarch64_memory_source_binding::ContractAccess;

/// Why [`source_bound_memory_leaf`] bound nothing. Never a function rejection:
/// the rows of an unbound leaf keep their ordinary lanes.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MemoryLeafRefusal {
    /// The LIR source is outside the checked domain.
    #[error("LIR source is outside the memory-leaf domain: {0}")]
    Source(String),
    /// The machine body is outside the checked domain.
    #[error("machine body is outside the memory-leaf domain: {0}")]
    Machine(String),
    /// The `position`-th accesses of the two traces disagree.
    #[error("memory access {position} disagrees with the source's: {what}")]
    Trace { position: usize, what: String },
    /// The traces have different lengths.
    #[error("the machine performs {machine} memory accesses, the source {expected}")]
    TraceLength { machine: usize, expected: usize },
    /// The returned register does not hold the source's returned value.
    #[error("the returned register does not hold the source's returned value")]
    Return,
    /// A machine access's TV-1 stamp names another source instruction than
    /// the one its trace position matches.
    #[error(
        "memory access {position} is stamped from {stamped}, not from the source access it \
         matches (lir{block}.{index})"
    )]
    Stamp {
        position: usize,
        stamped: String,
        block: u32,
        index: usize,
    },
}

/// One machine access the checker bound to its source access.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundLeafAccess {
    /// The machine instruction.
    pub instruction: InstId,
    /// The LIR instruction's index in the source's only block.
    pub source_index: usize,
    /// Position in the access trace.
    pub position: usize,
    /// The access the source names, with the base and data registers the
    /// checker found holding the source pointer and value.
    pub contract: ContractAccess,
}

/// A checked frameless leaf. No public constructor: only
/// [`source_bound_memory_leaf`] builds one, borrowing its exact inputs.
#[derive(Debug)]
pub struct SourceBoundMemoryLeaf<'a> {
    source: &'a Function,
    machine: &'a MachFunction,
    accesses: Vec<BoundLeafAccess>,
}

impl<'a> SourceBoundMemoryLeaf<'a> {
    pub fn source(&self) -> &'a Function {
        self.source
    }

    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }

    /// Every bound access, in trace order.
    pub fn accesses(&self) -> &[BoundLeafAccess] {
        &self.accesses
    }

    /// The bound access `id` is, if any.
    pub fn access(&self, id: InstId) -> Option<&BoundLeafAccess> {
        self.accesses.iter().find(|access| access.instruction == id)
    }
}

// ---------------------------------------------------------------------------
// Linear forms
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Sym {
    /// Argument register `i`'s whole incoming 64-bit content.
    Argument(u8),
    /// The value of the load at trace position `k`, zero-extended.
    Loaded(usize),
}

/// `sum(coefficient * symbol) + constant`, modulo 2^64.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Lin {
    terms: BTreeMap<Sym, u64>,
    constant: u64,
}

fn mask(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

impl Lin {
    fn constant(value: u64) -> Self {
        Self {
            terms: BTreeMap::new(),
            constant: value,
        }
    }

    fn symbol(sym: Sym) -> Self {
        Self {
            terms: BTreeMap::from([(sym, 1)]),
            constant: 0,
        }
    }

    fn combine(&self, other: &Self, subtract: bool) -> Self {
        let mut out = self.clone();
        for (sym, coefficient) in &other.terms {
            let entry = out.terms.entry(*sym).or_insert(0);
            *entry = if subtract {
                entry.wrapping_sub(*coefficient)
            } else {
                entry.wrapping_add(*coefficient)
            };
        }
        out.constant = if subtract {
            out.constant.wrapping_sub(other.constant)
        } else {
            out.constant.wrapping_add(other.constant)
        };
        out.reduced(64)
    }

    fn plus(&self, value: u64) -> Self {
        let mut out = self.clone();
        out.constant = out.constant.wrapping_add(value);
        out
    }

    /// Every coefficient and the constant modulo 2^`bits`, zeros dropped.
    fn reduced(&self, bits: u32) -> Self {
        let m = mask(bits);
        Self {
            terms: self
                .terms
                .iter()
                .filter(|(_, coefficient)| **coefficient & m != 0)
                .map(|(sym, coefficient)| (*sym, coefficient & m))
                .collect(),
            constant: self.constant & m,
        }
    }

    /// Equal modulo 2^`bits` for every value of every symbol (sufficient).
    fn agrees(&self, other: &Self, bits: u32) -> bool {
        self.reduced(bits) == other.reduced(bits)
    }

    fn as_constant(&self) -> Option<u64> {
        self.terms.is_empty().then_some(self.constant)
    }

    /// Whether `zext_bits(low_bits(self)) == self` for every input: a constant
    /// below 2^bits, or a lone load symbol at most `bits` wide.
    fn exact_within(&self, bits: u32, widths: &[u32]) -> bool {
        if bits >= 64 {
            return true;
        }
        if let Some(value) = self.as_constant() {
            return value <= mask(bits);
        }
        matches!(
            (self.terms.iter().next(), self.terms.len(), self.constant),
            (Some((Sym::Loaded(k), 1)), 1, 0) if widths[*k] <= bits
        )
    }
}

/// A machine register's content: `zext_bits(low_bits(lin))`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RegValue {
    lin: Lin,
    bits: u32,
}

impl RegValue {
    fn full(lin: Lin) -> Self {
        Self { lin, bits: 64 }
    }

    /// `zext_bits(low_bits(self))`, normalized to a full form when exact.
    fn narrowed(&self, bits: u32, widths: &[u32]) -> Self {
        let bits = bits.min(self.bits);
        if self.lin.exact_within(bits, widths) {
            return Self::full(self.lin.clone());
        }
        if let Some(value) = self.lin.as_constant() {
            return Self::full(Lin::constant(value & mask(bits)));
        }
        Self {
            lin: self.lin.reduced(bits),
            bits,
        }
    }

    /// Whether the low `width` bits equal those of `value` (sufficient).
    fn low_bits_equal(&self, value: &SourceValue, width: u32) -> bool {
        width <= self.bits && width <= value.bits && self.lin.agrees(&value.lin, width)
    }
}

/// A source value of `bits` bits: the low `bits` bits of `lin`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SourceValue {
    lin: Lin,
    bits: u32,
}

fn type_bits(ty: &Type) -> Option<u32> {
    match ty {
        Type::I8 => Some(8),
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        _ => None,
    }
}

fn bits_type(bits: u32) -> Type {
    match bits {
        8 => Type::I8,
        16 => Type::I16,
        32 => Type::I32,
        _ => Type::I64,
    }
}

// ---------------------------------------------------------------------------
// The source
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct SourceEvent {
    index: usize,
    load: bool,
    address: Lin,
    bytes: u32,
    /// The stored value (stores only).
    stored: Option<SourceValue>,
}

struct SourceTrace {
    events: Vec<SourceEvent>,
    widths: Vec<u32>,
    returned: Option<SourceValue>,
}

// The same instruction bound as the standing whole-body source and allocated
// machine profiles. This limits only the optional leaf binding, not compilation.
const MAX_SOURCE_INSTRUCTIONS: usize = 256;
const MAX_SOURCE_ARGUMENTS: usize = 8;

/// Necessary cardinality conditions, before allocating linear forms, the SSA
/// map or the access trace. Inspect only collections this checker traverses.
/// Each admitted instruction has at most two operands and one result; every
/// accepted hint names an argument or a distinct instruction result.
fn source_cardinality_preflight(
    source: &Function,
    block: &trust_cg_lower::function::BasicBlock,
) -> Result<(), MemoryLeafRefusal> {
    let refuse = |why: &str| MemoryLeafRefusal::Source(why.to_owned());
    if block.instructions.len() > MAX_SOURCE_INSTRUCTIONS {
        return Err(refuse("more than 256 source instructions"));
    }
    if block.params.len() > MAX_SOURCE_ARGUMENTS {
        return Err(refuse("more than eight entry parameters"));
    }
    let mut results = 0;
    for inst in &block.instructions {
        if inst.args.len() > 2 {
            return Err(refuse("an instruction exceeds two operands"));
        }
        if inst.results.len() > 1 {
            return Err(refuse("an instruction exceeds one result"));
        }
        // Both factors are already bounded above: at most 256 instructions,
        // each with at most one result. No operand/result vector is traversed.
        results += inst.results.len();
    }
    if source.value_types.len() > source.signature.params.len() + results {
        return Err(refuse(
            "more type hints than arguments and instruction results",
        ));
    }
    Ok(())
}

/// Read only the derived opcode's variant name. The LIR opcode may carry an
/// arbitrarily large unsupported payload; a refusal must not print that data.
fn source_opcode_name(opcode: &L) -> String {
    struct Name(String);
    impl std::fmt::Write for Name {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            for character in text.chars() {
                if matches!(character, ' ' | '{' | '(') || self.0.len() >= 64 {
                    return Err(std::fmt::Error);
                }
                self.0.push(character);
            }
            Ok(())
        }
    }
    let mut name = Name(String::new());
    let _ = std::fmt::write(&mut name, format_args!("{opcode:?}"));
    name.0
}

fn source_trace(source: &Function) -> Result<SourceTrace, MemoryLeafRefusal> {
    let refuse = |why: &str| MemoryLeafRefusal::Source(why.to_owned());
    if source.blocks.len() != 1
        || !source.stack_slots.is_empty()
        || !source.eh_info.is_empty()
        || source.stack_protector != StackProtectorMode::None
        || !source.param_pointee_types.is_empty()
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
        || !source.sret_arg_indirect_callees.is_empty()
        || (!source.block_order.is_empty() && source.block_order != [source.entry_block])
    {
        return Err(refuse(
            "requires one block without stack, EH or aggregate ABI metadata",
        ));
    }
    let block = source
        .blocks
        .get(&source.entry_block)
        .ok_or_else(|| refuse("missing entry block"))?;
    let signature = &source.signature;
    if signature.params.len() > MAX_SOURCE_ARGUMENTS || signature.returns.len() > 1 {
        return Err(refuse("requires at most eight arguments and one return"));
    }
    source_cardinality_preflight(source, block)?;
    let mut values: HashMap<Value, SourceValue> = HashMap::new();
    for (index, ty) in signature.params.iter().enumerate() {
        let bits = type_bits(ty).ok_or_else(|| refuse("a non-integer argument"))?;
        values.insert(
            Value(index as u32),
            SourceValue {
                lin: Lin::symbol(Sym::Argument(index as u8)),
                bits,
            },
        );
    }
    if !block.params.is_empty()
        && (block.params.len() != signature.params.len()
            || block
                .params
                .iter()
                .enumerate()
                .any(|(i, (value, ty))| value.0 as usize != i || ty != &signature.params[i]))
    {
        return Err(refuse(
            "entry parameters disagree with the Value(0..n) signature convention",
        ));
    }
    let mut events = Vec::new();
    let mut widths = Vec::new();
    let mut returned = None;
    let mut done = false;
    for (index, inst) in block.instructions.iter().enumerate() {
        if done {
            return Err(refuse("an instruction follows the return"));
        }
        let arity = match inst.opcode {
            L::Iconst { .. } => (0, 1),
            L::Copy | L::Uextend { .. } | L::Load { .. } => (1, 1),
            L::Iadd | L::Isub | L::ArrayGep { elem_ty: Type::I8 } => (2, 1),
            L::Store { .. } => (2, 0),
            L::Return => (signature.returns.len(), 0),
            _ => {
                return Err(MemoryLeafRefusal::Source(format!(
                    "instruction {index}: {}",
                    source_opcode_name(&inst.opcode)
                )));
            }
        };
        if (inst.args.len(), inst.results.len()) != arity {
            return Err(refuse("wrong operand or result arity"));
        }
        let read = |value: &Value| {
            values
                .get(value)
                .cloned()
                .ok_or_else(|| refuse("a use of an undefined value"))
        };
        let pointer = |value: &Value| -> Result<Lin, MemoryLeafRefusal> {
            let pointer = read(value)?;
            if pointer.bits != 64 {
                return Err(refuse("a pointer that is not 64 bits wide"));
            }
            Ok(pointer.lin)
        };
        let result = match &inst.opcode {
            L::Iconst { ty, imm } => {
                let bits = type_bits(ty).ok_or_else(|| refuse("a non-integer constant"))?;
                SourceValue {
                    lin: Lin::constant(*imm as u64 & mask(bits)),
                    bits,
                }
            }
            L::Copy => read(&inst.args[0])?,
            L::Iadd | L::Isub => {
                let (a, b) = (read(&inst.args[0])?, read(&inst.args[1])?);
                if a.bits != 64 || b.bits != 64 {
                    return Err(refuse("arithmetic narrower than 64 bits"));
                }
                SourceValue {
                    lin: a.lin.combine(&b.lin, matches!(inst.opcode, L::Isub)),
                    bits: 64,
                }
            }
            // A byte-stride address, the adapter's spelling of `base +
            // offset` since `b79533c9c`. LIR `ArrayGep { elem_ty }` is `base +
            // index * size(elem_ty)` with an I64 index, and the size of I8 is
            // 1, so its one meaning here is the 64-bit wrapping sum (OD-185's
            // and `read_only_source_lir`'s reading). Any other element type
            // is a product this linear domain does not model; it stays
            // refused by name above.
            L::ArrayGep { elem_ty: Type::I8 } => {
                let (base, index) = (read(&inst.args[0])?, read(&inst.args[1])?);
                if base.bits != 64 || index.bits != 64 {
                    return Err(refuse("a byte-stride address narrower than 64 bits"));
                }
                SourceValue {
                    lin: base.lin.combine(&index.lin, false),
                    bits: 64,
                }
            }
            L::Uextend { from_ty, to_ty } => {
                let value = read(&inst.args[0])?;
                let (from, to) = (
                    type_bits(from_ty).ok_or_else(|| refuse("a non-integer extension"))?,
                    type_bits(to_ty).ok_or_else(|| refuse("a non-integer extension"))?,
                );
                if value.bits != from || to <= from || !value.lin.exact_within(from, &widths) {
                    return Err(refuse(
                        "a zero extension of a value not known to be zero-extended",
                    ));
                }
                SourceValue {
                    lin: value.lin,
                    bits: to,
                }
            }
            L::Load { ty, .. } => {
                let bits = type_bits(ty).ok_or_else(|| refuse("a non-integer load"))?;
                let address = pointer(&inst.args[0])?;
                let position = events.len();
                events.push(SourceEvent {
                    index,
                    load: true,
                    address,
                    bytes: bits / 8,
                    stored: None,
                });
                widths.push(bits);
                SourceValue {
                    lin: Lin::symbol(Sym::Loaded(position)),
                    bits,
                }
            }
            L::Store { ty, .. } => {
                let bits = type_bits(ty).ok_or_else(|| refuse("a non-integer store"))?;
                let stored = read(&inst.args[0])?;
                if stored.bits != bits {
                    return Err(refuse("a stored value of another width than the store"));
                }
                let address = pointer(&inst.args[1])?;
                events.push(SourceEvent {
                    index,
                    load: false,
                    address,
                    bytes: bits / 8,
                    stored: Some(stored),
                });
                widths.push(0);
                continue;
            }
            L::Return => {
                if let Some(value) = inst.args.first() {
                    let value = read(value)?;
                    let ty = &signature.returns[0];
                    let bits = type_bits(ty).ok_or_else(|| refuse("a non-integer return"))?;
                    // A 32- or 64-bit return is that value. An 8- or 16-bit
                    // return is observed through W0: the adapter returns its
                    // explicit 32-bit extension, compared in full.
                    if !(value.bits == bits && bits >= 32 || value.bits == 32 && bits < 32) {
                        return Err(refuse(
                            "a returned value that is neither the return's width nor its \
                             32-bit extension",
                        ));
                    }
                    returned = Some(value);
                }
                done = true;
                continue;
            }
            _ => unreachable!("admitted above"),
        };
        if values.insert(inst.results[0], result).is_some() {
            return Err(refuse("an SSA value defined twice"));
        }
    }
    if !done {
        return Err(refuse("no return"));
    }
    if events.is_empty() {
        return Err(refuse("no memory access to bind"));
    }
    // Sidecar type hints must agree with the inferred widths (instruction
    // selection reads them); a hint for an absent value is refused too.
    for (value, hint) in &source.value_types {
        if values
            .get(value)
            .map(|value| bits_type(value.bits))
            .as_ref()
            != Some(hint)
        {
            return Err(refuse("a type hint disagrees with the inferred width"));
        }
    }
    Ok(SourceTrace {
        events,
        widths,
        returned,
    })
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

/// Register file index of an X0..X17 or W0..W17 operand.
fn register_index(operand: &O) -> Option<usize> {
    match operand {
        O::PReg(reg) => match reg.encoding() {
            e @ 0..=17 => Some(usize::from(e)),
            e @ 32..=49 => Some(usize::from(e - 32)),
            _ => None,
        },
        _ => None,
    }
}

fn is_w_view(operand: &O) -> bool {
    matches!(operand, O::PReg(reg) if (32..=49).contains(&reg.encoding()))
}

fn plain_effects(inst: &MachInst) -> bool {
    inst.flags == MachInst::new(inst.opcode, Vec::new()).flags
        && inst.implicit_defs.is_empty()
        && inst
            .implicit_uses
            .iter()
            .all(|reg| register_index(&O::PReg(*reg)).is_some() || *reg == X30)
}

/// Check `machine` against `source` and bind each of its memory accesses.
pub fn source_bound_memory_leaf<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
) -> Result<SourceBoundMemoryLeaf<'a>, MemoryLeafRefusal> {
    let unsupported = |why: &str| MemoryLeafRefusal::Machine(why.to_owned());
    if source.name != machine.name {
        return Err(unsupported("source and machine name different functions"));
    }
    let trace = source_trace(source)?;
    if machine.signature.params.len() != source.signature.params.len()
        || machine.signature.returns.len() != source.signature.returns.len()
        || !machine.stack_slots.is_empty()
        || machine.eh_metadata.has_eh_info()
        || machine.stack_protector != StackProtectorMode::None
        || machine.stack_protector_slot.is_some()
        || !machine.jump_tables.is_empty()
    {
        return Err(unsupported(
            "requires the source's arity and no stack, EH or jump table",
        ));
    }
    // The chain is every instruction the encoder emits: `machine_chain`
    // requires each laid-out instruction to occur once and every block
    // outside the layout to be empty. An arena entry no block references (an
    // instruction an optimizer unlinked, such as the UXTH O2 drops after an
    // LDRH that already zero-extends) is never emitted, so it is not judged.
    let chain = super::linear::machine_chain(machine)
        .map_err(|_| unsupported("control flow is not a bounded unconditional chain"))?;
    let body: Vec<InstId> = chain
        .instructions
        .iter()
        .copied()
        .filter(|id| !super::inert_allocated_nop(&machine.insts[id.0 as usize], machine.next_vreg))
        .collect();
    let widths = &trace.widths;
    let mut registers: [Option<RegValue>; 18] = std::array::from_fn(|_| None);
    for (index, register) in registers
        .iter_mut()
        .enumerate()
        .take(source.signature.params.len())
    {
        *register = Some(RegValue::full(Lin::symbol(Sym::Argument(index as u8))));
    }
    let read = |registers: &[Option<RegValue>; 18],
                operand: &O|
     -> Result<RegValue, MemoryLeafRefusal> {
        match operand {
            O::Special(SpecialReg::XZR | SpecialReg::WZR) => Ok(RegValue::full(Lin::constant(0))),
            _ => {
                let index = register_index(operand)
                    .ok_or_else(|| unsupported("an operand outside X0..X17"))?;
                registers[index]
                    .clone()
                    .ok_or_else(|| unsupported("a read of an undefined register"))
            }
        }
    };
    let write_index =
        |operand: &O| register_index(operand).ok_or_else(|| unsupported("a write outside X0..X17"));
    let mut accesses = Vec::new();
    let mut returned = false;
    for id in &body {
        if returned {
            return Err(unsupported("an instruction follows the return"));
        }
        let inst = &machine.insts[id.0 as usize];
        if !plain_effects(inst) {
            return Err(unsupported("non-default flags or an implicit effect"));
        }
        let operands = inst.operands.as_slice();
        match inst.opcode {
            M::LdrRI | M::LdrbRI | M::LdrhRI | M::StrRI | M::StrbRI | M::StrhRI => {
                let access = memory_access(inst).ok_or_else(|| {
                    unsupported("a memory access the memory-effect decomposition does not admit")
                })?;
                if access.base == 31 {
                    return Err(unsupported("an SP-based access (a frame or spill slot)"));
                }
                let position = accesses.len();
                let disagree = |what: &str| MemoryLeafRefusal::Trace {
                    position,
                    what: what.to_owned(),
                };
                let event = trace
                    .events
                    .get(position)
                    .ok_or(MemoryLeafRefusal::TraceLength {
                        machine: position + 1,
                        expected: trace.events.len(),
                    })?;
                if event.load != access.load {
                    return Err(disagree("a load where the source stores, or the reverse"));
                }
                if event.bytes != access.bytes {
                    return Err(disagree("another access width than the source's"));
                }
                let base = read(&registers, &operands[1])?;
                if base.bits != 64 {
                    return Err(disagree("the base register holds a narrowed value"));
                }
                let delta = event
                    .address
                    .combine(&base.lin, true)
                    .as_constant()
                    .ok_or_else(|| {
                        disagree(
                            "the base register does not hold the source pointer plus a constant",
                        )
                    })?;
                if delta != access.offset as u64 {
                    return Err(disagree("the offset does not reach the source's address"));
                }
                if let LoweringProvenance::SourceInst { id: stamp, .. } =
                    machine.inst_lowering_provenance(*id)
                    && (stamp.block != source.entry_block.0 || stamp.index as usize != event.index)
                {
                    return Err(MemoryLeafRefusal::Stamp {
                        position,
                        stamped: stamp.to_string(),
                        block: source.entry_block.0,
                        index: event.index,
                    });
                }
                if access.load {
                    let destination = write_index(&operands[0])?;
                    registers[destination] =
                        Some(RegValue::full(Lin::symbol(Sym::Loaded(position))));
                } else {
                    let data = if access.zero[0] {
                        RegValue::full(Lin::constant(0))
                    } else {
                        read(&registers, &operands[0])?
                    };
                    let stored = event
                        .stored
                        .as_ref()
                        .expect("a store event carries its value");
                    if !data.low_bits_equal(stored, 8 * access.bytes) {
                        return Err(disagree(
                            "the stored register does not hold the source's value",
                        ));
                    }
                }
                accesses.push(BoundLeafAccess {
                    instruction: *id,
                    source_index: event.index,
                    position,
                    contract: ContractAccess::scalar(
                        access.load,
                        event.bytes,
                        delta as i64,
                        access.base,
                        access.transfer[0],
                        access.zero[0],
                    ),
                });
            }
            M::MOVXrr | M::MOVWrr => {
                let [destination, input] = operands else {
                    return Err(unsupported("a move with other than two operands"));
                };
                let value = read(&registers, input)?;
                let destination = write_index(destination)?;
                registers[destination] = Some(if inst.opcode == M::MOVWrr {
                    value.narrowed(32, widths)
                } else {
                    value
                });
            }
            M::Uxtb | M::Uxth => {
                let [destination, input] = operands else {
                    return Err(unsupported("an extension with other than two operands"));
                };
                if !is_w_view(destination) {
                    return Err(unsupported("an extension to an X register"));
                }
                let value = read(&registers, input)?;
                let destination = write_index(destination)?;
                registers[destination] =
                    Some(value.narrowed(if inst.opcode == M::Uxtb { 8 } else { 16 }, widths));
            }
            M::AddRI | M::SubRI => {
                let [destination, input, O::Imm(imm @ 0..=4095)] = operands else {
                    return Err(unsupported("an add/sub immediate outside imm12"));
                };
                if is_w_view(destination) || is_w_view(input) {
                    return Err(unsupported("a 32-bit add/sub"));
                }
                let value = read(&registers, input)?;
                if value.bits != 64 || matches!(input, O::Special(_)) {
                    return Err(unsupported("an add/sub of a narrowed or special register"));
                }
                let imm = *imm as u64;
                let lin = if inst.opcode == M::AddRI {
                    value.lin.plus(imm)
                } else {
                    value.lin.plus(imm.wrapping_neg())
                };
                let destination = write_index(destination)?;
                registers[destination] = Some(RegValue::full(lin.reduced(64)));
            }
            M::Movz => {
                let (destination, imm, shift) = match operands {
                    [destination, O::Imm(imm)] => (destination, *imm, 0),
                    [destination, O::Imm(imm), O::Imm(shift)] => (destination, *imm, *shift),
                    _ => return Err(unsupported("a MOVZ of another shape")),
                };
                let limit = if is_w_view(destination) { 16 } else { 48 };
                if !(0..=0xffff).contains(&imm) || !(0..=limit).contains(&shift) || shift % 16 != 0
                {
                    return Err(unsupported("a MOVZ outside its fields"));
                }
                let value =
                    ((imm as u64) << shift) & mask(if is_w_view(destination) { 32 } else { 64 });
                let destination = write_index(destination)?;
                registers[destination] = Some(RegValue::full(Lin::constant(value)));
            }
            M::Ret => {
                if !(operands.is_empty() || operands == [O::PReg(X30)]) {
                    return Err(unsupported("a return through another register than LR"));
                }
                if let Some(value) = &trace.returned {
                    let x0 = registers[0]
                        .clone()
                        .ok_or_else(|| unsupported("an undefined return register"))?;
                    if !x0.low_bits_equal(value, value.bits) {
                        return Err(MemoryLeafRefusal::Return);
                    }
                }
                returned = true;
            }
            _ => {
                return Err(MemoryLeafRefusal::Machine(format!(
                    "instruction {id:?}: {:?}",
                    inst.opcode
                )));
            }
        }
    }
    if !returned {
        return Err(unsupported("no return"));
    }
    if accesses.len() != trace.events.len() {
        return Err(MemoryLeafRefusal::TraceLength {
            machine: accesses.len(),
            expected: trace.events.len(),
        });
    }
    Ok(SourceBoundMemoryLeaf {
        source,
        machine,
        accesses,
    })
}

#[cfg(test)]
#[path = "source_bound_memory_leaf_tests.rs"]
pub(crate) mod tests;
