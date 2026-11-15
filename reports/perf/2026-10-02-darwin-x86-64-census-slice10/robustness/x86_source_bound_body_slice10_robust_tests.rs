// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Robustness probe of slice 10 (instruction coverage: checked arithmetic,
//! `not`, `neg`, `popcnt`, shifts by CL, `call r64`): mutate the real
//! machine streams of the slice-10 fixtures (O0 selection and the x86
//! optimizer at O1-O3), judge every mutant with the owner, the solver-free
//! sampler, and (unless `ROB10_NO_REPLAY`) the replayed theorem (admitted
//! AY --strict-proofs + Clean) and the verifier's crediting, and compare
//! with an INDEPENDENT concrete interpreter of the LIR and of the pre-RA x86
//! stream (ground truth). Diagnostic only (ignored).
//!
//! Ground truth. LIR checked arithmetic is Rust's `overflowing_add`/`_sub`/
//! `_mul` at the operand width (signed for the `S` forms), `Bnot` is `!x`,
//! `Ineg` `wrapping_neg` and `CtPop` `count_ones`, all at the operand width;
//! a shift by a variable amount is trust-ir's below the width and undefined
//! at or above it (an input reaching it is skipped, so it judges nothing);
//! an indirect call calls the function its pointer value names. The
//! machine: `add`/`sub` set CF to the unsigned carry or borrow and OF to the
//! signed overflow (and ZF, SF and PF from the result), `imul` sets CF = OF
//! to "the signed product does not fit", `mul` writes RDX:RAX (EDX:EAX, each
//! zero-extended) with the full unsigned product and sets CF = OF to "the
//! high half is not zero"; the flags the Intel SDM leaves undefined after
//! `imul` and `mul` are fresh garbage, as are all flags after any other ALU
//! row but `cmp`/`test`/`and`/`or`/`xor`. `not` complements, `neg` negates,
//! `popcnt` counts, a shift by CL shifts by the low byte of RCX masked to 5
//! bits (6 for a 64-bit operand), and `call r64` calls the function the
//! register's 64 bits name (written from the Intel SDM, not from either
//! translator). A callee is a deterministic pseudo-random function of (its
//! identity, the bits its parameters own). A virtual register's bits above a
//! narrow write are garbage; a physical register's 8- or 16-bit write keeps
//! the bits above. Observables: the returned bits a caller reads, the call
//! log (callee and argument bits), incoming accesses and final incoming
//! memory, and the callee-saved registers at the return.

use super::slice5::describe;
use super::slice10::{InsnShape, all_slice_ten_shapes, slice10_pair, theorem_refuted};
use super::*;
use std::collections::BTreeMap;
use trust_cg_ir::X86CondCode;

const SLOT_BASE: u64 = 0x7ff0_0000_0000;
const SLOT_STRIDE: u64 = 0x1_0000;
const PARAM_BASE: u64 = 0x7fe0_0000_0000;
const RESULT_BASE: u64 = 0x7fd0_0000_0000;
const GT_INPUTS: u64 = 3000;

fn slot_base(slot: u32) -> u64 {
    SLOT_BASE + u64::from(slot) * SLOT_STRIDE
}

fn splitmix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn mix(a: u64, b: u64) -> u64 {
    splitmix(a ^ splitmix(b.wrapping_add(0x1234_5678)))
}

fn bitmask(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn sext(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else {
        let shift = 64 - bits;
        (((value << shift) as i64) >> shift) as u64
    }
}

fn name_hash(name: &str) -> u64 {
    name.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The ground truth's eightbyte placement: `(offset, bytes)` per register.
fn eightbytes(size: u32) -> Vec<(u32, u32)> {
    (0..size.div_ceil(8))
        .map(|k| (8 * k, (size - 8 * k).min(8)))
        .collect()
}

fn is_aggregate(ty: &Type) -> bool {
    matches!(ty, Type::Struct(_) | Type::Array(..))
}

/// A parameter or result of the ground truth's callees.
// `Aggregate` is slice 8's; no slice-10 callee takes or returns one.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
enum Kind {
    Scalar(u32),
    Aggregate(u32),
}

/// The direct callees of the slice-10 fixtures.
fn callee(name: &str) -> Option<(Vec<Kind>, Option<Kind>)> {
    use Kind::*;
    Some(match name {
        "g" => (vec![Scalar(64)], Some(Scalar(64))),
        "panic_const_overflow" => (vec![], None),
        _ => return None,
    })
}

/// The function type of a fixture's function-pointer parameter: what any
/// function its pointer names takes and returns.
fn indirect_signature(shape: InsnShape) -> (Vec<Kind>, Option<Kind>) {
    use Kind::*;
    match shape {
        InsnShape::IndirectVoid => (vec![Scalar(32)], None),
        _ => (vec![Scalar(64)], Some(Scalar(64))),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Observed {
    end: String,
    calls: Vec<String>,
    accesses: Vec<String>,
    incoming: BTreeMap<u64, u8>,
}

struct World {
    seed: u64,
    mem: HashMap<u64, u8>,
    calls: Vec<String>,
    accesses: Vec<String>,
    /// The signature of every function a pointer names (slice 10).
    indirect: (Vec<Kind>, Option<Kind>),
}

fn is_private(address: u64) -> bool {
    address >= RESULT_BASE
}

impl World {
    fn new(seed: u64, shape: InsnShape) -> Self {
        Self {
            seed,
            mem: HashMap::new(),
            calls: Vec::new(),
            accesses: Vec::new(),
            indirect: indirect_signature(shape),
        }
    }

    fn garbage(&self, tag: u64, x: u64) -> u64 {
        mix(mix(self.seed, tag), x)
    }

    fn byte(&self, address: u64) -> u8 {
        self.mem
            .get(&address)
            .copied()
            .unwrap_or_else(|| self.garbage(0xF00D, address) as u8)
    }

    fn read(&mut self, address: u64, bytes: u32) -> u64 {
        let mut value = 0u64;
        for i in (0..u64::from(bytes)).rev() {
            value = (value << 8) | u64::from(self.byte(address.wrapping_add(i)));
        }
        if !is_private(address) {
            self.accesses.push(format!("load{bytes} {address:#x}"));
        }
        value
    }

    fn write(&mut self, address: u64, bytes: u32, value: u64) {
        for i in 0..u64::from(bytes) {
            self.mem
                .insert(address.wrapping_add(i), (value >> (8 * i)) as u8);
        }
        if !is_private(address) {
            self.accesses.push(format!(
                "store{bytes} {address:#x} = {:#x}",
                bitmask(value, bytes * 8)
            ));
        }
    }

    /// Call `name` with its argument registers `registers` (in System V
    /// order); the result registers (RAX, RDX) and their garbage.
    fn call(&mut self, name: &str, registers: &[u64], step: u64) -> Result<[u64; 2], String> {
        let (params, result) = match callee(name) {
            Some(known) => known,
            None if name.starts_with("fn@") => self.indirect.clone(),
            None => return Err(format!("unknown callee {name}")),
        };
        let mut key = mix(name_hash(name), 0x5151);
        let mut log = format!("{name}(");
        let mut next = 0usize;
        for param in &params {
            match param {
                Kind::Scalar(bits) => {
                    let value = bitmask(registers[next], *bits);
                    next += 1;
                    key = mix(key, value);
                    log.push_str(&format!("{value:#x}, "));
                }
                Kind::Aggregate(size) => {
                    for (_, bytes) in eightbytes(*size) {
                        let value = bitmask(registers[next], bytes * 8);
                        next += 1;
                        key = mix(key, value);
                        log.push_str(&format!("{value:#x}/{bytes}, "));
                    }
                }
            }
        }
        self.calls.push(log);
        let mut out = [
            self.garbage(0xC10B, step * 2),
            self.garbage(0xC10B, step * 2 + 1),
        ];
        match result {
            None => {}
            Some(Kind::Scalar(bits)) => {
                out[0] = (out[0] & !bitmask(u64::MAX, bits)) | bitmask(splitmix(key), bits);
            }
            Some(Kind::Aggregate(size)) => {
                for (k, (_, bytes)) in eightbytes(size).into_iter().enumerate() {
                    let value = splitmix(key ^ (k as u64 + 1));
                    // A zero low prefix now and then (an `Option`'s `None`
                    // tag beside a nonzero payload, or a zero low half):
                    // `key % 9` low bytes zeroed in one call of four.
                    let zeroed = if key % 4 == 0 { (key >> 8) % 9 } else { 0 };
                    let value = if zeroed == 0 {
                        value
                    } else {
                        value & !bitmask(u64::MAX, (8 * zeroed) as u32)
                    };
                    out[k] = (out[k] & !bitmask(u64::MAX, bytes * 8)) | bitmask(value, bytes * 8);
                }
            }
        }
        Ok(out)
    }

    fn finish(self, end: String) -> Observed {
        Observed {
            end,
            calls: self.calls,
            accesses: self.accesses,
            incoming: self
                .mem
                .into_iter()
                .filter(|(address, _)| !is_private(*address))
                .collect(),
        }
    }
}

fn ty_bits(ty: &Type) -> Option<u32> {
    Some(match ty {
        Type::B1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        _ => return None,
    })
}

/// The return bits a caller reads of a scalar result of type `ty`.
fn return_bits(ty: &Type) -> u32 {
    match ty {
        Type::B1 | Type::I32 => 32,
        Type::I8 => 8,
        Type::I16 => 16,
        _ => 64,
    }
}

/// Raw argument registers (RDI, RSI, ...), each drawn independently: small
/// words, shift counts around every width, overflow and sign boundaries,
/// zero, and random words of varied density. (A per-input draw: slice 8's
/// one pattern for every register never put a small shift count beside a
/// large value, nor both operands of an add at zero.)
fn gt_registers(seed: u64) -> Vec<u64> {
    const COUNTS: [u64; 12] = [0, 1, 2, 7, 8, 15, 16, 31, 32, 33, 63, 64];
    const EDGES: [u64; 14] = [
        0,
        1,
        u64::MAX,
        1 << 63,
        (1 << 63) - 1,
        0xffff_ffff,
        0x8000_0000,
        0x7fff_ffff,
        0xff,
        0x80,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
        0x3333_3333_3333_3333,
        0xcccc_cccc_cccc_cccc,
    ];
    // One register in eight samples: every register the same word (equal
    // operands).
    let same = mix(seed, 0xC000) % 8 == 0;
    (0..6)
        .map(|i| {
            let i = if same { 0 } else { i };
            let r = mix(seed, 0xA000 + i);
            match mix(seed, 0xB000 + i) % 10 {
                0 => r % 16,
                1 => r % 72,
                2 => COUNTS[(r % COUNTS.len() as u64) as usize],
                3 => EDGES[(r % EDGES.len() as u64) as usize],
                4 => r & 0x00ff_00ff_00ff_00ff,
                5 => r & 0xffff_0000_ffff_0000,
                6 => r | (1 << 63),
                7 => 0,
                _ => r,
            }
        })
        .collect()
}

/// The text a caller observes of a return: each scalar at its return bits,
/// each aggregate eightbyte at its own bytes.
fn returned_text(
    returns: &[Type],
    registers: [u64; 2],
    bytes_of: &dyn Fn(usize) -> Vec<u8>,
) -> String {
    let mut text = String::from("ret");
    match returns {
        [only] if is_aggregate(only) => {
            let bytes = bytes_of(0);
            for (k, (offset, n)) in eightbytes(only.bytes()).into_iter().enumerate() {
                let _ = k;
                let lane: u64 = (0..n)
                    .rev()
                    .fold(0, |v, i| (v << 8) | u64::from(bytes[(offset + i) as usize]));
                text.push_str(&format!(" {lane:#x}/{n}"));
            }
        }
        _ => {
            for (ty, register) in returns.iter().zip(registers) {
                text.push_str(&format!(" {:#x}", bitmask(register, return_bits(ty))));
            }
        }
    }
    text
}

/// trust-ir's `Overflow` of two `bits`-wide operands, from the mathematical
/// result (an `i128`/`u128`, which cannot overflow): the wrapped value, and
/// whether the exact result lies outside the carrier's range.
fn overflowing(opcode: &L, a: u64, b: u64, bits: u32) -> (u64, bool) {
    let (ua, ub) = (u128::from(bitmask(a, bits)), u128::from(bitmask(b, bits)));
    let (sa, sb) = (
        i128::from(sext(a, bits) as i64),
        i128::from(sext(b, bits) as i64),
    );
    let max_unsigned = (1u128 << bits) - 1;
    let (min_signed, max_signed) = (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1);
    let unsigned = |exact: i128| {
        (
            bitmask(exact as u64, bits),
            exact < 0 || exact as u128 > max_unsigned,
        )
    };
    let signed = |exact: i128| {
        (
            bitmask(exact as u64, bits),
            exact < min_signed || exact > max_signed,
        )
    };
    match opcode {
        L::CheckedUadd => unsigned(ua as i128 + ub as i128),
        L::CheckedUsub => unsigned(ua as i128 - ub as i128),
        L::CheckedUmul => {
            let exact = ua * ub;
            (bitmask(exact as u64, bits), exact > max_unsigned)
        }
        L::CheckedSadd => signed(sa + sb),
        L::CheckedSsub => signed(sa - sb),
        _ => signed(sa * sb),
    }
}

/// Run the LIR source on argument registers `raw`.
fn run_source(source: &Function, raw: &[u64], world: &mut World) -> String {
    let mut vals: HashMap<Value, (u64, u32)> = HashMap::new();
    let mut aggregate_values: HashSet<Value> = HashSet::new();
    let mut next = 0usize;
    for (i, ty) in source.signature.params.iter().enumerate() {
        if is_aggregate(ty) {
            // The callee's copy of the caller's eightbytes.
            let base = PARAM_BASE + SLOT_STRIDE * i as u64;
            for (offset, bytes) in eightbytes(ty.bytes()) {
                world.write(base + u64::from(offset), bytes, raw[next]);
                next += 1;
            }
            vals.insert(Value(i as u32), (base, 64));
            aggregate_values.insert(Value(i as u32));
        } else {
            let bits = ty_bits(ty).unwrap_or(64);
            let value = if bits == 1 {
                raw[next] & 1
            } else {
                bitmask(raw[next], bits)
            };
            next += 1;
            vals.insert(Value(i as u32), (value, bits));
        }
    }
    let mut block = source.entry_block;
    let mut steps = 0u64;
    loop {
        let Some(body) = source.blocks.get(&block) else {
            return format!("fault: no block {block:?}");
        };
        let mut next_block = None;
        for (index, inst) in body.instructions.iter().enumerate() {
            steps += 1;
            if steps > 10_000 {
                return "fault: step limit".into();
            }
            let get = |k: usize| -> Result<(u64, u32), String> {
                inst.args
                    .get(k)
                    .and_then(|value| vals.get(value).copied())
                    .ok_or_else(|| format!("fault: undefined operand of {:?}", inst.opcode))
            };
            // The overflow result of checked arithmetic (its second result).
            let mut second: Option<(u64, u32)> = None;
            let def: Result<Option<(u64, u32)>, String> = (|| {
                Ok(match &inst.opcode {
                    L::CheckedUadd
                    | L::CheckedUsub
                    | L::CheckedUmul
                    | L::CheckedSadd
                    | L::CheckedSsub
                    | L::CheckedSmul => {
                        let (a, bits) = get(0)?;
                        let (b, _) = get(1)?;
                        let (value, overflow) = overflowing(&inst.opcode, a, b, bits);
                        second = Some((u64::from(overflow), 1));
                        Some((value, bits))
                    }
                    L::Bnot => {
                        let (a, bits) = get(0)?;
                        Some((bitmask(!a, bits), bits))
                    }
                    L::Ineg => {
                        let (a, bits) = get(0)?;
                        Some((bitmask(0u64.wrapping_sub(a), bits), bits))
                    }
                    L::CtPop => {
                        let (a, bits) = get(0)?;
                        Some((u64::from(bitmask(a, bits).count_ones()), bits))
                    }
                    L::CallIndirect => {
                        let (pointer, _) = get(0)?;
                        let (params, result) = world.indirect.clone();
                        let mut registers = Vec::new();
                        for k in 0..params.len() {
                            registers.push(get(k + 1)?.0);
                        }
                        let out = world
                            .call(&format!("fn@{pointer:#x}"), &registers, 1000 + index as u64)
                            .map_err(|e| format!("fault: {e}"))?;
                        match (result, inst.results.first()) {
                            (Some(Kind::Scalar(bits)), Some(_)) => {
                                Some((bitmask(out[0], bits), bits))
                            }
                            (None, None) => None,
                            _ => return Err("gt: indirect result".into()),
                        }
                    }
                    L::Iconst { ty, imm } => {
                        let bits = ty_bits(ty).unwrap_or(64);
                        Some((bitmask(*imm as u64, bits), bits))
                    }
                    L::Copy => Some(get(0)?),
                    L::Bitcast { to_ty } => {
                        let bits = ty_bits(to_ty).unwrap_or(64);
                        Some((bitmask(get(0)?.0, bits), bits))
                    }
                    L::Iadd
                    | L::Isub
                    | L::Imul
                    | L::Band
                    | L::Bor
                    | L::Bxor
                    | L::Ishl
                    | L::Ushr
                    | L::Sshr => {
                        let (a, bits) = get(0)?;
                        let (b, _) = get(1)?;
                        // trust-ir `shift_amount`: an amount of the width or
                        // more is undefined behavior (any machine behavior
                        // refines it; the input is not judged).
                        if matches!(inst.opcode, L::Ishl | L::Ushr | L::Sshr)
                            && b >= u64::from(bits)
                        {
                            return Err("ub".into());
                        }
                        let amount = (b % u64::from(bits.max(1))) as u32;
                        let value = match &inst.opcode {
                            L::Iadd => a.wrapping_add(b),
                            L::Isub => a.wrapping_sub(b),
                            L::Imul => a.wrapping_mul(b),
                            L::Band => a & b,
                            L::Bor => a | b,
                            L::Bxor => a ^ b,
                            L::Ishl => a << amount,
                            L::Ushr => a >> amount,
                            _ => (sext(a, bits) as i64 >> amount) as u64,
                        };
                        Some((bitmask(value, bits), bits))
                    }
                    L::Uextend { to_ty, .. } => Some((get(0)?.0, ty_bits(to_ty).unwrap_or(64))),
                    L::Sextend { from_ty, to_ty } => {
                        let from = ty_bits(from_ty).unwrap_or(64);
                        let bits = ty_bits(to_ty).unwrap_or(64);
                        Some((bitmask(sext(get(0)?.0, from), bits), bits))
                    }
                    L::Trunc { to_ty } => {
                        let bits = ty_bits(to_ty).unwrap_or(64);
                        Some((bitmask(get(0)?.0, bits), bits))
                    }
                    L::Icmp { cond } => {
                        let (a, bits) = get(0)?;
                        let (b, _) = get(1)?;
                        let (sa, sb) = (sext(a, bits) as i64, sext(b, bits) as i64);
                        let holds = match cond {
                            IntCC::Equal => a == b,
                            IntCC::NotEqual => a != b,
                            IntCC::SignedLessThan => sa < sb,
                            IntCC::SignedGreaterThanOrEqual => sa >= sb,
                            IntCC::SignedGreaterThan => sa > sb,
                            IntCC::SignedLessThanOrEqual => sa <= sb,
                            IntCC::UnsignedLessThan => a < b,
                            IntCC::UnsignedGreaterThanOrEqual => a >= b,
                            IntCC::UnsignedGreaterThan => a > b,
                            IntCC::UnsignedLessThanOrEqual => a <= b,
                        };
                        Some((u64::from(holds), 1))
                    }
                    L::Select {
                        cond: IntCC::NotEqual,
                    } => {
                        let (test, _) = get(0)?;
                        Some(if test != 0 { get(1)? } else { get(2)? })
                    }
                    L::StackAddr { slot } => Some((slot_base(*slot), 64)),
                    L::StructGep {
                        struct_ty,
                        field_index,
                    } => {
                        let offset = struct_ty
                            .offset_of(*field_index as usize)
                            .ok_or("fault: struct gep")?;
                        Some((get(0)?.0.wrapping_add(u64::from(offset)), 64))
                    }
                    L::Load { ty, .. } => {
                        let (address, _) = get(0)?;
                        let bits = ty_bits(ty).ok_or("fault: load type")?;
                        let value = world.read(address, bits.div_ceil(8));
                        Some(if bits == 1 {
                            (u64::from(value != 0), 1)
                        } else {
                            (value, bits)
                        })
                    }
                    L::Store { ty, .. } => {
                        let (value, _) = get(0)?;
                        let (address, _) = get(1)?;
                        let bits = ty_bits(ty).ok_or("fault: store type")?;
                        world.write(address, bits.div_ceil(8), value);
                        None
                    }
                    L::Call { name, .. } => {
                        // Each argument: an aggregate's eightbytes (bytes at
                        // its address), else the scalar.
                        let (params, result) = callee(name).ok_or("gt: callee")?;
                        let result = result.as_ref().copied();
                        let mut registers = Vec::new();
                        for (k, param) in params.iter().enumerate() {
                            let (value, _) = get(k)?;
                            match param {
                                Kind::Scalar(_) => registers.push(value),
                                Kind::Aggregate(size) => {
                                    for (offset, bytes) in eightbytes(*size) {
                                        registers
                                            .push(world.read(value + u64::from(offset), bytes));
                                    }
                                }
                            }
                        }
                        let out = world
                            .call(name, &registers, 1000 + index as u64)
                            .map_err(|e| format!("fault: {e}"))?;
                        match (result, inst.results.first()) {
                            (_, None) => None,
                            (Some(Kind::Aggregate(size)), Some(result)) => {
                                let base = RESULT_BASE + SLOT_STRIDE * u64::from(result.0);
                                for (k, (offset, bytes)) in eightbytes(size).into_iter().enumerate()
                                {
                                    world.write(base + u64::from(offset), bytes, out[k]);
                                }
                                Some((base, 64))
                            }
                            (_, Some(result)) => {
                                let bits = source
                                    .value_types
                                    .get(result)
                                    .and_then(ty_bits)
                                    .unwrap_or(64);
                                Some((bitmask(out[0], bits), bits))
                            }
                        }
                    }
                    L::Jump { dest } => {
                        next_block = Some(*dest);
                        None
                    }
                    L::Brif {
                        then_dest,
                        else_dest,
                        ..
                    } => {
                        let (test, _) = get(0)?;
                        next_block = Some(if test != 0 { *then_dest } else { *else_dest });
                        None
                    }
                    L::Switch { cases, default } => {
                        let (test, bits) = get(0)?;
                        next_block = Some(
                            cases
                                .iter()
                                .find(|(case, _)| bitmask(*case as u64, bits) == test)
                                .map_or(*default, |(_, block)| *block),
                        );
                        None
                    }
                    L::Return => {
                        let returns = &source.signature.returns;
                        let text = match returns.as_slice() {
                            [only] if is_aggregate(only) => {
                                let (address, _) = get(0)?;
                                let size = only.bytes();
                                let bytes: Vec<u8> = (0..u64::from(size))
                                    .map(|i| world.byte(address + i))
                                    .collect();
                                returned_text(returns, [0, 0], &|_| bytes.clone())
                            }
                            _ => {
                                let mut registers = [0u64; 2];
                                for (k, register) in
                                    registers.iter_mut().enumerate().take(returns.len())
                                {
                                    *register = get(k)?.0;
                                }
                                returned_text(returns, registers, &|_| Vec::new())
                            }
                        };
                        return Err(text);
                    }
                    L::Trap => return Err("trap".into()),
                    other => return Err(format!("gt-unsupported source {other:?}")),
                })
            })();
            match def {
                Ok(Some(value)) => {
                    if let Some(result) = inst.results.first() {
                        vals.insert(*result, value);
                    }
                    if let (Some(overflow), Some(result)) = (second, inst.results.get(1)) {
                        vals.insert(*result, overflow);
                    }
                }
                Ok(None) => {}
                Err(end) => return end,
            }
            if next_block.is_some() {
                break;
            }
        }
        match next_block {
            Some(dest) => block = dest,
            None => return "fault: block without terminator".into(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Key {
    V(u32),
    P(u16),
}

/// An operand's register, the bits it names, and whether it is physical.
fn operand_reg(operand: &O) -> Option<(Key, u32)> {
    match operand {
        O::VReg(vreg) => Some((
            Key::V(vreg.id),
            match vreg.class {
                RegClass::Gpr64 => 64,
                RegClass::Gpr32 => 32,
                _ => return None,
            },
        )),
        O::PReg(preg) => {
            let e = preg.encoding();
            Some(match e {
                0..=15 => (Key::P(e), 64),
                16..=31 => (Key::P(e - 16), 32),
                32..=47 => (Key::P(e - 32), 16),
                48..=63 => (Key::P(e - 48), 8),
                _ => return None,
            })
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct Eflags {
    cf: bool,
    zf: bool,
    sf: bool,
    of: bool,
    pf: bool,
}

fn eflags_of(result: u64, bits: u32, cf: bool, of: bool) -> Eflags {
    let r = bitmask(result, bits);
    Eflags {
        cf,
        zf: r == 0,
        sf: (r >> (bits - 1)) & 1 == 1,
        of,
        pf: (r as u8).count_ones() % 2 == 0,
    }
}

fn condition(cc: X86CondCode, f: Eflags) -> bool {
    let code = cc as u8;
    let base = match code >> 1 {
        0 => f.of,
        1 => f.cf,
        2 => f.zf,
        3 => f.cf || f.zf,
        4 => f.sf,
        5 => f.pf,
        6 => f.sf != f.of,
        _ => f.zf || (f.sf != f.of),
    };
    if code & 1 == 1 { !base } else { base }
}

const ARG_REGS: [u16; 6] = [RDI, RSI, RDX, RCX, R8, R9];
const PRESERVED: [u16; 6] = [RBX, RBP, R12, R13, R14, R15];

/// Run the pre-RA machine stream on argument registers `raw`.
fn run_machine(
    machine: &X86ISelFunction,
    returns: &[Type],
    raw: &[u64],
    world: &mut World,
) -> String {
    let mut regs: HashMap<Key, u64> = HashMap::new();
    for (i, value) in raw.iter().enumerate().take(6) {
        regs.insert(Key::P(ARG_REGS[i]), *value);
    }
    for root in PRESERVED {
        regs.insert(Key::P(root), world.garbage(0xCA11_EE, u64::from(root)));
    }
    regs.insert(Key::P(RSP), 0x7fff_ffff_f000);
    let mut flags: Option<Eflags> = None;
    let order = &machine.block_order;
    let (mut bi, mut idx, mut steps) = (0usize, 0usize, 0u64);
    loop {
        steps += 1;
        if steps > 10_000 {
            return "fault: step limit".into();
        }
        let Some(block) = order.get(bi) else {
            return "fault: fell off the layout".into();
        };
        let insts = &machine.blocks[block].insts;
        let Some(inst) = insts.get(idx) else {
            bi += 1;
            idx = 0;
            continue;
        };
        idx += 1;
        let garbage = world.garbage(0x6A6A, steps);
        let read =
            |regs: &HashMap<Key, u64>, operand: &O, world: &World| -> Result<(u64, u32), String> {
                let (key, bits) =
                    operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
                let value = regs.get(&key).copied().unwrap_or_else(|| {
                    world.garbage(
                        0x0DEF,
                        steps
                            ^ (u64::from(match key {
                                Key::V(id) => id,
                                Key::P(p) => 100_000 + u32::from(p),
                            }) << 20),
                    )
                });
                Ok((bitmask(value, bits), bits))
            };
        // A write of `bits` bits: 64 is the whole root, 32 zero-extends; an
        // 8- or 16-bit write keeps the bits above in a physical register
        // (the hardware) and leaves garbage there in a virtual one (register
        // allocation treats it as a pure definition).
        let write = |regs: &mut HashMap<Key, u64>,
                     operand: &O,
                     bits: u32,
                     value: u64|
         -> Result<(), String> {
            let (key, _) =
                operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
            let above = match key {
                Key::P(_) => regs.get(&key).copied().unwrap_or(garbage),
                Key::V(_) => garbage,
            };
            let value = match bits {
                64 => value,
                32 => bitmask(value, 32),
                _ => (above & !bitmask(u64::MAX, bits)) | bitmask(value, bits),
            };
            regs.insert(key, value);
            Ok(())
        };
        let address =
            |regs: &HashMap<Key, u64>, operand: &O, world: &World| -> Result<u64, String> {
                match operand {
                    O::MemAddr { base, disp } => {
                        let base = match base.as_ref() {
                            O::StackSlot(slot) => slot_base(*slot),
                            other => read(regs, other, world)?.0,
                        };
                        Ok(base.wrapping_add(i64::from(*disp) as u64))
                    }
                    O::SibMemAddr {
                        base,
                        index,
                        scale,
                        disp,
                    } => {
                        let base = read(regs, base, world)?.0;
                        let index = read(regs, index, world)?.0;
                        Ok(base
                            .wrapping_add(index.wrapping_mul(u64::from(*scale)))
                            .wrapping_add(i64::from(*disp) as u64))
                    }
                    other => Err(format!("gt: address {other:?}")),
                }
            };
        let jump = |target: &O| -> Result<usize, String> {
            let O::Block(target) = target else {
                return Err("gt: jump operand".into());
            };
            order
                .iter()
                .position(|b| b == target)
                .ok_or_else(|| format!("fault: jump to unlaid block {target:?}"))
        };
        // The two-operand (tied) forms compute `d = d op x`.
        let ops: Vec<O> = match (inst.opcode, inst.operands.as_slice()) {
            (
                X86Opcode::OrRR
                | X86Opcode::AndRR
                | X86Opcode::XorRR
                | X86Opcode::AddRR
                | X86Opcode::SubRR
                | X86Opcode::ShlRI
                | X86Opcode::ShrRI
                | X86Opcode::SarRI
                | X86Opcode::AddRI
                | X86Opcode::SubRI
                | X86Opcode::AndRI
                | X86Opcode::OrRI
                | X86Opcode::XorRI,
                [d, x],
            ) => vec![d.clone(), d.clone(), x.clone()],
            _ => inst.operands.clone(),
        };
        let step: Result<Option<String>, String> = (|| {
            use X86Opcode as X;
            match inst.opcode {
                X::Nop => {}
                X::MovRR => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    let bits = operand_reg(&ops[0]).ok_or("gt")?.1;
                    write(&mut regs, &ops[0], bits, v)?;
                }
                X::MovRR32 => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], 32, v)?;
                }
                X::MovRI => {
                    let O::Imm(imm) = ops[1] else {
                        return Err("gt: MovRI".into());
                    };
                    let bits = operand_reg(&ops[0]).ok_or("gt")?.1;
                    write(&mut regs, &ops[0], bits, imm as u64)?;
                }
                X::Movzx | X::MovzxW | X::MovsxB | X::MovsxW | X::Movsx => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    let from = match inst.opcode {
                        X::Movzx | X::MovsxB => 8,
                        X::MovzxW | X::MovsxW => 16,
                        _ => 32,
                    };
                    let value = if matches!(inst.opcode, X::Movzx | X::MovzxW) {
                        bitmask(v, from)
                    } else {
                        sext(v, from)
                    };
                    write(&mut regs, &ops[0], 64, value)?;
                }
                X::AddRR
                | X::SubRR
                | X::ImulRR
                | X::AndRR
                | X::OrRR
                | X::XorRR
                | X::AddRI
                | X::SubRI
                | X::AndRI
                | X::OrRI
                | X::XorRI
                | X::ShlRI
                | X::ShrRI
                | X::SarRI => {
                    let bits = operand_reg(&ops[0]).ok_or("gt")?.1;
                    let (a, _) = read(&regs, &ops[1], world)?;
                    let b = match &ops[2] {
                        O::Imm(imm) => bitmask(i64::from(*imm as i32) as u64, bits),
                        other => read(&regs, other, world)?.0,
                    };
                    let shift = (b & if bits == 64 { 63 } else { 31 }) as u32;
                    let r = match inst.opcode {
                        X::AddRR | X::AddRI => a.wrapping_add(b),
                        X::SubRR | X::SubRI => a.wrapping_sub(b),
                        X::ImulRR => a.wrapping_mul(b),
                        X::AndRR | X::AndRI => a & b,
                        X::OrRR | X::OrRI => a | b,
                        X::XorRR | X::XorRI => a ^ b,
                        X::ShlRI => a << shift,
                        X::ShrRI => a >> shift,
                        _ => (sext(a, bits) as i64 >> shift) as u64,
                    };
                    let r = bitmask(r, bits);
                    let msb = |x: u64| (x >> (bits - 1)) & 1 == 1;
                    let imul_overflow = i128::from(sext(a, bits) as i64)
                        * i128::from(sext(b, bits) as i64)
                        != i128::from(sext(r, bits) as i64);
                    flags = match inst.opcode {
                        X::ImulRR => Some(Eflags {
                            cf: imul_overflow,
                            of: imul_overflow,
                            zf: garbage & 1 == 1,
                            sf: garbage & 2 == 2,
                            pf: garbage & 4 == 4,
                        }),
                        X::AddRR | X::AddRI => {
                            Some(eflags_of(r, bits, r < a, msb(!(a ^ b) & (a ^ r))))
                        }
                        X::SubRR | X::SubRI => {
                            Some(eflags_of(r, bits, a < b, msb((a ^ b) & (a ^ r))))
                        }
                        X::AndRR | X::AndRI | X::OrRR | X::OrRI | X::XorRR | X::XorRI => {
                            Some(eflags_of(r, bits, false, false))
                        }
                        _ if shift == 0 => flags,
                        _ => None,
                    };
                    write(&mut regs, &ops[0], bits, r)?;
                }
                X::Not => {
                    // Intel SDM NOT: no flag changes.
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], operand_reg(&ops[0]).ok_or("gt")?.1, !v)?;
                }
                X::ShlRR | X::ShrRR | X::SarRR => {
                    // Intel SDM SAL/SAR/SHL/SHR r/m, CL: the count is CL
                    // masked to 5 (32-bit) or 6 (64-bit) bits; a zero count
                    // leaves the flags, any other one sets them (read as
                    // garbage here).
                    let (a, bits) = read(&regs, &ops[1], world)?;
                    let cl = regs.get(&Key::P(RCX)).copied().unwrap_or(garbage) & 0xff;
                    let shift = (cl & if bits == 64 { 63 } else { 31 }) as u32;
                    let r = match inst.opcode {
                        X::ShlRR => a << shift,
                        X::ShrRR => a >> shift,
                        _ => (sext(a, bits) as i64 >> shift) as u64,
                    };
                    if shift != 0 {
                        flags = None;
                    }
                    write(
                        &mut regs,
                        &ops[0],
                        operand_reg(&ops[0]).ok_or("gt")?.1,
                        bitmask(r, bits),
                    )?;
                }
                X::Neg => {
                    // Intel SDM NEG: DEST := 0 - SRC; CF = (SRC != 0), OF, SF,
                    // ZF, PF from the result.
                    let (v, bits) = read(&regs, &ops[1], world)?;
                    let r = bitmask(0u64.wrapping_sub(v), bits);
                    let msb = |x: u64| (x >> (bits - 1)) & 1 == 1;
                    flags = Some(eflags_of(r, bits, v != 0, msb(v & r)));
                    write(&mut regs, &ops[0], operand_reg(&ops[0]).ok_or("gt")?.1, r)?;
                }
                X::Popcnt => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(
                        &mut regs,
                        &ops[0],
                        operand_reg(&ops[0]).ok_or("gt")?.1,
                        u64::from(v.count_ones()),
                    )?;
                    // Intel SDM POPCNT: ZF = (src == 0), the others cleared.
                    flags = Some(Eflags {
                        cf: false,
                        zf: v == 0,
                        sf: false,
                        of: false,
                        pf: false,
                    });
                }
                X::Mul => {
                    // Intel SDM MUL: EDX:EAX / RDX:RAX := EAX/RAX * src
                    // (unsigned), each 32-bit half zero-extended; CF = OF =
                    // (high half != 0); SF, ZF, AF, PF undefined.
                    let (source, bits) = read(&regs, &ops[0], world)?;
                    let accumulator =
                        bitmask(regs.get(&Key::P(RAX)).copied().unwrap_or(garbage), bits);
                    let product = u128::from(accumulator) * u128::from(source);
                    let low = bitmask(product as u64, bits);
                    let high = bitmask((product >> bits) as u64, bits);
                    regs.insert(Key::P(RAX), low);
                    regs.insert(Key::P(RDX), high);
                    flags = Some(Eflags {
                        cf: high != 0,
                        of: high != 0,
                        zf: garbage & 1 == 1,
                        sf: garbage & 2 == 2,
                        pf: garbage & 4 == 4,
                    });
                }
                X::Lea | X::LeaSib => {
                    let a = address(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], 64, a)?;
                }
                X::MovRM8 | X::MovRM16 | X::MovRM32 | X::MovRM => {
                    let a = address(&regs, &ops[1], world)?;
                    let bytes = match inst.opcode {
                        X::MovRM8 => 1,
                        X::MovRM16 => 2,
                        X::MovRM32 => 4,
                        _ => 8,
                    };
                    let v = world.read(a, bytes);
                    write(&mut regs, &ops[0], bytes * 8, v)?;
                }
                X::MovMR8 | X::MovMR16 | X::MovMR32 | X::MovMR => {
                    let a = address(&regs, &ops[0], world)?;
                    let bytes = match inst.opcode {
                        X::MovMR8 => 1,
                        X::MovMR16 => 2,
                        X::MovMR32 => 4,
                        _ => 8,
                    };
                    let (v, _) = read(&regs, &ops[1], world)?;
                    world.write(a, bytes, v);
                }
                X::CmpRR | X::CmpRI | X::TestRR | X::TestRI => {
                    let (a, bits) = read(&regs, &ops[0], world)?;
                    let b = match &ops[1] {
                        O::Imm(imm) => bitmask(i64::from(*imm as i32) as u64, bits),
                        other => read(&regs, other, world)?.0,
                    };
                    let msb = |x: u64| (x >> (bits - 1)) & 1 == 1;
                    flags = Some(if matches!(inst.opcode, X::CmpRR | X::CmpRI) {
                        let r = bitmask(a.wrapping_sub(b), bits);
                        eflags_of(r, bits, a < b, msb((a ^ b) & (a ^ r)))
                    } else {
                        eflags_of(a & b, bits, false, false)
                    });
                }
                X::Setcc => {
                    let O::CondCode(cc) = ops[1] else {
                        return Err("gt: setcc".into());
                    };
                    let holds = flags.map_or(garbage & 1 == 1, |f| condition(cc, f));
                    write(&mut regs, &ops[0], 8, u64::from(holds))?;
                }
                X::Cmovcc | X::Cmovcc32 => {
                    let O::CondCode(cc) = ops[2] else {
                        return Err("gt: cmov".into());
                    };
                    let holds = flags.map_or(garbage & 1 == 1, |f| condition(cc, f));
                    let bits = if inst.opcode == X::Cmovcc { 64 } else { 32 };
                    let value = if holds {
                        read(&regs, &ops[1], world)?.0
                    } else {
                        read(&regs, &ops[0], world)?.0
                    };
                    write(&mut regs, &ops[0], bits, value)?;
                }
                X::Call | X::CallR => {
                    // `call symbol`, or `call r64`: the function the
                    // register's 64 bits name.
                    let name = match &ops[0] {
                        O::Symbol(name) => name.clone(),
                        register if inst.opcode == X::CallR => {
                            format!("fn@{:#x}", read(&regs, register, world)?.0)
                        }
                        _ => return Err("gt: call operand".into()),
                    };
                    let registers: Vec<u64> = ARG_REGS
                        .iter()
                        .enumerate()
                        .map(|(i, root)| {
                            regs.get(&Key::P(*root))
                                .copied()
                                .unwrap_or_else(|| world.garbage(0xA59, steps * 8 + i as u64))
                        })
                        .collect();
                    let out = world
                        .call(&name, &registers, steps)
                        .map_err(|e| format!("fault: {e}"))?;
                    for (k, root) in [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11]
                        .iter()
                        .enumerate()
                    {
                        regs.insert(Key::P(*root), world.garbage(0xC10B, steps * 16 + k as u64));
                    }
                    regs.insert(Key::P(RAX), out[0]);
                    regs.insert(Key::P(RDX), out[1]);
                    flags = None;
                }
                X::Jcc => {
                    let O::CondCode(cc) = ops[0] else {
                        return Err("gt: jcc".into());
                    };
                    let holds = flags.map_or(garbage & 1 == 1, |f| condition(cc, f));
                    if holds {
                        bi = jump(&ops[1])?;
                        idx = 0;
                    }
                }
                X::Jmp => {
                    bi = jump(&ops[0])?;
                    idx = 0;
                }
                X::Ud2 => return Ok(Some("trap".into())),
                X::Ret => {
                    for root in PRESERVED {
                        if regs.get(&Key::P(root)).copied()
                            != Some(world.garbage(0xCA11_EE, u64::from(root)))
                        {
                            return Ok(Some(format!("fault: callee-saved root {root} clobbered")));
                        }
                    }
                    let read_root = |root: u16| {
                        regs.get(&Key::P(root))
                            .copied()
                            .unwrap_or_else(|| world.garbage(0x2E7, u64::from(root)))
                    };
                    let registers = [read_root(RAX), read_root(RDX)];
                    let text = match returns {
                        [only] if is_aggregate(only) => {
                            let bytes: Vec<u8> = eightbytes(only.bytes())
                                .into_iter()
                                .enumerate()
                                .flat_map(|(k, (_, n))| {
                                    (0..n).map(move |i| (registers[k] >> (8 * i)) as u8)
                                })
                                .collect();
                            returned_text(returns, registers, &|_| bytes.clone())
                        }
                        _ => returned_text(returns, registers, &|_| Vec::new()),
                    };
                    return Ok(Some(text));
                }
                other => return Err(format!("gt-unsupported machine {other:?}")),
            }
            Ok(None)
        })();
        match step {
            Ok(Some(end)) => return end,
            Ok(None) => {}
            Err(end) => return end,
        }
    }
}

/// Ground truth: the first input on which the machine differs from the
/// source, or why the interpreter cannot judge.
#[derive(Debug, Clone, Default)]
struct Truth {
    wrong: Option<String>,
    unsupported: Option<String>,
}

fn ground_truth(shape: InsnShape, source: &Function, machine: &X86ISelFunction) -> Truth {
    let mut truth = Truth::default();
    for seed in 0..GT_INPUTS {
        let raw = gt_registers(seed);
        let mut world = World::new(seed, shape);
        let end = run_source(source, &raw, &mut world);
        // Undefined behavior of the source: every machine behavior refines
        // it, so this input judges nothing.
        if end == "ub" {
            continue;
        }
        let expected = world.finish(end);
        let mut world = World::new(seed, shape);
        let end = run_machine(machine, &source.signature.returns, &raw, &mut world);
        let found = world.finish(end);
        for end in [&expected.end, &found.end] {
            if end.starts_with("gt-unsupported") || end.starts_with("gt:") {
                truth.unsupported = Some(end.clone());
                return truth;
            }
        }
        if expected != found {
            truth.wrong = Some(format!(
                "seed {seed}: source {:?} / machine {:?}",
                (expected.end, expected.calls, expected.accesses),
                (found.end, found.calls, found.accesses)
            ));
            break;
        }
    }
    truth
}

// ---------------------------------------------------------------------------
// Mutations
// ---------------------------------------------------------------------------

const CLASSES: [&str; 9] = [
    "C0 original",
    "C1 wrong condition code",
    "C2 operands swapped",
    "C3 wrong operation",
    "C4 ABI or implicit register replaced",
    "C5 wrong source register",
    "C6 row dropped",
    "C7 wrong immediate",
    "C8 signedness or width of the flag reader",
];

struct Mutant {
    class: usize,
    label: String,
    machine: X86ISelFunction,
}

/// The ABI register a physical operand names, as its 64-bit root.
fn abi_root(operand: &O) -> Option<u16> {
    match operand_reg(operand) {
        Some((Key::P(root), _))
            if ARG_REGS.contains(&root) || root == RAX || root == RDX || root == RCX =>
        {
            Some(root)
        }
        _ => None,
    }
}

/// `operand` with its physical root replaced by `root` at the same width.
fn with_root(operand: &O, root: u16) -> Option<O> {
    let O::PReg(preg) = operand else {
        return None;
    };
    let base = preg.encoding() / 16 * 16;
    Some(O::PReg(X86PReg::new(base + root)))
}

const ALL_CONDITIONS: [X86CondCode; 16] = [
    X86CondCode::O,
    X86CondCode::NO,
    X86CondCode::B,
    X86CondCode::AE,
    X86CondCode::E,
    X86CondCode::NE,
    X86CondCode::BE,
    X86CondCode::A,
    X86CondCode::S,
    X86CondCode::NS,
    X86CondCode::P,
    X86CondCode::NP,
    X86CondCode::L,
    X86CondCode::GE,
    X86CondCode::LE,
    X86CondCode::G,
];

fn mutants(base: &X86ISelFunction) -> Vec<Mutant> {
    let mut out: Vec<Mutant> = Vec::new();
    let mut push = |class: usize, label: String, machine: X86ISelFunction| {
        out.push(Mutant {
            class,
            label,
            machine,
        });
    };
    push(0, "original".into(), base.clone());
    let all = rows(base);
    // The flag writers this slice models: a reader after one of them reads
    // its flags.
    let flag_writer = |opcode: X86Opcode| {
        matches!(
            opcode,
            X86Opcode::AddRR | X86Opcode::SubRR | X86Opcode::ImulRR | X86Opcode::Mul
        )
    };
    for (ordinal, _, _) in &all {
        let ordinal = *ordinal;
        let row = inst(base, ordinal).clone();
        // C1: a flag reader's condition replaced by every other one. (C8 is
        // the reader of a modelled writer: the condition with the other
        // signedness or reading only flags the writer leaves undefined.)
        if let Some(k) = row
            .operands
            .iter()
            .position(|operand| matches!(operand, O::CondCode(_)))
        {
            let O::CondCode(cc) = row.operands[k] else {
                unreachable!()
            };
            let after_writer = (0..ordinal)
                .rev()
                .map(|o| inst(base, o).opcode)
                .find(|opcode| {
                    flag_writer(*opcode)
                        || matches!(
                            opcode,
                            X86Opcode::CmpRR
                                | X86Opcode::CmpRI
                                | X86Opcode::TestRR
                                | X86Opcode::TestRI
                        )
                })
                .is_some_and(flag_writer);
            for other in ALL_CONDITIONS {
                if other == cc {
                    continue;
                }
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[k] = O::CondCode(other);
                let class = if after_writer { 8 } else { 1 };
                push(class, format!("row {ordinal}: {other:?} (was {cc:?})"), m);
            }
        }
        // C2: the two source operands of a three-address row swapped.
        if matches!(
            row.opcode,
            X86Opcode::AddRR | X86Opcode::SubRR | X86Opcode::ImulRR | X86Opcode::CmpRR
        ) {
            let mut m = base.clone();
            let r = inst_mut(&mut m, ordinal);
            let n = r.operands.len();
            r.operands.swap(n - 2, n - 1);
            push(
                2,
                format!("row {ordinal}: {:?} operands swapped", row.opcode),
                m,
            );
        }
        // C3: another operation of the same shape.
        let others: &[X86Opcode] = match row.opcode {
            X86Opcode::AddRR => &[X86Opcode::SubRR, X86Opcode::ImulRR, X86Opcode::OrRR],
            X86Opcode::SubRR => &[X86Opcode::AddRR, X86Opcode::XorRR],
            X86Opcode::ImulRR => &[X86Opcode::AddRR, X86Opcode::SubRR],
            X86Opcode::Not => &[X86Opcode::MovRR, X86Opcode::Popcnt, X86Opcode::Neg],
            X86Opcode::Neg => &[X86Opcode::MovRR, X86Opcode::Not],
            X86Opcode::Popcnt => &[X86Opcode::MovRR, X86Opcode::Not],
            X86Opcode::AndRI => &[X86Opcode::OrRI, X86Opcode::XorRI],
            // Signed for unsigned, and the other direction of shift.
            X86Opcode::ShlRR => &[X86Opcode::ShrRR, X86Opcode::SarRR],
            X86Opcode::ShrRR => &[X86Opcode::SarRR, X86Opcode::ShlRR],
            X86Opcode::SarRR => &[X86Opcode::ShrRR, X86Opcode::ShlRR],
            X86Opcode::Movzx => &[X86Opcode::MovsxB],
            X86Opcode::MovsxB => &[X86Opcode::Movzx],
            X86Opcode::MovzxW => &[X86Opcode::MovsxW],
            X86Opcode::MovsxW => &[X86Opcode::MovzxW],
            _ => &[],
        };
        for other in others {
            let mut m = base.clone();
            let r = inst_mut(&mut m, ordinal);
            r.opcode = *other;
            r.flags = other.default_flags();
            push(
                3,
                format!("row {ordinal}: {other:?} (was {:?})", row.opcode),
                m,
            );
        }
        // C4: an ABI or implicit register operand (an argument register,
        // RAX, RDX, RCX) replaced by another of the same width.
        for (k, operand) in row.operands.iter().enumerate() {
            let Some(root) = abi_root(operand) else {
                continue;
            };
            for other in [RDI, RSI, RDX, RAX, RCX] {
                if other == root {
                    continue;
                }
                let Some(replaced) = with_root(operand, other) else {
                    continue;
                };
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[k] = replaced;
                push(
                    4,
                    format!(
                        "row {ordinal} operand {k}: {} for {}",
                        ROOT_NAMES[other as usize], ROOT_NAMES[root as usize]
                    ),
                    m,
                );
            }
        }
        // C5: a source register (the last register operand: `mul`'s and
        // `call r64`'s only one) replaced by another virtual register of the
        // same class defined earlier.
        if let Some(k) = row
            .operands
            .iter()
            .rposition(|operand| matches!(operand, O::VReg(_)))
            && (k > 0 || matches!(row.opcode, X86Opcode::Mul | X86Opcode::CallR))
        {
            let O::VReg(v) = row.operands[k] else {
                unreachable!()
            };
            let earlier: Vec<VReg> = all
                .iter()
                .take(ordinal)
                .filter_map(|(o, _, _)| match inst(base, *o).operands.first() {
                    Some(O::VReg(d)) if d.class == v.class && d.id != v.id => Some(*d),
                    _ => None,
                })
                .collect();
            for other in earlier.into_iter().rev().take(3) {
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[k] = O::VReg(other);
                push(5, format!("row {ordinal}: v{} for v{}", other.id, v.id), m);
            }
        }
        // C6: a value row dropped.
        if !matches!(
            row.opcode,
            X86Opcode::Jmp
                | X86Opcode::Jcc
                | X86Opcode::Ret
                | X86Opcode::Call
                | X86Opcode::CallR
                | X86Opcode::Ud2
        ) {
            let mut m = base.clone();
            remove_at(&mut m, ordinal);
            push(6, format!("row {ordinal} ({:?}) dropped", row.opcode), m);
        }
        // C7: another immediate.
        if let Some(k) = row
            .operands
            .iter()
            .position(|operand| matches!(operand, O::Imm(_)))
        {
            let O::Imm(imm) = row.operands[k] else {
                unreachable!()
            };
            for other in [imm ^ 1, imm >> 1, imm.wrapping_add(0x100), -1, 0] {
                if other == imm || i32::try_from(other).is_err() {
                    continue;
                }
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[k] = O::Imm(other);
                push(
                    7,
                    format!("row {ordinal}: imm {other:#x} (was {imm:#x})"),
                    m,
                );
            }
        }
    }
    let mut seen = HashSet::new();
    out.retain(|m| seen.insert(describe(&m.machine)));
    out
}

// ---------------------------------------------------------------------------
// The probe
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct Tally {
    n: usize,
    unsupported: usize,
    mismatch: usize,
    theorem: usize,
    sample_refuted: usize,
    ay_ce: usize,
    ay_valid: usize,
    ay_other: usize,
    credited: usize,
    wrong: usize,
    wrong_unsupported: usize,
    wrong_mismatch: usize,
    wrong_refuted: usize,
    wrong_credited: usize,
    ay_ce_not_sampled: usize,
    correct_refuted: usize,
    gt_na: usize,
}

struct Probe {
    table: Vec<Tally>,
    findings: Vec<String>,
    conservative: Vec<String>,
    ay_cache: HashMap<String, String>,
}

fn optimized_bases(selected: &X86ISelFunction) -> Vec<(String, X86ISelFunction)> {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut bases = vec![("O0".to_owned(), selected.clone())];
    for (name, opt_level) in [
        ("O1", trust_cg_opt::OptLevel::O1),
        ("O2", trust_cg_opt::OptLevel::O2),
        ("O3", trust_cg_opt::OptLevel::O3),
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        let mut machine = selected.clone();
        pipeline.run_x86_optimization_passes(&mut machine);
        if bases.iter().all(|(_, b)| describe(b) != describe(&machine)) {
            bases.push((name.to_owned(), machine));
        }
    }
    bases
}

fn probe(replay: bool, only: Option<&str>) -> Probe {
    let mut probe = Probe {
        table: vec![Tally::default(); CLASSES.len()],
        findings: Vec::new(),
        conservative: Vec::new(),
        ay_cache: HashMap::new(),
    };
    let verifier = promotion_verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let fresh = FunctionVerificationRequest::capture(
        VerificationConfig::for_proof_promotion(),
        ProvenanceXCheckMode::Enforce,
    );
    for shape in all_slice_ten_shapes() {
        if only.is_some_and(|only| !format!("{shape:?}").contains(only)) {
            continue;
        }
        let (source, selected) = slice10_pair(shape);
        for (level, base) in &optimized_bases(&selected) {
            for mutant in mutants(base) {
                let row = &mut probe.table[mutant.class];
                row.n += 1;
                let tag = format!(
                    "{shape:?}@{level} [{}] {}",
                    CLASSES[mutant.class], mutant.label
                );
                let truth = ground_truth(shape, &source, &mutant.machine);
                if let Some(reason) = &truth.unsupported {
                    row.gt_na += 1;
                    eprintln!("ROB10 GT-NA {tag}: {reason}");
                }
                let wrong = truth.wrong.is_some();
                if wrong {
                    row.wrong += 1;
                }
                if mutant.class == 0 && (wrong || truth.unsupported.is_some()) {
                    probe.findings.push(format!(
                        "ORIGINAL judged wrong/NA by GT {tag}: {truth:?}\n{}",
                        describe(&mutant.machine)
                    ));
                }
                let body = match source_bound_x86_body(&source, &mutant.machine, SYSV) {
                    Err(X86BodyRefusal::Unsupported(reason)) => {
                        row.unsupported += 1;
                        if wrong {
                            row.wrong_unsupported += 1;
                        }
                        eprintln!("ROB10 {tag}: unsupported ({reason}) gt_wrong={wrong}");
                        continue;
                    }
                    Err(other) => {
                        row.mismatch += 1;
                        if wrong {
                            row.wrong_mismatch += 1;
                        } else if mutant.class != 0 && truth.unsupported.is_none() {
                            probe
                                .conservative
                                .push(format!("mismatch on GT-correct {tag}: {other}"));
                        }
                        eprintln!("ROB10 {tag}: mismatch ({other}) gt_wrong={wrong}");
                        continue;
                    }
                    Ok(body) => body,
                };
                row.theorem += 1;
                let sample_refuted = theorem_refuted(body.obligation());
                if sample_refuted {
                    row.sample_refuted += 1;
                }
                let mut credited = false;
                let mut ay = String::from("not replayed");
                if replay {
                    let smt2 = generate_smt2_query_raw(body.obligation(), &replay_config());
                    ay = match probe.ay_cache.get(&smt2) {
                        Some(cached) => cached.clone(),
                        None => {
                            let result = fresh
                                .ay()
                                .verify_fresh_source_bound(&body, &replay_config());
                            let text = match &result {
                                AYResult::Verified => "Verified".to_owned(),
                                AYResult::CounterExample(_) => "CounterExample".to_owned(),
                                other => stable_outcome(other),
                            };
                            probe.ay_cache.insert(smt2, text.clone());
                            text
                        }
                    };
                    match ay.as_str() {
                        "Verified" => row.ay_valid += 1,
                        "CounterExample" => {
                            row.ay_ce += 1;
                            if !sample_refuted {
                                row.ay_ce_not_sampled += 1;
                                probe.findings.push(format!(
                                    "AY refutes but the sampler does not {tag}\n{}",
                                    describe(&mutant.machine)
                                ));
                            }
                        }
                        _ => row.ay_other += 1,
                    }
                    let (report, exports) = verifier.verify_with_request_for_export(
                        &mutant.machine,
                        Some(&source),
                        SYSV,
                        &request,
                    );
                    let covered = body.bound_rows().len();
                    let formal = covered_rows_matching(&body, report.report(), is_body_credit);
                    credited = covered > 0 && formal == covered && !exports.is_empty();
                    if formal > 0 && !credited {
                        probe
                            .findings
                            .push(format!("PARTIAL body credit {formal}/{covered} {tag}"));
                    }
                    if credited {
                        row.credited += 1;
                    }
                    if ay == "Verified" && sample_refuted {
                        probe.findings.push(format!(
                            "AY Verified but sample-refuted {tag}\n{}",
                            describe(&mutant.machine)
                        ));
                    }
                }
                if wrong {
                    if sample_refuted || ay == "CounterExample" {
                        row.wrong_refuted += 1;
                    }
                    if credited || ay == "Verified" || (!replay && !sample_refuted) {
                        row.wrong_credited += 1;
                        probe.findings.push(format!(
                            "CREDITED/VALID BUT WRONG {tag} ay={ay} credited={credited} sample_refuted={sample_refuted}\nGT: {truth:?}\n{}",
                            describe(&mutant.machine)
                        ));
                    }
                } else if (sample_refuted || ay == "CounterExample") && mutant.class != 0 {
                    row.correct_refuted += 1;
                    probe
                        .conservative
                        .push(format!("refuted but GT-correct {tag} (ay={ay})"));
                } else if mutant.class == 0 && replay && !credited {
                    probe
                        .findings
                        .push(format!("original not credited {tag} ay={ay}"));
                }
                eprintln!(
                    "ROB10 {tag}: theorem sample_refuted={sample_refuted} ay={ay} credited={credited} gt_wrong={wrong}"
                );
            }
        }
    }
    probe
}

#[test]
#[ignore]
fn slice_ten_mutation_robustness() {
    let test = "slice_ten_mutation_robustness";
    let only = std::env::var("ROB10_ONLY").ok();
    let edits = if std::env::var_os("ROB10_NO_REPLAY").is_some() {
        None
    } else {
        replay_environment(test)
    };
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let probe = match &edits {
        Some(edits) => with_edits(edits, || probe(true, only.as_deref())),
        None => without_replay(|| probe(false, only.as_deref())),
    };
    eprintln!(
        "\nROB10 TABLE replay={} (n | owner unsupported | owner mismatch | theorem | sample-refuted | AY CE | AY CE not sampled | AY Valid | AY other | credited || GT-wrong: total / unsupported / mismatch / refuted / CREDITED-or-VALID || GT-correct but refuted | GT n/a)",
        edits.is_some()
    );
    for (class, row) in CLASSES.iter().zip(&probe.table) {
        eprintln!(
            "ROB10 {class:<34} {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} || {:>4} / {:>4} / {:>4} / {:>4} / {:>4} || {:>4} | {:>3}",
            row.n,
            row.unsupported,
            row.mismatch,
            row.theorem,
            row.sample_refuted,
            row.ay_ce,
            row.ay_ce_not_sampled,
            row.ay_valid,
            row.ay_other,
            row.credited,
            row.wrong,
            row.wrong_unsupported,
            row.wrong_mismatch,
            row.wrong_refuted,
            row.wrong_credited,
            row.correct_refuted,
            row.gt_na
        );
    }
    eprintln!("ROB10 conservative ({}):", probe.conservative.len());
    for line in &probe.conservative {
        eprintln!("ROB10-C {line}");
    }
    eprintln!("ROB10 findings ({}):", probe.findings.len());
    for line in &probe.findings {
        eprintln!("ROB10-F {line}");
    }
}
