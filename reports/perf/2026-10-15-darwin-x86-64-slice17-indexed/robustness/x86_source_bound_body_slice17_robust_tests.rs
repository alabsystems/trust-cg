// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Robustness probe of slice 17 (private stack accesses at a non-constant
//! offset): mutate the real machine streams of the slice-17 fixtures (O0
//! selection and the x86 optimizer at O1-O3) where they form and use indexed
//! addresses (the index register swapped with another live register, the
//! stride constant changed, the displacement changed, the base slot changed,
//! the index's extension dropped or changed, a bounds check's `jcc`
//! inverted), judge every mutant with the owner, the solver-free sampler of
//! the library gate (`slice9::dag_refuted_on_samples`), and (unless
//! `ROB17_NO_REPLAY`) the replayed theorem (admitted AY --strict-proofs +
//! Clean) and the verifier's crediting, and compare with an INDEPENDENT
//! concrete interpreter of the LIR and of the pre-RA x86 stream (ground
//! truth), slice 12's (`robustness/` of the slice-12 report) with the
//! slice-17 callees. Diagnostic only (ignored).
//!
//! Ground truth. Both streams run on the same argument registers and world;
//! private slots live at fixed addresses (an out-of-bounds access reads or
//! writes whatever lies there, as hardware would); a callee is a
//! deterministic pseudo-random function of (its name, its arguments' defined
//! bits, and the bytes it reads through a pointer): `write_digit(p, d)`
//! writes the byte `d` at `p`; `finish(p, n)` reads the 8 bytes at `p`;
//! `fill(p)` writes 160 pseudo-random bytes at `p` and `sum(p)` reads them;
//! `fill_ptrs(p)` writes four pointers into incoming memory; `memset(p, b,
//! n)` writes `n` bytes. The source runs at most `SOURCE_STEPS` LIR
//! instructions and the machine at most `MACHINE_STEPS` rows. Observables:
//! the returned bits, the trap, the call log, the incoming accesses and final
//! incoming memory, and the callee-saved registers. `F64Table` is left out
//! (the interpreters model no SSE register).

use super::slice5::describe;
use super::slice9::dag_refuted_on_samples;
use super::slice17::{IndexShape, SLICE_SEVENTEEN, slice17_pair};
use super::*;
use std::collections::BTreeMap;
use trust_cg_ir::X86CondCode;

const SLOT_BASE: u64 = 0x7ff0_0000_0000;
const SLOT_STRIDE: u64 = 0x1_0000;
const PARAM_BASE: u64 = 0x7fe0_0000_0000;
const RESULT_BASE: u64 = 0x7fd0_0000_0000;
const GT_INPUTS: u64 = 400;
/// The ground truth's bound on a source run (LIR instructions) and on a
/// machine run (rows).
const SOURCE_STEPS: u64 = 2_000;
const MACHINE_STEPS: u64 = 20 * SOURCE_STEPS;
/// The machine's bound where the source has not ended: a machine that ends
/// within it makes the vector undecided.
const UNENDED_STEPS: u64 = 4 * SOURCE_STEPS;
/// Where the machine ends after R rows and the source has not, the source
/// runs again with a bound of `RETRY_FACTOR * R` LIR instructions (a correct
/// stream of these fixtures runs at least one row per LIR instruction of
/// the source it matches, but for an `Iconst` or a `Copy` it folds; nested
/// loops do quadratic work on a modest bound).
const RETRY_FACTOR: u64 = 8;

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
#[derive(Clone, Copy, Debug)]
enum Kind {
    Scalar(u32),
    Aggregate(u32),
}

fn callee(name: &str) -> Option<(&'static [Kind], Option<Kind>)> {
    use Kind::*;
    Some(match name {
        "take4" => (&[Aggregate(4)], Some(Scalar(64))),
        "give2" => (&[Scalar(64)], Some(Aggregate(8))),
        "take2" => (&[Aggregate(16)], Some(Scalar(64))),
        "give2w" => (&[Scalar(64)], Some(Aggregate(16))),
        "give1" => (&[Scalar(64)], Some(Aggregate(4))),
        "g1" => (&[Scalar(64)], Some(Scalar(64))),
        "panic_at" => (&[Scalar(64), Scalar(64)], None),
        "tick" => (&[], None),
        "step" => (&[Scalar(64)], Some(Scalar(1))),
        // A `bool` argument: the backend's clean 32-bit carrier.
        "take_bool" => (&[Scalar(32)], None),
        // Slice 17.
        "panic_bounds" => (&[Scalar(64), Scalar(64)], None),
        "write_digit" => (&[Scalar(64), Scalar(32)], None),
        "finish" => (&[Scalar(64), Scalar(64)], Some(Scalar(64))),
        "fill" => (&[Scalar(64)], None),
        "sum" => (&[Scalar(64)], Some(Scalar(64))),
        "peek" => (&[Scalar(64)], None),
        "assume" => (&[Scalar(32)], None),
        "fill_ptrs" => (&[Scalar(64)], None),
        "memset" => (&[Scalar(64), Scalar(32), Scalar(64)], None),
        _ => return None,
    })
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
}

fn is_private(address: u64) -> bool {
    address >= RESULT_BASE
}

impl World {
    fn new(seed: u64) -> Self {
        Self {
            seed,
            mem: HashMap::new(),
            calls: Vec::new(),
            accesses: Vec::new(),
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
        let (params, result) = callee(name).ok_or_else(|| format!("unknown callee {name}"))?;
        let mut key = mix(name_hash(name), 0x5151);
        let _ = &mut key;
        let mut log = format!("{name}(");
        let mut next = 0usize;
        for param in params {
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
        // Slice 17: the callees' memory effects, and the bytes they read.
        match name {
            "write_digit" => self.write(registers[0], 1, registers[1] & 0xff),
            "finish" => key = mix(key, self.read(registers[0], 8)),
            "sum" => {
                for k in 0..20 {
                    key = mix(key, self.read(registers[0].wrapping_add(8 * k), 8));
                }
            }
            "fill" => {
                for k in 0..20 {
                    let word = splitmix(key ^ (k + 1));
                    self.write(registers[0].wrapping_add(8 * k), 8, word);
                }
            }
            "fill_ptrs" => {
                for k in 0..4 {
                    let pointer = 0x1000_0000 + 0x100 * k + (key & 0xf0);
                    self.write(registers[0].wrapping_add(8 * k), 8, pointer);
                }
            }
            "memset" => {
                for k in 0..registers[2].min(4096) {
                    self.write(registers[0].wrapping_add(k), 1, registers[1] & 0xff);
                }
            }
            _ => {}
        }
        // `step(p)`: decrement the word at `p`, return whether it was not 0.
        if name == "step" {
            let address = registers[0];
            let before = self.read(address, 8);
            self.write(address, 8, before.wrapping_sub(1));
            let garbage = self.garbage(0xC10B, step * 2);
            return Ok([
                (garbage & !0xff) | u64::from(before != 0),
                self.garbage(0xC10B, step * 2 + 1),
            ]);
        }
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

thread_local! {
    /// Whether the run models a psABI caller (a `bool` result read at 8
    /// bits) rather than the backend's clean-bool caller (32 bits).
    static PSABI: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The rows the last machine run executed.
    static MACHINE_ROWS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The return bits a caller reads of a scalar result of type `ty`.
fn return_bits(ty: &Type) -> u32 {
    match ty {
        Type::B1 if PSABI.with(|psabi| psabi.get()) => 8,
        Type::B1 | Type::I32 => 32,
        Type::I8 => 8,
        Type::I16 => 16,
        _ => 64,
    }
}

/// Raw argument registers (RDI, RSI, ...): random words of varied density.
fn gt_registers(seed: u64) -> Vec<u64> {
    (0..6)
        .map(|i| {
            let r = mix(seed, 0xA000 + i);
            match seed % 7 {
                0 => r % 16,
                1 => r & 0x00ff_00ff_00ff_00ff,
                2 => r & 0xffff_0000_ffff_0000,
                3 => r | (1 << 63),
                4 => r % 24,
                5 => r % 4,
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

/// Run the LIR source on argument registers `raw`.
fn run_source(source: &Function, raw: &[u64], world: &mut World, budget: u64) -> String {
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
            if steps > budget {
                return "fault: step limit".into();
            }
            let get = |k: usize| -> Result<(u64, u32), String> {
                inst.args
                    .get(k)
                    .and_then(|value| vals.get(value).copied())
                    .ok_or_else(|| format!("fault: undefined operand of {:?}", inst.opcode))
            };
            let def: Result<Option<(u64, u32)>, String> = (|| {
                Ok(match &inst.opcode {
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
                    // Slice 17: the C runtime's `memset`, a call like any.
                    L::Memset => {
                        let registers = vec![get(0)?.0, get(1)?.0, get(2)?.0];
                        world
                            .call("memset", &registers, 1000 + index as u64)
                            .map_err(|e| format!("fault: {e}"))?;
                        None
                    }
                    other => return Err(format!("gt-unsupported source {other:?}")),
                })
            })();
            match def {
                Ok(Some(value)) => {
                    if let Some(result) = inst.results.first() {
                        vals.insert(*result, value);
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
    budget: u64,
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
        MACHINE_ROWS.with(|cell| cell.set(steps));
        if steps > budget {
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
                    flags = match inst.opcode {
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
                X::MovzxRM8 | X::MovzxRM16 => {
                    let a = address(&regs, &ops[1], world)?;
                    let bytes = if inst.opcode == X::MovzxRM8 { 1 } else { 2 };
                    let v = world.read(a, bytes);
                    write(&mut regs, &ops[0], 64, bitmask(v, bytes * 8))?;
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
                X::BtRI => {
                    // Intel SDM BT: CF is the selected bit (the offset
                    // modulo the operand width), ZF is unaffected, OF, SF
                    // and PF are undefined (garbage here).
                    let (a, bits) = read(&regs, &ops[0], world)?;
                    let O::Imm(imm) = ops[1] else {
                        return Err("gt: bt".into());
                    };
                    let bit = (a >> ((imm as u64) % u64::from(bits))) & 1 == 1;
                    flags = Some(Eflags {
                        cf: bit,
                        zf: flags.map_or(garbage & 2 == 2, |f| f.zf),
                        sf: garbage & 4 == 4,
                        of: garbage & 8 == 8,
                        pf: garbage & 16 == 16,
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
                X::Call => {
                    let O::Symbol(name) = &ops[0] else {
                        return Err("gt: call operand".into());
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
                        .call(name, &registers, steps)
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
    undecided: Option<String>,
}

/// The constants of both streams (the source's `Iconst`s and `Switch` cases,
/// the machine's immediates) and their neighbours: the boundary inputs that
/// random words miss (a case of 70, a compare against 69, `<` against `<=`).
fn boundary_pool(source: &Function, machine: &X86ISelFunction) -> Vec<u64> {
    let mut constants: Vec<u64> = vec![0];
    for body in source.blocks.values() {
        for inst in &body.instructions {
            match &inst.opcode {
                L::Iconst { imm, .. } => constants.push(*imm as u64),
                L::Switch { cases, .. } => {
                    constants.extend(cases.iter().map(|(case, _)| *case as u64))
                }
                _ => {}
            }
        }
    }
    for (ordinal, _, _) in rows(machine) {
        for operand in &inst(machine, ordinal).operands {
            if let O::Imm(imm) = operand {
                constants.push(*imm as u64);
            }
        }
    }
    let mut pool: Vec<u64> = constants
        .iter()
        .flat_map(|c| [c.wrapping_sub(1), *c, c.wrapping_add(1)])
        .collect();
    pool.sort_unstable();
    pool.dedup();
    pool
}

/// Directed argument registers: register `(j / n) % 6` walks the pool, the
/// others take pool values pseudo-randomly.
fn gt_boundary_registers(pool: &[u64], j: u64) -> Vec<u64> {
    let n = pool.len() as u64;
    let walker = (j / n) % 6;
    (0..6)
        .map(|i| {
            if i == walker {
                pool[(j % n) as usize]
            } else {
                pool[(mix(j, 0xB000 + i) % n) as usize]
            }
        })
        .collect()
}

fn ground_truth(source: &Function, machine: &X86ISelFunction) -> Truth {
    let mut truth = Truth::default();
    let pool = boundary_pool(source, machine);
    // Every pool value at every register twice (with different partners).
    let directed = 12 * pool.len() as u64;
    for seed in 0..2 * (GT_INPUTS + directed) {
        // Even seeds: the clean-bool caller; odd: the psABI caller.
        let psabi = seed % 2 == 1;
        PSABI.with(|cell| cell.set(psabi));
        let mut raw = if seed / 2 < GT_INPUTS {
            gt_registers(seed / 2)
        } else {
            gt_boundary_registers(&pool, seed / 2 - GT_INPUTS)
        };
        for (i, ty) in source.signature.params.iter().enumerate().take(6) {
            if *ty == Type::B1 {
                raw[i] = if psabi {
                    (raw[i] & !0xff) | (raw[i] & 1)
                } else {
                    raw[i] & 1
                };
            }
        }
        let mut world = World::new(seed);
        let end = run_source(source, &raw, &mut world, SOURCE_STEPS);
        let mut unended = end == "fault: step limit";
        let mut expected = world.finish(end);
        let mut world = World::new(seed);
        let budget = if unended {
            UNENDED_STEPS
        } else {
            MACHINE_STEPS
        };
        let end = run_machine(machine, &source.signature.returns, &raw, &mut world, budget);
        let found = world.finish(end);
        let rows = MACHINE_ROWS.with(std::cell::Cell::get);
        if unended && found.end != "fault: step limit" && RETRY_FACTOR * rows > SOURCE_STEPS {
            let mut world = World::new(seed);
            let end = run_source(source, &raw, &mut world, RETRY_FACTOR * rows);
            unended = end == "fault: step limit";
            expected = world.finish(end);
        }
        if unended {
            if found.end != "fault: step limit" && truth.undecided.is_none() {
                truth.undecided = Some(format!(
                    "seed {seed}: the source runs past its bound, the machine ends {:?}",
                    found.end
                ));
            }
            continue;
        }
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

const CLASSES: [&str; 7] = [
    "C0 original",
    "C19 index register swapped",
    "C20 stride constant changed",
    "C21 displacement changed",
    "C22 base slot changed",
    "C23 index extension dropped or changed",
    "C24 bounds check jcc inverted",
];

struct Mutant {
    class: usize,
    label: String,
    machine: X86ISelFunction,
}

/// The x86 conditions a mutant puts in place of `cc`: its inverse, its
/// signed/unsigned twin and its strict/non-strict twin.
fn neighbours(cc: X86CondCode) -> Vec<X86CondCode> {
    use X86CondCode as C;
    let inverse = match cc {
        C::E => C::NE,
        C::NE => C::E,
        C::B => C::AE,
        C::AE => C::B,
        C::BE => C::A,
        C::A => C::BE,
        C::L => C::GE,
        C::GE => C::L,
        C::LE => C::G,
        C::G => C::LE,
        C::S => C::NS,
        C::NS => C::S,
        C::O => C::NO,
        C::NO => C::O,
        C::P => C::NP,
        C::NP => C::P,
    };
    let twin = match cc {
        C::B => Some(C::L),
        C::L => Some(C::B),
        C::BE => Some(C::LE),
        C::LE => Some(C::BE),
        C::A => Some(C::G),
        C::G => Some(C::A),
        C::AE => Some(C::GE),
        C::GE => Some(C::AE),
        _ => None,
    };
    let strictness = match cc {
        C::B => Some(C::BE),
        C::BE => Some(C::B),
        C::A => Some(C::AE),
        C::AE => Some(C::A),
        C::L => Some(C::LE),
        C::LE => Some(C::L),
        C::G => Some(C::GE),
        C::GE => Some(C::G),
        C::E => Some(C::BE),
        C::NE => Some(C::A),
        _ => None,
    };
    std::iter::once(inverse)
        .chain(twin)
        .chain(strictness)
        .collect()
}

fn mutants(base: &X86ISelFunction) -> Vec<Mutant> {
    use X86Opcode as X;
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
    let vreg = |operand: &O| match operand {
        O::VReg(v) => Some(*v),
        _ => None,
    };
    // Frame registers (a `lea` of a stack slot, or a copy of one) with their
    // slot, and constant registers (a `mov` of an immediate).
    let mut frames: HashMap<u32, u32> = HashMap::new();
    let mut constants: HashSet<u32> = HashSet::new();
    for (ordinal, _, _) in &all {
        let row = inst(base, *ordinal);
        match (row.opcode, row.operands.as_slice()) {
            (X::Lea, [O::VReg(d), O::MemAddr { base: b, .. }]) => match b.as_ref() {
                O::StackSlot(slot) => {
                    frames.insert(d.id, *slot);
                }
                O::VReg(v) => {
                    if let Some(slot) = frames.get(&v.id).copied() {
                        frames.insert(d.id, slot);
                    }
                }
                _ => {}
            },
            (X::MovRR, [O::VReg(d), O::VReg(v)]) => {
                if let Some(slot) = frames.get(&v.id).copied() {
                    frames.insert(d.id, slot);
                }
            }
            (X::MovRI, [O::VReg(d), _]) => {
                constants.insert(d.id);
            }
            _ => {}
        }
    }
    // The indexed adds (an `add` of a frame or indexed register and a
    // non-constant one: the row, the frame operand's index, the index
    // operand's index) and the indexed registers.
    let mut indexed: HashSet<u32> = HashSet::new();
    let mut adds: Vec<(usize, usize, usize)> = Vec::new();
    for (ordinal, _, _) in &all {
        let row = inst(base, *ordinal);
        let private = |v: &VReg| frames.contains_key(&v.id) || indexed.contains(&v.id);
        match (row.opcode, row.operands.as_slice()) {
            (X::AddRR, [O::VReg(d), O::VReg(a), O::VReg(b)]) if private(a) != private(b) => {
                let (frame, index) = if private(a) { (1, 2) } else { (2, 1) };
                let other = if private(a) { b } else { a };
                if !constants.contains(&other.id) {
                    adds.push((*ordinal, frame, index));
                    indexed.insert(d.id);
                }
            }
            (X::LeaSib, [O::VReg(d), O::SibMemAddr { base: b, .. }])
                if vreg(b).is_some_and(|v| private(&v)) =>
            {
                indexed.insert(d.id);
            }
            (X::MovRR, [O::VReg(d), O::VReg(v)]) if indexed.contains(&v.id) => {
                indexed.insert(d.id);
            }
            (X::Lea, [O::VReg(d), O::MemAddr { base: b, .. }])
                if vreg(b).is_some_and(|v| indexed.contains(&v.id)) =>
            {
                indexed.insert(d.id);
            }
            _ => {}
        }
    }
    // The last row before `upto` that writes `id`.
    let definition = |upto: usize, id: u32| -> Option<usize> {
        all.iter()
            .map(|(o, _, _)| *o)
            .filter(|o| *o < upto)
            .filter(|o| matches!(inst(base, *o).operands.first(), Some(O::VReg(d)) if d.id == id))
            .last()
    };
    // Earlier registers of the class of `v` (not `v`, not constants).
    let earlier = |upto: usize, v: VReg| -> Vec<VReg> {
        let mut found: Vec<VReg> = all
            .iter()
            .map(|(o, _, _)| *o)
            .filter(|o| *o < upto)
            .filter_map(|o| match inst(base, o).operands.first() {
                Some(O::VReg(d))
                    if d.class == v.class
                        && d.id != v.id
                        && !constants.contains(&d.id)
                        && !frames.contains_key(&d.id)
                        && !indexed.contains(&d.id) =>
                {
                    Some(*d)
                }
                _ => None,
            })
            .collect();
        found.dedup();
        found.into_iter().rev().take(2).collect()
    };
    for &(add, frame, index) in &adds {
        let row = inst(base, add).clone();
        let (Some(x), Some(f)) = (vreg(&row.operands[index]), vreg(&row.operands[frame])) else {
            continue;
        };
        // C19: the index register swapped with another live register.
        for other in earlier(add, x) {
            let mut m = base.clone();
            inst_mut(&mut m, add).operands[index] = O::VReg(other);
            push(
                1,
                format!("row {add}: index v{} for v{}", other.id, x.id),
                m,
            );
        }
        // C22: the base slot changed (another slot's frame register).
        let slot = frames.get(&f.id).copied();
        let mut others: Vec<u32> = frames
            .iter()
            .filter(|(id, s)| Some(**s) != slot && **id != f.id && definition(add, **id).is_some())
            .map(|(id, _)| *id)
            .collect();
        others.sort_unstable();
        for other in others.into_iter().take(2) {
            let mut m = base.clone();
            inst_mut(&mut m, add).operands[frame] = O::VReg(VReg::new(other, f.class));
            push(4, format!("row {add}: base v{other} for v{}", f.id), m);
        }
        // Walk the index back through copies to its scaling and extension.
        let mut at = add;
        let mut id = x.id;
        for _ in 0..8 {
            let Some(def) = definition(at, id) else {
                break;
            };
            let def_row = inst(base, def).clone();
            match (def_row.opcode, def_row.operands.as_slice()) {
                (X::MovRR | X::MovRR32, [_, O::VReg(v)]) => {
                    (at, id) = (def, v.id);
                }
                // C20: the stride constant of an `imul` or a scaled `lea`.
                (X::ImulRR, [_, a, b]) => {
                    for (k, operand) in [(1usize, a), (2, b)] {
                        if let Some(v) = vreg(operand)
                            && constants.contains(&v.id)
                            && let Some(c) = definition(def, v.id)
                            && let O::Imm(imm) = inst(base, c).operands[1]
                        {
                            for value in [imm + 1, imm - 1, imm * 2] {
                                let mut m = base.clone();
                                inst_mut(&mut m, c).operands[1] = O::Imm(value);
                                push(2, format!("row {c}: stride {value} for {imm}"), m);
                            }
                            let other = if k == 1 { b } else { a };
                            if let Some(v) = vreg(other) {
                                (at, id) = (def, v.id);
                            }
                        }
                    }
                }
                (
                    X::LeaSib,
                    [
                        _,
                        O::SibMemAddr {
                            index: i, scale, ..
                        },
                    ],
                ) => {
                    for value in [1u8, 2, 4, 8].into_iter().filter(|v| v != scale).take(2) {
                        let mut m = base.clone();
                        if let O::SibMemAddr { scale, .. } = &mut inst_mut(&mut m, def).operands[1]
                        {
                            *scale = value;
                        }
                        push(2, format!("row {def}: scale {value}"), m);
                    }
                    if let Some(v) = vreg(i) {
                        (at, id) = (def, v.id);
                    }
                }
                (X::ShlRI, [_, O::VReg(v), O::Imm(k)]) => {
                    for value in [k + 1, (k - 1).max(0)] {
                        let mut m = base.clone();
                        inst_mut(&mut m, def).operands[2] = O::Imm(value);
                        push(2, format!("row {def}: shift {value} for {k}"), m);
                    }
                    (at, id) = (def, v.id);
                }
                // C23: the index's extension changed (signedness, width) or
                // dropped (the whole source register copied).
                (X::Movzx | X::MovzxW | X::MovsxB | X::MovsxW | X::Movsx, [d, src]) => {
                    let swaps: &[X86Opcode] = match def_row.opcode {
                        X::Movzx => &[X::MovsxB, X::MovzxW],
                        X::MovzxW => &[X::MovsxW, X::Movzx],
                        X::MovsxB => &[X::Movzx],
                        X::MovsxW => &[X::MovzxW],
                        _ => &[],
                    };
                    for opcode in swaps {
                        let mut m = base.clone();
                        let row = inst_mut(&mut m, def);
                        row.opcode = *opcode;
                        row.flags = opcode.default_flags();
                        push(
                            5,
                            format!("row {def}: {opcode:?} for {:?}", def_row.opcode),
                            m,
                        );
                    }
                    // Dropped: a 64-bit copy of the register the source
                    // value was copied from at entry (an argument register).
                    if let (Some(d), Some(v)) = (vreg(d), vreg(src))
                        && d.class == RegClass::Gpr64
                        && let Some(entry) = definition(def, v.id)
                        && let [_, O::PReg(p)] = inst(base, entry).operands.as_slice()
                    {
                        let mut m = base.clone();
                        let row = inst_mut(&mut m, def);
                        row.opcode = X::MovRR;
                        row.flags = X::MovRR.default_flags();
                        row.operands[1] = O::PReg(X86PReg::new(p.encoding() % 16));
                        push(5, format!("row {def}: extension dropped"), m);
                    }
                    break;
                }
                _ => break,
            }
        }
    }
    // C21: the displacement of an access through an indexed register.
    for (ordinal, _, _) in &all {
        let row = inst(base, *ordinal);
        let Some(form) = memory_access(row.opcode) else {
            continue;
        };
        let operand = if form.load { 1 } else { 0 };
        let Some(O::MemAddr { base: b, disp }) = row.operands.get(operand) else {
            continue;
        };
        if !vreg(b).is_some_and(|v| indexed.contains(&v.id)) {
            continue;
        }
        let width = form.bytes as i32;
        for delta in [1, -1, width, -width] {
            let mut m = base.clone();
            if let O::MemAddr { disp: d, .. } = &mut inst_mut(&mut m, *ordinal).operands[operand] {
                *d = disp + delta;
            }
            push(
                3,
                format!("row {ordinal}: displacement {}", disp + delta),
                m,
            );
        }
    }
    // C24: a conditional jump inverted (a bounds check among them).
    for (ordinal, _, _) in &all {
        if let (X::Jcc, [O::CondCode(cc), _]) = (
            inst(base, *ordinal).opcode,
            inst(base, *ordinal).operands.as_slice(),
        ) {
            let inverse = neighbours(*cc)[0];
            let mut m = base.clone();
            inst_mut(&mut m, *ordinal).operands[0] = O::CondCode(inverse);
            push(6, format!("row {ordinal}: j{inverse:?} for j{cc:?}"), m);
        }
    }
    let mut seen = HashSet::new();
    out.retain(|m| seen.insert(describe(&m.machine)));
    // At most `ROB17_CAP` (default 12) mutants per class and stream, spread
    // evenly over the class's mutants in row order (deterministic).
    let cap: usize = std::env::var("ROB17_CAP")
        .ok()
        .and_then(|cap| cap.parse().ok())
        .unwrap_or(12);
    let mut by_class: Vec<Vec<Mutant>> = (0..CLASSES.len()).map(|_| Vec::new()).collect();
    for mutant in out {
        by_class[mutant.class].push(mutant);
    }
    by_class
        .into_iter()
        .flat_map(|mutants| spread(mutants, cap))
        .collect()
}

/// At most `cap` of `items`, spread evenly in order.
fn spread(items: Vec<Mutant>, cap: usize) -> Vec<Mutant> {
    let n = items.len();
    if n <= cap {
        return items;
    }
    items
        .into_iter()
        .enumerate()
        .filter(|(i, _)| (i * cap) / n != ((i + 1) * cap) / n)
        .map(|(_, m)| m)
        .collect()
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
    undecided: usize,
    undecided_refuted: usize,
    undecided_holds: usize,
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
    for shape in SLICE_SEVENTEEN {
        if shape == IndexShape::F64Table
            || only.is_some_and(|only| !format!("{shape:?}").contains(only))
        {
            continue;
        }
        let (source, selected) = slice17_pair(shape);
        for (level, base) in &optimized_bases(&selected) {
            for mutant in mutants(base) {
                let row = &mut probe.table[mutant.class];
                row.n += 1;
                let tag = format!(
                    "{shape:?}@{level} [{}] {}",
                    CLASSES[mutant.class], mutant.label
                );
                let truth = ground_truth(&source, &mutant.machine);
                if std::env::var_os("ROB17_DEBUG").is_some() {
                    eprintln!("ROB17-DEBUG {tag}: {truth:?}");
                }
                if let Some(reason) = &truth.unsupported {
                    row.gt_na += 1;
                    eprintln!("ROB17 GT-NA {tag}: {reason}");
                }
                let wrong = truth.wrong.is_some();
                let undecided = !wrong && truth.undecided.is_some();
                if wrong {
                    row.wrong += 1;
                }
                if undecided {
                    row.undecided += 1;
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
                        eprintln!("ROB17 {tag}: unsupported ({reason}) gt_wrong={wrong}");
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
                        eprintln!("ROB17 {tag}: mismatch ({other}) gt_wrong={wrong}");
                        continue;
                    }
                    Ok(body) => body,
                };
                row.theorem += 1;
                let sample_refuted = dag_refuted_on_samples(body.obligation());
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
                } else if undecided {
                    if sample_refuted || ay == "CounterExample" {
                        row.undecided_refuted += 1;
                    } else {
                        row.undecided_holds += 1;
                        probe.findings.push(format!(
                            "UNDECIDED and not refuted {tag} ay={ay} credited={credited}\n{:?}\n{}",
                            truth.undecided,
                            describe(&mutant.machine)
                        ));
                    }
                } else if (sample_refuted || ay == "CounterExample")
                    && mutant.class != 0
                    && truth.unsupported.is_none()
                {
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
                    "ROB17 {tag}: theorem sample_refuted={sample_refuted} ay={ay} credited={credited} gt_wrong={wrong}"
                );
            }
        }
    }
    probe
}

#[test]
#[ignore]
fn slice_seventeen_mutation_robustness() {
    let test = "slice_seventeen_mutation_robustness";
    let only = std::env::var("ROB17_ONLY").ok();
    let edits = if std::env::var_os("ROB17_NO_REPLAY").is_some() {
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
        "\nROB17 TABLE replay={} (n | owner unsupported | owner mismatch | theorem | sample-refuted | AY CE | AY CE not sampled | AY Valid | AY other | credited || GT-wrong: total / unsupported / mismatch / refuted / CREDITED-or-VALID || GT-correct but refuted | GT n/a || GT-undecided: total / refuted / NOT REFUTED)",
        edits.is_some()
    );
    for (class, row) in CLASSES.iter().zip(&probe.table) {
        eprintln!(
            "ROB17 {class:<38} {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} || {:>4} / {:>4} / {:>4} / {:>4} / {:>4} || {:>4} | {:>3} || {:>3} / {:>3} / {:>3}",
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
            row.gt_na,
            row.undecided,
            row.undecided_refuted,
            row.undecided_holds
        );
    }
    eprintln!("ROB17 conservative ({}):", probe.conservative.len());
    for line in &probe.conservative {
        eprintln!("ROB17-C {line}");
    }
    eprintln!("ROB17 findings ({}):", probe.findings.len());
    for line in &probe.findings {
        eprintln!("ROB17-F {line}");
    }
}
