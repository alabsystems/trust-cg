// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Robustness probe of slice 7 (calls through memory): mutate the real
//! machine streams of the slice-7 fixtures (O0 selection and the x86
//! optimizer at O1-O3), judge every mutant with the owner, the replayed
//! theorem (admitted AY --strict-proofs + Clean) and the verifier's crediting,
//! and compare with an INDEPENDENT concrete interpreter of the LIR and of the
//! pre-RA x86 stream (ground truth). Diagnostic only (ignored).
//!
//! Ground truth: a callee is a deterministic pseudo-random function of (its
//! name, its scalar arguments, the bytes of every buffer it was given). It
//! returns a pseudo-random result and OVERWRITES every byte of each buffer it
//! receives (in `retaining` mode also every buffer any earlier call
//! received, the model's adversary). Caller-saved registers, flags and the
//! bits above a narrow write are pseudo-random garbage after a call / write.
//! Observables: return bits (or trap), the call sequence with scalar
//! arguments, buffer addresses and buffer contents at each call, the
//! function's own incoming-memory accesses, the final incoming memory, and
//! the callee-saved registers at the return.

use super::slice5::describe;
use super::slice7::{CallMemShape, all_slice_seven_shapes, slice7_pair, theorem_refuted};
use super::*;
use std::collections::BTreeMap;
use trust_cg_ir::X86CondCode;
use trust_cg_lower::function::Signature;

// ---------------------------------------------------------------------------
// Ground truth
// ---------------------------------------------------------------------------

const SLOT_BASE: u64 = 0x7ff0_0000_0000;
const SLOT_STRIDE: u64 = 0x1_0000;
const IN_BASE: u64 = 0x5000_0000_0000;
const GT_INPUTS: u64 = 500;

fn slot_base(slot: u32) -> u64 {
    SLOT_BASE + u64::from(slot) * SLOT_STRIDE
}

fn is_private(address: u64) -> bool {
    (SLOT_BASE..SLOT_BASE + 64 * SLOT_STRIDE).contains(&address)
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

fn symbol_address(name: &str) -> u64 {
    (IN_BASE + 0x80_0000) + (name_hash(name) & 0xffff) * 0x100
}

#[derive(Clone, Copy, Debug)]
enum Param {
    Scalar(u32),
    Buffer(u32),
}

/// The ground-truth callee table: each callee's parameters (a buffer is a
/// pointer to that many bytes it reads and overwrites) and result bits.
fn callee(name: &str) -> Option<(&'static [Param], Option<u32>)> {
    use Param::*;
    Some(match name {
        "make3" | "pair_of" => (&[Buffer(24), Scalar(64)], None),
        "mixed_of" => (&[Buffer(16), Scalar(64)], None),
        "bump" => (&[Buffer(8)], None),
        "peek" => (&[Buffer(8)], Some(64)),
        "fill" => (&[Buffer(16)], None),
        "g1" => (&[Scalar(64)], Some(64)),
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
    retaining: bool,
    mem: HashMap<u64, u8>,
    retained: Vec<(u64, u32)>,
    calls: Vec<String>,
    accesses: Vec<String>,
}

impl World {
    fn new(seed: u64, retaining: bool) -> Self {
        Self {
            seed,
            retaining,
            mem: HashMap::new(),
            retained: Vec::new(),
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
            self.accesses
                .push(format!("load{bytes} {address:#x}"));
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

    fn call(&mut self, name: &str, args: &[u64]) -> Result<Option<u64>, String> {
        let (params, result) = callee(name).ok_or_else(|| format!("unknown callee {name}"))?;
        let mut key = mix(name_hash(name), 0x5151);
        let mut log = format!("{name}(");
        let mut buffers: Vec<(u64, u32)> = Vec::new();
        for (i, param) in params.iter().enumerate() {
            let raw = args[i];
            match param {
                Param::Scalar(bits) => {
                    let value = bitmask(raw, *bits);
                    key = mix(key, value);
                    log.push_str(&format!("{value:#x}, "));
                }
                Param::Buffer(bytes) => {
                    let valid = is_private(raw) || (IN_BASE..IN_BASE + 0x100_0000).contains(&raw);
                    if !valid {
                        return Err(format!("{name} dereferences {raw:#x}"));
                    }
                    buffers.push((raw, *bytes));
                }
            }
        }
        if self.retaining {
            for retained in self.retained.clone() {
                if !buffers.contains(&retained) {
                    buffers.push(retained);
                }
            }
        }
        for (address, bytes) in &buffers {
            log.push_str(&format!("[{address:#x}:"));
            for i in 0..u64::from(*bytes) {
                let byte = self.byte(address + i);
                key = mix(key, u64::from(byte) | (i << 8));
                log.push_str(&format!("{byte:02x}"));
            }
            log.push_str("] ");
        }
        self.calls.push(log);
        let zero_tag = key % 4 == 0;
        let mut rng = key;
        for (address, bytes) in &buffers {
            // Bytes at varied densities: an all-zero first word (an
            // `Option`'s `None` tag), zero 4-byte groups, 0/1 bytes, and
            // dense random bytes.
            let mut group = 0u64;
            for i in 0..u64::from(*bytes) {
                rng = splitmix(rng);
                if i % 4 == 0 {
                    group = rng % 5;
                }
                let byte = if zero_tag && i < 8 {
                    0
                } else {
                    match group {
                        0 => 0,
                        1 => (rng >> 8) as u8 & 1,
                        _ => rng as u8,
                    }
                };
                self.mem.insert(address + i, byte);
            }
        }
        if self.retaining {
            for buffer in &buffers {
                if !self.retained.contains(buffer) {
                    self.retained.push(*buffer);
                }
            }
        }
        rng = splitmix(rng ^ 0x7e57);
        Ok(result.map(|bits| bitmask(rng, bits)))
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

/// The return bits a caller reads of a result of type `ty`.
fn return_bits(ty: &Type) -> u32 {
    match ty {
        Type::B1 | Type::I32 => 32,
        Type::I8 => 8,
        Type::I16 => 16,
        _ => 64,
    }
}

/// Raw argument-register contents for each source parameter.
fn gt_input(source: &Function, pointers: &[usize], seed: u64) -> Vec<u64> {
    source
        .signature
        .params
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            let r = mix(seed, 0xA000 + i as u64);
            let garbage = mix(seed, 0xB000 + i as u64);
            if pointers.contains(&i) {
                return IN_BASE + 0x1000 * (i as u64 + 1);
            }
            match ty {
                // psABI _Bool: bit 0 the value, bits 1..7 clear, the rest
                // unspecified.
                Type::B1 => (r & 1) | (garbage & !0xff),
                _ => {
                    let bits = ty_bits(ty).unwrap_or(64);
                    let value = match seed % 4 {
                        0 => r % 16,
                        1 => r & 0xff,
                        2 => r,
                        _ => r | (1 << 63),
                    };
                    bitmask(value, bits) | (garbage & !bitmask(u64::MAX, bits))
                }
            }
        })
        .collect()
}

fn int_cc(cond: IntCC, a: u64, b: u64, bits: u32) -> bool {
    let (sa, sb) = (sext(a, bits) as i64, sext(b, bits) as i64);
    match cond {
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
    }
}

/// Run the LIR source on `raw` arguments.
fn run_source(source: &Function, raw: &[u64], world: &mut World) -> String {
    let mut vals: HashMap<Value, (u64, u32)> = HashMap::new();
    for (i, ty) in source.signature.params.iter().enumerate() {
        let bits = ty_bits(ty).unwrap_or(64);
        let value = if bits == 1 { raw[i] & 1 } else { bitmask(raw[i], bits) };
        vals.insert(Value(i as u32), (value, bits));
    }
    let sret = source.abi_sret_param.is_some();
    let mut block = source.entry_block;
    let mut steps = 0;
    loop {
        let Some(body) = source.blocks.get(&block) else {
            return format!("fault: no block {block:?}");
        };
        let mut next = None;
        for inst in &body.instructions {
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
            let result_bits = |default: u32| {
                inst.results
                    .first()
                    .and_then(|r| source.value_types.get(r))
                    .and_then(ty_bits)
                    .unwrap_or(default)
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
                    L::Iadd | L::Isub | L::Imul | L::Band | L::Bor | L::Bxor | L::Ishl
                    | L::Ushr | L::Sshr => {
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
                    L::Uextend { to_ty, .. } => {
                        let bits = ty_bits(to_ty).unwrap_or(64);
                        Some((get(0)?.0, bits))
                    }
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
                        Some((u64::from(int_cc(*cond, a, b, bits)), 1))
                    }
                    L::Select { cond: IntCC::NotEqual } => {
                        let (test, _) = get(0)?;
                        Some(if test != 0 { get(1)? } else { get(2)? })
                    }
                    L::StackAddr { slot } => Some((slot_base(*slot), 64)),
                    L::GlobalRef { name } | L::ExternRef { name } => {
                        Some((symbol_address(name), 64))
                    }
                    L::Load { ty, .. } => {
                        let (address, _) = get(0)?;
                        let bits = ty_bits(ty).ok_or("fault: load type")?;
                        let bytes = bits.div_ceil(8);
                        let value = world.read(address, bytes);
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
                        let args: Vec<u64> = (0..inst.args.len())
                            .map(|k| get(k).map(|(v, _)| v))
                            .collect::<Result<_, _>>()?;
                        let result = world.call(name, &args).map_err(|e| format!("fault: {e}"))?;
                        if inst.results.is_empty() {
                            None
                        } else {
                            let bits = result_bits(64);
                            Some((bitmask(result.unwrap_or(0), bits), bits))
                        }
                    }
                    L::Jump { dest } => {
                        next = Some(*dest);
                        None
                    }
                    L::Brif {
                        then_dest,
                        else_dest,
                        ..
                    } => {
                        let (test, _) = get(0)?;
                        next = Some(if test != 0 { *then_dest } else { *else_dest });
                        None
                    }
                    L::Switch { cases, default } => {
                        let (test, bits) = get(0)?;
                        next = Some(
                            cases
                                .iter()
                                .find(|(case, _)| bitmask(*case as u64, bits) == test)
                                .map_or(*default, |(_, block)| *block),
                        );
                        None
                    }
                    L::Return => {
                        let mut text = String::from("ret");
                        if sret {
                            text.push_str(&format!(" {:#x}", raw[0]));
                        } else {
                            for (k, ty) in source.signature.returns.iter().enumerate() {
                                let (value, _) = get(k)?;
                                text.push_str(&format!(" {:#x}", bitmask(value, return_bits(ty))));
                            }
                        }
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
                }
                Ok(None) => {}
                Err(end) => return end,
            }
            if next.is_some() {
                break;
            }
        }
        match next {
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

/// Run the pre-RA machine stream on `raw` arguments.
fn run_machine(
    machine: &X86ISelFunction,
    signature: &Signature,
    sret: bool,
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
        let read = |regs: &HashMap<Key, u64>, operand: &O, world: &World| -> Result<(u64, u32), String> {
            let (key, bits) = operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
            let value = regs.get(&key).copied().unwrap_or_else(|| {
                world.garbage(0x0DEF, steps ^ (u64::from(match key {
                    Key::V(id) => id,
                    Key::P(p) => 100_000 + u32::from(p),
                }) << 20))
            });
            Ok((bitmask(value, bits), bits))
        };
        let write = |regs: &mut HashMap<Key, u64>, operand: &O, bits: u32, value: u64| -> Result<(), String> {
            let (key, _) = operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
            let value = match bits {
                64 => value,
                32 => bitmask(value, 32),
                _ => (garbage & !bitmask(u64::MAX, bits)) | bitmask(value, bits),
            };
            regs.insert(key, value);
            Ok(())
        };
        let address = |regs: &HashMap<Key, u64>, operand: &O, world: &World| -> Result<u64, String> {
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
        let ops = &inst.operands;
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
                    let O::Imm(imm) = ops[1] else { return Err("gt: MovRI".into()) };
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
                X::AddRR | X::SubRR | X::ImulRR | X::AndRR | X::OrRR | X::XorRR | X::AddRI
                | X::SubRI | X::AndRI | X::OrRI | X::XorRI | X::ShlRI | X::ShrRI | X::SarRI => {
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
                        X::SubRR | X::SubRI => Some(eflags_of(r, bits, a < b, msb((a ^ b) & (a ^ r)))),
                        X::AndRR | X::AndRI | X::OrRR | X::OrRI | X::XorRR | X::XorRI => {
                            Some(eflags_of(r, bits, false, false))
                        }
                        _ if matches!(inst.opcode, X::ShlRI | X::ShrRI | X::SarRI) && shift == 0 => flags,
                        _ => None,
                    };
                    write(&mut regs, &ops[0], bits, r)?;
                }
                X::Lea | X::LeaSib => {
                    let a = address(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], 64, a)?;
                }
                X::LeaRip | X::MovRipRel => {
                    let O::Symbol(name) = &ops[1] else { return Err("gt: symbol".into()) };
                    write(&mut regs, &ops[0], 64, symbol_address(name))?;
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
                X::BtRI => {
                    let (a, bits) = read(&regs, &ops[0], world)?;
                    let O::Imm(bit) = ops[1] else { return Err("gt: bt".into()) };
                    let cf = (a >> ((bit as u64) & u64::from(bits - 1))) & 1 == 1;
                    flags = Some(Eflags {
                        cf,
                        zf: flags.map_or(garbage & 2 != 0, |f| f.zf),
                        sf: garbage & 4 != 0,
                        of: garbage & 8 != 0,
                        pf: garbage & 16 != 0,
                    });
                }
                X::Setcc => {
                    let O::CondCode(cc) = ops[1] else { return Err("gt: setcc".into()) };
                    let holds = flags.map_or(garbage & 1 == 1, |f| condition(cc, f));
                    write(&mut regs, &ops[0], 8, u64::from(holds))?;
                }
                X::Cmovcc | X::Cmovcc32 => {
                    let O::CondCode(cc) = ops[2] else { return Err("gt: cmov".into()) };
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
                    let O::Symbol(name) = &ops[0] else { return Err("gt: call operand".into()) };
                    let (params, _) = callee(name).ok_or_else(|| format!("gt: callee {name}"))?;
                    let args: Vec<u64> = (0..params.len())
                        .map(|i| {
                            regs.get(&Key::P(ARG_REGS[i])).copied().unwrap_or_else(|| {
                                world.garbage(0xA59, steps * 8 + i as u64)
                            })
                        })
                        .collect();
                    let result = world.call(name, &args).map_err(|e| format!("fault: {e}"))?;
                    for (k, root) in [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11].iter().enumerate() {
                        regs.insert(Key::P(*root), world.garbage(0xC10B, steps * 16 + k as u64));
                    }
                    if let Some(result) = result {
                        regs.insert(Key::P(RAX), result);
                    }
                    flags = None;
                }
                X::Jcc => {
                    let O::CondCode(cc) = ops[0] else { return Err("gt: jcc".into()) };
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
                    let mut text = String::from("ret");
                    let read_root = |root: u16| {
                        regs.get(&Key::P(root))
                            .copied()
                            .unwrap_or_else(|| world.garbage(0x2E7, u64::from(root)))
                    };
                    if sret {
                        text.push_str(&format!(" {:#x}", read_root(RAX)));
                    } else {
                        for (ty, root) in signature.returns.iter().zip([RAX, RDX]) {
                            text.push_str(&format!(" {:#x}", bitmask(read_root(root), return_bits(ty))));
                        }
                    }
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

/// Parameters of each shape that are pointers into incoming memory.
fn pointer_params(shape: CallMemShape) -> Vec<usize> {
    match shape {
        CallMemShape::SretForward | CallMemShape::OutParamThenStore => vec![0],
        _ => vec![],
    }
}

/// Ground truth: the first input on which the machine differs from the
/// source, per callee mode (simple, retaining).
#[derive(Debug, Clone, Default)]
struct Truth {
    simple: Option<String>,
    retaining: Option<String>,
    unsupported: Option<String>,
}

impl Truth {
    fn wrong(&self) -> bool {
        self.simple.is_some() || self.retaining.is_some()
    }
}

fn ground_truth(source: &Function, machine: &X86ISelFunction, shape: CallMemShape) -> Truth {
    let mut truth = Truth::default();
    let sret = source.abi_sret_param.is_some();
    let pointers = pointer_params(shape);
    for retaining in [false, true] {
        for seed in 0..GT_INPUTS {
            let raw = gt_input(source, &pointers, seed);
            let mut world = World::new(seed, retaining);
            let end = run_source(source, &raw, &mut world);
            let expected = world.finish(end);
            let mut world = World::new(seed, retaining);
            let end = run_machine(machine, &source.signature, sret, &raw, &mut world);
            let found = world.finish(end);
            for end in [&expected.end, &found.end] {
                if end.starts_with("gt-unsupported") || end.starts_with("gt:") {
                    truth.unsupported = Some(end.clone());
                    return truth;
                }
            }
            if expected != found {
                let detail = format!(
                    "seed {seed}: source {:?} / machine {:?}",
                    (expected.end, expected.calls, expected.accesses),
                    (found.end, found.calls, found.accesses)
                );
                if retaining {
                    truth.retaining = Some(detail);
                } else {
                    truth.simple = Some(detail);
                }
                break;
            }
        }
    }
    truth
}

// ---------------------------------------------------------------------------
// Mutations
// ---------------------------------------------------------------------------

const CLASSES: [&str; 11] = [
    "C0 original",
    "C1 other slot/offset",
    "C2 wrong call/arg position",
    "C3 slot read before call",
    "C4 pre-call copy reused",
    "C5 init store skipped",
    "C6 store after call",
    "C7 byte call did not define",
    "C8 two calls swapped",
    "C9 call dropped",
    "C10 slot read/store size",
];

struct Mutant {
    class: usize,
    label: String,
    machine: X86ISelFunction,
}

fn is_arg_root(operand: &O) -> Option<u16> {
    match operand_reg(operand) {
        Some((Key::P(root), _)) if ARG_REGS.contains(&root) => Some(root),
        _ => None,
    }
}

/// The frame address each register holds before each row (walk order,
/// ignoring control flow), and the slot address each memory row accesses.
fn frame_analysis(machine: &X86ISelFunction) -> (Vec<HashMap<Key, (u32, i64)>>, Vec<Option<(u32, i64, u32, bool)>>) {
    let mut before = Vec::new();
    let mut access = Vec::new();
    let mut state: HashMap<Key, (u32, i64)> = HashMap::new();
    let mut consts: HashMap<Key, i64> = HashMap::new();
    for (ordinal, _, _) in rows(machine) {
        let row = inst(machine, ordinal);
        before.push(state.clone());
        let slot_of = |operand: &O, state: &HashMap<Key, (u32, i64)>| match operand {
            O::MemAddr { base, disp } => match base.as_ref() {
                O::StackSlot(slot) => Some((*slot, i64::from(*disp))),
                other => operand_reg(other)
                    .and_then(|(key, _)| state.get(&key).copied())
                    .map(|(slot, offset)| (slot, offset + i64::from(*disp))),
            },
            _ => None,
        };
        let form = memory_access(row.opcode);
        access.push(form.and_then(|form| {
            let operand = if form.load { &row.operands[1] } else { &row.operands[0] };
            slot_of(operand, &state).map(|(s, o)| (s, o, form.bytes, form.load))
        }));
        let frame = |operand: &O| operand_reg(operand).and_then(|(key, _)| state.get(&key).copied());
        let constant = |operand: &O| operand_reg(operand).and_then(|(key, _)| consts.get(&key).copied());
        let defined = match row.opcode {
            X86Opcode::AddRR => match (frame(&row.operands[1]), frame(&row.operands[2]), constant(&row.operands[1]), constant(&row.operands[2])) {
                (Some((slot, offset)), None, _, Some(delta)) | (None, Some((slot, offset)), Some(delta), _) => Some((slot, offset + delta)),
                _ => None,
            },
            X86Opcode::Lea => slot_of(&row.operands[1], &state),
            X86Opcode::MovRR => operand_reg(&row.operands[1]).and_then(|(key, _)| state.get(&key).copied()),
            X86Opcode::AddRI | X86Opcode::SubRI => match (&row.operands[2], operand_reg(&row.operands[1]).and_then(|(key, _)| state.get(&key).copied())) {
                (O::Imm(imm), Some((slot, offset))) => Some((slot, if row.opcode == X86Opcode::AddRI { offset + imm } else { offset - imm })),
                _ => None,
            },
            _ => None,
        };
        let defined_constant = match (row.opcode, row.operands.get(1)) {
            (X86Opcode::MovRI, Some(O::Imm(imm))) => Some(*imm),
            _ => None,
        };
        if let Some((key, _)) = row.operands.first().and_then(operand_reg)
            && memory_access(row.opcode).is_none_or(|form| form.load)
        {
            match defined_constant {
                Some(imm) => {
                    consts.insert(key, imm);
                }
                None => {
                    consts.remove(&key);
                }
            }
        }
        if row.opcode == X86Opcode::Call {
            for root in [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11] {
                state.remove(&Key::P(root));
                consts.remove(&Key::P(root));
            }
        } else if memory_access(row.opcode).is_none_or(|form| form.load)
            && let Some((key, _)) = row.operands.first().and_then(operand_reg)
        {
            match defined {
                Some(address) => {
                    state.insert(key, address);
                }
                None => {
                    state.remove(&key);
                }
            }
        }
    }
    (before, access)
}

/// The argument set-up rows immediately before `call`.
fn setup_rows(machine: &X86ISelFunction, call: usize) -> Vec<usize> {
    let mut found = Vec::new();
    for ordinal in (0..call).rev() {
        let row = inst(machine, ordinal);
        if row.opcode == X86Opcode::Call || row.operands.first().and_then(is_arg_root).is_none() {
            break;
        }
        found.push(ordinal);
    }
    found.reverse();
    found
}

/// The result copy right after `call`, if any.
fn result_copy(machine: &X86ISelFunction, call: usize) -> Option<usize> {
    let next = call + 1;
    (next < rows(machine).len()).then_some(next).filter(|ordinal| {
        let row = inst(machine, *ordinal);
        row.operands.get(1).and_then(operand_reg).is_some_and(|(key, _)| key == Key::P(RAX))
    })
}

fn same_block(machine: &X86ISelFunction, a: usize, b: usize) -> bool {
    let all = rows(machine);
    all[a].1 == all[b].1
}

fn new_vreg(machine: &mut X86ISelFunction, class: RegClass) -> O {
    machine.next_vreg += 1;
    O::VReg(VReg::new(50_000 + machine.next_vreg, class))
}

/// `new` carrying the TV-1 provenance stamp of the row it replaces.
fn keep(old: &X86ISelInst, mut new: X86ISelInst) -> X86ISelInst {
    new.lowering_provenance = old.lowering_provenance.clone();
    new
}

fn slot_addr(slot: u32, offset: i64) -> O {
    O::MemAddr {
        base: Box::new(O::StackSlot(slot)),
        disp: offset as i32,
    }
}

fn load_opcode(bytes: u32) -> X86Opcode {
    match bytes {
        1 => X86Opcode::MovRM8,
        2 => X86Opcode::MovRM16,
        4 => X86Opcode::MovRM32,
        _ => X86Opcode::MovRM,
    }
}

fn store_opcode(bytes: u32) -> X86Opcode {
    match bytes {
        1 => X86Opcode::MovMR8,
        2 => X86Opcode::MovMR16,
        4 => X86Opcode::MovMR32,
        _ => X86Opcode::MovMR,
    }
}

/// Rebuild one block's rows as `new` (walk ordinals `first..=last` replaced).
fn replace_range(machine: &mut X86ISelFunction, first: usize, last: usize, new: Vec<X86ISelInst>) {
    let all = rows(machine);
    let (_, block, start) = all[first];
    let end = all[last].2;
    let insts = &mut machine.blocks.get_mut(&block).unwrap().insts;
    insts.splice(start..=end, new);
}

fn mutants(source: &Function, base: &X86ISelFunction) -> Vec<Mutant> {
    let mut out: Vec<Mutant> = Vec::new();
    let mut push = |class: usize, label: String, machine: X86ISelFunction| {
        out.push(Mutant {
            class,
            label,
            machine,
        });
    };
    push(0, "original".into(), base.clone());
    let slots = source.stack_slots.len() as u32;
    let size = |slot: u32| i64::from(source.stack_slots[slot as usize].size);
    let calls = find(base, X86Opcode::Call);
    let (frames, access) = frame_analysis(base);
    let total = rows(base).len();
    let frame_arg = |ordinal: usize| -> Option<(u32, i64)> {
        let row = inst(base, ordinal);
        match row.opcode {
            X86Opcode::Lea => match &row.operands[1] {
                O::MemAddr { base: b, disp } => match b.as_ref() {
                    O::StackSlot(slot) => Some((*slot, i64::from(*disp))),
                    other => operand_reg(other).and_then(|(key, _)| frames[ordinal].get(&key).copied()).map(|(s, o)| (s, o + i64::from(*disp))),
                },
                _ => None,
            },
            X86Opcode::MovRR => operand_reg(&row.operands[1]).and_then(|(key, _)| frames[ordinal].get(&key).copied()),
            _ => None,
        }
    };
    // Slot accesses: (ordinal, slot, offset, bytes, load).
    let slot_rows: Vec<(usize, u32, i64, u32, bool)> = access
        .iter()
        .enumerate()
        .filter_map(|(ordinal, a)| a.map(|(s, o, n, l)| (ordinal, s, o, n, l)))
        .collect();
    // Slots escaped at or before each call.
    let mut escaped_at: Vec<Vec<u32>> = Vec::new();
    let mut escaped: Vec<u32> = Vec::new();
    for &call in &calls {
        for row in setup_rows(base, call) {
            if let Some((slot, _)) = frame_arg(row)
                && !escaped.contains(&slot)
            {
                escaped.push(slot);
            }
        }
        escaped_at.push(escaped.clone());
    }
    let candidates = |slot: u32, offset: i64| -> Vec<(u32, i64)> {
        let mut c: Vec<(u32, i64)> = (0..slots).filter(|s| *s != slot).map(|s| (s, offset)).collect();
        for delta in [-8, 8, 1, 16, -1, 4] {
            let o = offset + delta;
            if o >= 0 && o < size(slot) + 8 {
                c.push((slot, o));
            }
        }
        c
    };

    // C1: another slot or offset passed.
    for (n, &call) in calls.iter().enumerate() {
        for row in setup_rows(base, call) {
            let Some((slot, offset)) = frame_arg(row) else { continue };
            for (s2, o2) in candidates(slot, offset) {
                let mut m = base.clone();
                let dst = inst(&m, row).operands[0].clone();
                let old = inst(&m, row).clone();
                *inst_mut(&mut m, row) = keep(&old, X86ISelInst::new(X86Opcode::Lea, vec![dst, slot_addr(s2, o2)]));
                push(1, format!("call {n}: arg row {row} passes slot {s2}+{o2} (was {slot}+{offset})"), m);
            }
        }
    }
    for (ordinal, _, _) in rows(base) {
        let row = inst(base, ordinal);
        if let (X86Opcode::Lea, Some(O::MemAddr { base: b, disp })) = (row.opcode, row.operands.get(1))
            && let O::StackSlot(slot) = b.as_ref()
        {
            for (s2, o2) in candidates(*slot, i64::from(*disp)) {
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[1] = slot_addr(s2, o2);
                push(1, format!("lea row {ordinal}: slot {s2}+{o2} (was {slot}+{disp}), all uses"), m);
            }
        }
    }

    // C2: wrong call or argument position.
    for (n, &call) in calls.iter().enumerate() {
        let setup = setup_rows(base, call);
        for &f in &setup {
            if frame_arg(f).is_none() {
                continue;
            }
            for &g in &setup {
                if g == f {
                    continue;
                }
                let mut m = base.clone();
                let (df, dg) = (inst(&m, f).operands[0].clone(), inst(&m, g).operands[0].clone());
                inst_mut(&mut m, f).operands[0] = dg;
                inst_mut(&mut m, g).operands[0] = df;
                push(2, format!("call {n}: rows {f}/{g} swap argument registers"), m);
            }
            for (n2, &other) in calls.iter().enumerate() {
                if other == call {
                    continue;
                }
                let setup2 = setup_rows(base, other);
                let Some(&g) = setup2.iter().find(|row| inst(base, **row).operands.first().and_then(is_arg_root) == inst(base, f).operands.first().and_then(is_arg_root)) else {
                    continue;
                };
                // The slot given to the other call too (same register).
                let mut m = base.clone();
                let given = inst(base, f).clone();
                let mut copy = given.clone();
                copy.operands[0] = inst(base, g).operands[0].clone();
                if given.opcode == X86Opcode::MovRR && other < f {
                    // The source vreg may be defined after `other`: use a lea.
                    let (s, o) = frame_arg(f).unwrap();
                    copy = keep(&given, X86ISelInst::new(X86Opcode::Lea, vec![copy.operands[0].clone(), slot_addr(s, o)]));
                }
                *inst_mut(&mut m, g) = copy.clone();
                push(2, format!("call {n2} also given call {n}'s slot (row {g})"), m.clone());
                // And swapped: call `n` gets the other's argument.
                let mut m2 = m;
                let mut theirs = inst(base, g).clone();
                theirs.operands[0] = given.operands[0].clone();
                *inst_mut(&mut m2, f) = theirs;
                push(2, format!("calls {n}/{n2} swap their argument {}", f), m2);
            }
        }
    }

    // C3/C4/C6/C7/C10 over slot loads after a call.
    for (n, &call) in calls.iter().enumerate() {
        let setup = setup_rows(base, call);
        let first = setup.first().copied().unwrap_or(call);
        let after = result_copy(base, call).map_or(call + 1, |r| r + 1);
        for &(load, slot, offset, bytes, is_load) in &slot_rows {
            if !is_load || load <= call || !escaped_at[n].contains(&slot) {
                continue;
            }
            let row = inst(base, load).clone();
            let address_ok_before = match &row.operands[1] {
                O::MemAddr { base: b, .. } => match b.as_ref() {
                    O::StackSlot(_) => true,
                    other => operand_reg(other).is_some_and(|(key, _)| frames[first].contains_key(&key)),
                },
                _ => false,
            };
            // C3: the load moved before the call (its arguments' set-up).
            if address_ok_before && same_block(base, first, load) {
                let mut m = base.clone();
                let moved = remove_at(&mut m, load);
                insert_at(&mut m, first, moved);
                push(3, format!("load row {load} (slot {slot}+{offset}) moved before call {n}"), m);
            }
            // C4: a pre-call register copy reused after the call.
            if address_ok_before && same_block(base, first, load) {
                let mut m = base.clone();
                let class = match &row.operands[0] {
                    O::VReg(v) => v.class,
                    _ => RegClass::Gpr64,
                };
                let temp = new_vreg(&mut m, class);
                let mut early = row.clone();
                early.operands[0] = temp.clone();
                *inst_mut(&mut m, load) = keep(&row, X86ISelInst::new(X86Opcode::MovRR, vec![row.operands[0].clone(), temp]));
                insert_at(&mut m, first, early);
                push(4, format!("slot {slot}+{offset} read into a register before call {n}, copied after (row {load})"), m);
            }
            if let Some(&(store, _, _, _, _)) = slot_rows.iter().rev().find(|(r, s, o, nb, l)| {
                *r < call && !*l && *s == slot && *o == offset && *nb == bytes
            }) {
                let src = inst(base, store).operands[1].clone();
                let mut m = base.clone();
                let opcode = if operand_reg(&row.operands[0]).map(|r| r.1) == operand_reg(&src).map(|r| r.1) {
                    X86Opcode::MovRR
                } else {
                    X86Opcode::MovRR32
                };
                *inst_mut(&mut m, load) = keep(&row, X86ISelInst::new(opcode, vec![row.operands[0].clone(), src]));
                push(4, format!("stored value (row {store}) forwarded across call {n} to row {load}"), m);
            }
            // C6: a store into the slot after the call, before the read.
            if same_block(base, after.min(load), load) && after <= load {
                for (what, value) in [("0x5a5a", Some(0x5a5a_i64)), ("param", None)] {
                    let mut m = base.clone();
                    let temp = new_vreg(&mut m, RegClass::Gpr64);
                    let mut new = Vec::new();
                    match value {
                        Some(imm) => new.push(X86ISelInst::new(X86Opcode::MovRI, vec![temp.clone(), O::Imm(imm)])),
                        None => {
                            // The first parameter's vreg (row 0's destination).
                            let p = inst(base, 0).operands[0].clone();
                            if operand_reg(&p).is_none_or(|r| r.1 != 64) {
                                continue;
                            }
                            new.push(X86ISelInst::new(X86Opcode::MovRR, vec![temp.clone(), p]));
                        }
                    }
                    new.push(X86ISelInst::new(store_opcode(bytes), vec![slot_addr(slot, offset), temp]));
                    for (k, i) in new.into_iter().enumerate() {
                        insert_at(&mut m, after + k, i);
                    }
                    push(6, format!("store {what} to slot {slot}+{offset} after call {n}, before row {load}"), m);
                }
            }
            // C7: another byte read (another offset or slot).
            for (s2, o2) in candidates(slot, offset) {
                let mut m = base.clone();
                inst_mut(&mut m, load).operands[1] = slot_addr(s2, o2);
                push(7, format!("row {load} reads slot {s2}+{o2} (was {slot}+{offset})"), m);
            }
            // C10: another load size.
            for b2 in [1u32, 2, 4, 8] {
                if b2 == bytes {
                    continue;
                }
                let mut m = base.clone();
                let r = inst_mut(&mut m, load);
                r.opcode = load_opcode(b2);
                r.flags = load_opcode(b2).default_flags();
                if b2 == 8
                    && let O::VReg(v) = r.operands[0]
                {
                    r.operands[0] = O::VReg(VReg::new(v.id, RegClass::Gpr64));
                }
                push(10, format!("row {load} reads {b2} bytes (was {bytes})"), m);
            }
        }
        // C6 variant: a store to every escaped slot right after the call
        // (whether or not the source reads it later).
        for &slot in &escaped_at[n] {
            if size(slot) < 8 || after >= total {
                continue;
            }
            let mut m = base.clone();
            let temp = new_vreg(&mut m, RegClass::Gpr64);
            insert_at(&mut m, after.min(total), X86ISelInst::new(X86Opcode::MovRI, vec![temp.clone(), O::Imm(0x77)]));
            insert_at(&mut m, after.min(total) + 1, X86ISelInst::new(X86Opcode::MovMR, vec![slot_addr(slot, 0), temp]));
            push(6, format!("store 0x77 to slot {slot}+0 right after call {n}"), m);
        }
    }

    // C5: an initializing slot store skipped; C10 on stores.
    for &(store, slot, offset, bytes, is_load) in &slot_rows {
        if is_load {
            continue;
        }
        let before_a_call = calls.iter().any(|c| *c > store);
        if before_a_call {
            let mut m = base.clone();
            remove_at(&mut m, store);
            push(5, format!("store row {store} (slot {slot}+{offset}) removed"), m);
        }
        for b2 in [1u32, 2, 4, 8] {
            if b2 == bytes {
                continue;
            }
            let src = inst(base, store).operands[1].clone();
            if operand_reg(&src).is_none_or(|r| r.1 < b2 * 8) {
                continue;
            }
            let mut m = base.clone();
            let r = inst_mut(&mut m, store);
            r.opcode = store_opcode(b2);
            r.flags = store_opcode(b2).default_flags();
            push(10, format!("store row {store} writes {b2} bytes (was {bytes})"), m);
        }
    }

    // C8: two calls swapped (set-up, call and result copy as a group).
    for i in 0..calls.len() {
        for j in i + 1..calls.len() {
            let group = |c: usize| {
                let s = setup_rows(base, c);
                let first = s.first().copied().unwrap_or(c);
                let last = result_copy(base, c).unwrap_or(c);
                (first, last)
            };
            let (a0, a1) = group(calls[i]);
            let (b0, b1) = group(calls[j]);
            if !same_block(base, a0, b1) || a1 >= b0 {
                continue;
            }
            let mut m = base.clone();
            let take = |range: std::ops::RangeInclusive<usize>| range.map(|o| inst(base, o).clone()).collect::<Vec<_>>();
            let mut new = take(b0..=b1);
            new.extend(take(a1 + 1..=b0 - 1));
            new.extend(take(a0..=a1));
            replace_range(&mut m, a0, b1, new);
            push(8, format!("calls {i} and {j} swapped with their set-up"), m);
            // Only the call rows swapped.
            let mut m = base.clone();
            let (ci, cj) = (inst(base, calls[i]).clone(), inst(base, calls[j]).clone());
            *inst_mut(&mut m, calls[i]) = cj;
            *inst_mut(&mut m, calls[j]) = ci;
            push(8, format!("call rows {i} and {j} swapped"), m);
        }
    }

    // C9: a call dropped.
    for (n, &call) in calls.iter().enumerate() {
        let mut m = base.clone();
        remove_at(&mut m, call);
        push(9, format!("call {n} row removed"), m);
        let setup = setup_rows(base, call);
        let first = setup.first().copied().unwrap_or(call);
        let mut new = Vec::new();
        let last = match result_copy(base, call) {
            Some(r) => {
                new.push(keep(inst(base, r), X86ISelInst::new(X86Opcode::MovRI, vec![inst(base, r).operands[0].clone(), O::Imm(0)])));
                r
            }
            None => call,
        };
        let mut m = base.clone();
        replace_range(&mut m, first, last, new);
        push(9, format!("call {n} with its set-up removed"), m);
    }
    // Deduplicate identical streams.
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
    wrong_retaining_only: usize,
    wrong_unsupported: usize,
    wrong_mismatch: usize,
    wrong_refuted: usize,
    wrong_credited: usize,
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
    for shape in all_slice_seven_shapes() {
        if only.is_some_and(|only| !format!("{shape:?}").contains(only)) {
            continue;
        }
        let (source, selected) = slice7_pair(shape);
        for (level, base) in &optimized_bases(&selected) {
            for mutant in mutants(&source, base) {
                let row = &mut probe.table[mutant.class];
                row.n += 1;
                let tag = format!("{shape:?}@{level} [{}] {}", CLASSES[mutant.class], mutant.label);
                let truth = ground_truth(&source, &mutant.machine, shape);
                if let Some(reason) = &truth.unsupported {
                    row.gt_na += 1;
                    eprintln!("ROB7 GT-NA {tag}: {reason}");
                }
                let wrong = truth.wrong();
                if wrong {
                    row.wrong += 1;
                    if truth.simple.is_none() {
                        row.wrong_retaining_only += 1;
                    }
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
                        eprintln!("ROB7 {tag}: unsupported ({reason}) gt_wrong={wrong}");
                        continue;
                    }
                    Err(other) => {
                        row.mismatch += 1;
                        if wrong {
                            row.wrong_mismatch += 1;
                        } else if mutant.class != 0 {
                            probe
                                .conservative
                                .push(format!("mismatch on GT-correct {tag}: {other}"));
                        }
                        eprintln!("ROB7 {tag}: mismatch ({other}) gt_wrong={wrong}");
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
                            let result = fresh.ay().verify_fresh_source_bound(&body, &replay_config());
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
                        "CounterExample" => row.ay_ce += 1,
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
                    probe.findings.push(format!("original not credited {tag} ay={ay}"));
                }
                eprintln!(
                    "ROB7 {tag}: theorem sample_refuted={sample_refuted} ay={ay} credited={credited} gt_wrong={wrong}"
                );
            }
        }
    }
    probe
}

#[test]
#[ignore]
fn slice_seven_mutation_robustness() {
    let test = "slice_seven_mutation_robustness";
    let only = std::env::var("ROB7_ONLY").ok();
    let edits = if std::env::var_os("ROB7_NO_REPLAY").is_some() {
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
        "\nROB7 TABLE replay={} (n | owner unsupported | owner mismatch | theorem | sample-refuted | AY CE | AY Valid | AY other | credited || GT-wrong: total (retention-only) / unsupported / mismatch / refuted / CREDITED-or-VALID || GT-correct but refuted | GT n/a)",
        edits.is_some()
    );
    for (class, row) in CLASSES.iter().zip(&probe.table) {
        eprintln!(
            "ROB7 {class:<28} {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} || {:>4} ({:>3}) / {:>4} / {:>4} / {:>4} / {:>4} || {:>4} | {:>3}",
            row.n,
            row.unsupported,
            row.mismatch,
            row.theorem,
            row.sample_refuted,
            row.ay_ce,
            row.ay_valid,
            row.ay_other,
            row.credited,
            row.wrong,
            row.wrong_retaining_only,
            row.wrong_unsupported,
            row.wrong_mismatch,
            row.wrong_refuted,
            row.wrong_credited,
            row.correct_refuted,
            row.gt_na
        );
    }
    eprintln!("ROB7 conservative ({}):", probe.conservative.len());
    for line in &probe.conservative {
        eprintln!("ROB7-C {line}");
    }
    eprintln!("ROB7 findings ({}):", probe.findings.len());
    for line in &probe.findings {
        eprintln!("ROB7-F {line}");
    }
}
