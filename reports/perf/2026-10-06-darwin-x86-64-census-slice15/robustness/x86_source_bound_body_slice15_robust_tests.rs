// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Robustness probe of slice 15 (float constants and sign-bit operations,
//! mixed-width registers, a forwarded `bool` parameter, accesses through an
//! address that may derive from an escaped slot, `I128` in the stack argument
//! areas): mutate the real machine streams of the slice-15 fixtures (O0
//! selection and the x86 optimizer at O1-O3), judge every mutant with the
//! owner, the solver-free sampler, and (unless `ROB15_NO_REPLAY`) the replayed
//! theorem (admitted AY --strict-proofs + Clean) and the verifier's crediting,
//! and compare with an INDEPENDENT concrete interpreter of the LIR and of the
//! pre-RA x86 stream (ground truth). Diagnostic only (ignored).
//!
//! Ground truth, as in the slice-13 probe (concrete bytes, the slot binding,
//! a concrete frame and stack pointer, callees as deterministic pseudo-random
//! functions of what they can REACH, by the probe's own reachability), and in
//! addition:
//!
//! - Floats: a constant is `(imm as f32).to_bits()` / `imm.to_bits()`, and
//!   `Fneg`/`Fabs` are Rust's `-x` and `x.abs()` on the bit pattern (the
//!   interpreter never uses the owner's bit-operation statement); the machine
//!   reads a constant-pool entry's bytes and runs `pxor`/`andps`/`andpd` on
//!   whole 128-bit registers.
//! - Callees return pointers into a slot they can reach, into incoming
//!   memory or anywhere, and when they overwrite a reachable slot write such
//!   pointers into it too, so a load or store through what they returned or
//!   left really reaches an escaped slot sometimes.
//! - A row of mixed register widths runs as the encoder emits it, with REX.W:
//!   all 64 bits, and a 32-bit virtual register read at 64 bits holds garbage
//!   above bit 31 (the allocator keeps only its low half).
//! - Each input picks a caller convention: a psABI caller clears bits 1..7
//!   of a `bool` argument register only and reads AL of a `bool` result; a
//!   clean-bool caller clears bits 1..31 and reads EAX. A `bool` argument the
//!   body passes is observed at 32 bits, the clean bool every callee reads.
//! - An `I128` past the integer registers lies in two eightbytes of the
//!   stack areas, the first 16-byte aligned.

use super::slice5::describe;
use super::slice11::theorem_refuted;
use super::slice15::{all_slice_fifteen_shapes, slice15_pair};
use super::*;
use std::collections::BTreeMap;
use trust_cg_ir::X86CondCode;
use trust_cg_ir::regs::VReg;

const SLOT_BASE: u64 = 0x7ff0_0000_0000;
/// The frame pointer the machine walk starts with: the caller's incoming
/// stack eightbytes lie at `FRAME_BASE + 16 + 8k`.
const FRAME_BASE: u64 = 0x7ffe_0000_0000;
const INITIAL_RSP: u64 = 0x7fff_ffff_f000;
/// Bytes of each slot a callee reads and may overwrite.
const SLOT_SPAN: u64 = 64;
const SLOT_STRIDE: u64 = 0x1_0000;
const PARAM_BASE: u64 = 0x7fe0_0000_0000;
const RESULT_BASE: u64 = 0x7fd0_0000_0000;
const GT_INPUTS: u64 = 3000;
/// Where callees point into incoming memory.
const INCOMING_BASE: u64 = 0x5000_0000_0000;

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

fn mask128(value: u128, bits: u32) -> u128 {
    if bits >= 128 {
        value
    } else {
        value & ((1u128 << bits) - 1)
    }
}

fn mask64(value: u64, bits: u32) -> u64 {
    if bits >= 64 {
        value
    } else {
        value & ((1u64 << bits) - 1)
    }
}

fn sext128(value: u128, bits: u32) -> i128 {
    if bits >= 128 {
        value as i128
    } else {
        let shift = 128 - bits;
        ((value << shift) as i128) >> shift
    }
}

fn sext64(value: u64, bits: u32) -> u64 {
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

/// The ground truth's own scalar kinds: the bits of a value, and whether it
/// is a float (an SSE register) or an `I128` (two integer registers).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Int(u32),
    Wide,
    Float(u32),
    /// A `[u128; 1]` aggregate: 16 bytes, two INTEGER eightbytes.
    Pair,
    /// An array of `n` bytes, `n` at most 8: one INTEGER eightbyte.
    Bytes(u32),
}

fn kind(ty: &Type) -> Option<Kind> {
    Some(match ty {
        Type::B1 => Kind::Int(1),
        Type::I8 => Kind::Int(8),
        Type::I16 => Kind::Int(16),
        Type::I32 => Kind::Int(32),
        Type::I64 => Kind::Int(64),
        Type::I128 => Kind::Wide,
        Type::F32 => Kind::Float(32),
        Type::F64 => Kind::Float(64),
        Type::Array(element, 1) if **element == Type::I128 => Kind::Pair,
        Type::Array(element, n) if **element == Type::I8 && *n <= 8 => Kind::Bytes(*n),
        _ => return None,
    })
}

fn bits_of(kind: Kind) -> u32 {
    match kind {
        Kind::Int(bits) | Kind::Float(bits) => bits,
        Kind::Wide | Kind::Pair => 128,
        Kind::Bytes(n) => 8 * n,
    }
}

/// The direct callees of the slice-15 fixtures (and of the placement
/// controls).
fn callee(name: &str) -> Option<(Vec<Kind>, Vec<Kind>)> {
    use Kind::*;
    Some(match name {
        "g3" => (vec![Bytes(3)], vec![Bytes(3)]),
        "sink" => (vec![Int(1)], vec![]),
        "mix" => (vec![Int(64), Int(1)], vec![Int(64)]),
        "flip" => (vec![Int(1)], vec![Int(1)]),
        "fill" | "data" => (vec![Int(64)], vec![]),
        "id" => (vec![Int(64)], vec![Int(64)]),
        "take4" => (vec![Int(64), Wide, Wide, Wide], vec![Int(64)]),
        "take5" => (vec![Int(64), Wide, Wide, Int(64), Wide], vec![Int(64)]),
        _ => return None,
    })
}

/// The ground truth's own System V placement of `kinds`: each value's
/// registers, an integer register by its index into RDI.. (0..6) and an SSE
/// register as 100 + its index into XMM0.. (0..8), and an integer past the six
/// integer registers as 200 + its eightbyte's index in the stack area.
fn placement(kinds: &[Kind]) -> Option<Vec<Vec<u16>>> {
    let (mut gpr, mut sse, mut stack) = (0u16, 0u16, 0u16);
    kinds
        .iter()
        .map(|kind| match kind {
            Kind::Float(_) => {
                sse += 1;
                (sse <= 8).then(|| vec![100 + sse - 1])
            }
            Kind::Pair => {
                gpr += 2;
                (gpr <= 6).then(|| vec![gpr - 2, gpr - 1])
            }
            // Two registers, or (none left for both) two eightbytes of the
            // stack area, the first 16-byte aligned; a later scalar still
            // takes a register left over.
            Kind::Wide => {
                if gpr + 2 <= 6 {
                    gpr += 2;
                    return Some(vec![gpr - 2, gpr - 1]);
                }
                stack += stack % 2;
                stack += 2;
                Some(vec![200 + stack - 2, 200 + stack - 1])
            }
            Kind::Bytes(_) => {
                gpr += 1;
                (gpr <= 6).then(|| vec![gpr - 1])
            }
            Kind::Int(bits) => {
                if gpr < 6 {
                    gpr += 1;
                    return Some(vec![gpr - 1]);
                }
                // A `bool` on the stack is outside what the probe models.
                if *bits == 1 {
                    return None;
                }
                stack += 1;
                Some(vec![200 + stack - 1])
            }
        })
        .collect()
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
    /// The slots callees could reach so far (their base addresses): a callee
    /// may retain any address it saw.
    retained: std::collections::BTreeSet<u64>,
}

/// The base of the private slot `address` lies in, if any.
fn slot_of(address: u64) -> Option<u64> {
    (SLOT_BASE..SLOT_BASE + 64 * SLOT_STRIDE)
        .contains(&address)
        .then(|| SLOT_BASE + (address - SLOT_BASE) / SLOT_STRIDE * SLOT_STRIDE)
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
            retained: std::collections::BTreeSet::new(),
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

    fn read(&mut self, address: u64, bytes: u32) -> u128 {
        // A 16-byte access is its two 8-byte halves, low first: a
        // non-atomic, non-volatile access's granularity is not observable
        // (its bytes and its value are). Each half is classified (private
        // or incoming) at its own address, as the machine's two accesses
        // are.
        if bytes == 16 {
            let low = self.read(address, 8);
            let high = self.read(address.wrapping_add(8), 8);
            return (high << 64) | low;
        }
        let mut value = 0u128;
        for i in (0..u64::from(bytes)).rev() {
            value = (value << 8) | u128::from(self.byte(address.wrapping_add(i)));
        }
        if !is_private(address) {
            self.accesses.push(format!("load{bytes} {address:#x}"));
        }
        value
    }

    fn write(&mut self, address: u64, bytes: u32, value: u128) {
        if bytes == 16 {
            self.write(address, 8, u128::from(value as u64));
            self.write(address.wrapping_add(8), 8, value >> 64);
            return;
        }
        for i in 0..u64::from(bytes) {
            self.mem
                .insert(address.wrapping_add(i), (value >> (8 * i)) as u8);
        }
        if !is_private(address) {
            self.accesses.push(format!(
                "store{bytes} {address:#x} = {:#x}",
                mask128(value, bytes * 8)
            ));
        }
    }

    /// Call `name` with its parameters' bits `values` (one per parameter,
    /// already masked to its width); its results, each at its width.
    /// The 8-byte little-endian word at `address`, without logging an
    /// access (what a callee could read).
    fn peek_word(&self, address: u64) -> u64 {
        (0..8u64).rev().fold(0u64, |word, i| {
            (word << 8) | u64::from(self.byte(address.wrapping_add(i)))
        })
    }

    /// Every slot a callee given `values` can reach: those retained from
    /// earlier calls, those an argument points into, and, to a fixpoint,
    /// those an 8-byte word of incoming memory or of a reachable slot points
    /// into.
    fn reachable(&self, values: &[u128]) -> std::collections::BTreeSet<u64> {
        let mut reached = self.retained.clone();
        reached.extend(values.iter().filter_map(|value| slot_of(*value as u64)));
        loop {
            let mut grew = false;
            let mut addresses: Vec<u64> = self
                .mem
                .keys()
                .copied()
                .filter(|address| !is_private(*address))
                .collect();
            for base in &reached {
                addresses.extend(*base..*base + SLOT_SPAN);
            }
            for address in addresses {
                if let Some(slot) = slot_of(self.peek_word(address))
                    && reached.insert(slot)
                {
                    grew = true;
                }
            }
            if !grew {
                return reached;
            }
        }
    }

    fn call(&mut self, name: &str, values: &[u128]) -> Result<Vec<u128>, String> {
        let (params, results) = callee(name).ok_or_else(|| format!("unknown callee {name}"))?;
        let mut key = mix(name_hash(name), 0x5151);
        let mut log = format!("{name}(");
        for (value, kind) in values.iter().zip(&params) {
            // A `bool` argument is read as the clean 32-bit bool every
            // callee relies on (an LLVM `zeroext i1` callee, the backend's
            // own).
            let bits = match kind {
                Kind::Int(1) => 32,
                other => bits_of(*other),
            };
            let value = mask128(*value, bits);
            key = mix(mix(key, value as u64), (value >> 64) as u64);
            log.push_str(&format!("{value:#x}, "));
        }
        // The callee reads every slot it can reach, then (three calls in
        // four) overwrites their bytes.
        let reached = self.reachable(values);
        for base in &reached {
            let bytes: Vec<u8> = (*base..*base + SLOT_SPAN).map(|a| self.byte(a)).collect();
            log.push_str(&format!("[{base:#x}: {bytes:02x?}] "));
            for chunk in bytes.chunks(8) {
                key = mix(
                    key,
                    chunk.iter().fold(0u64, |w, b| (w << 8) | u64::from(*b)),
                );
            }
        }
        self.calls.push(log);
        // A pointer the callee may produce: into a slot it can reach, into
        // incoming memory, or any word.
        let reached_list: Vec<u64> = reached.iter().copied().collect();
        let pointer = |k: u64| -> u64 {
            let r = splitmix(key ^ k);
            match r % 4 {
                0 | 1 if !reached_list.is_empty() => {
                    reached_list[(r >> 8) as usize % reached_list.len()] + 8 * ((r >> 16) % 2)
                }
                2 => INCOMING_BASE + 8 * ((r >> 8) % 8),
                _ => r,
            }
        };
        if key % 4 != 0 {
            for base in &reached {
                for word in 0..SLOT_SPAN / 8 {
                    let address = base + 8 * word;
                    let value = if splitmix(key ^ address ^ 0x77) % 3 == 0 {
                        pointer(address)
                    } else {
                        splitmix(key ^ address)
                    };
                    for i in 0..8 {
                        self.mem.insert(address + i, (value >> (8 * i)) as u8);
                    }
                }
            }
        }
        self.retained = reached;
        Ok(results
            .iter()
            .enumerate()
            .map(|(k, kind)| {
                let low = splitmix(key ^ (2 * k as u64 + 1));
                let high = splitmix(key ^ (2 * k as u64 + 2));
                // A zero high half now and then (an `I128` that fits 64
                // bits), and the edges.
                let wide = match key % 7 {
                    0 => u128::from(low),
                    1 => u128::MAX,
                    _ => (u128::from(high) << 64) | u128::from(low),
                };
                // A 64-bit result is a pointer two times in three.
                if *kind == Kind::Int(64) && key % 3 != 0 {
                    return u128::from(pointer(0x9000 + k as u64));
                }
                mask128(wide, bits_of(*kind))
            })
            .collect())
    }

    /// `memcpy`/`memmove(dst, src, n)` or `memset(dst, byte, n)`, run
    /// concretely (each byte an access of incoming memory, logged); an
    /// overlapping `memcpy`, or more than 4096 bytes, is undefined here.
    fn memory_routine(&mut self, name: &str, args: [u64; 3]) -> Result<(), String> {
        let [dst, middle, n] = args;
        if n > 4096 {
            return Err("ub".into());
        }
        self.calls
            .push(format!("{name}({dst:#x}, {middle:#x}, {n:#x})"));
        match name {
            "memset" => {
                for i in 0..n {
                    self.write(dst.wrapping_add(i), 1, u128::from(middle as u8));
                }
            }
            "memcpy" | "memmove" => {
                let overlap = dst < middle.wrapping_add(n) && middle < dst.wrapping_add(n);
                if name == "memcpy" && overlap && n > 0 {
                    return Err("ub".into());
                }
                let bytes: Vec<u128> = (0..n)
                    .map(|i| self.read(middle.wrapping_add(i), 1))
                    .collect();
                for (i, byte) in bytes.into_iter().enumerate() {
                    self.write(dst.wrapping_add(i as u64), 1, byte);
                }
            }
            _ => return Err(format!("gt: memory routine {name}")),
        }
        Ok(())
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

/// The text a caller observes of a return: each lane at the bits a caller
/// reads (a `bool` at `bool_bits`: 8 for a psABI caller, 32 for a clean-bool
/// one; a narrow integer at its width, an `I128` as both halves, a float as
/// its bit pattern).
fn returned_text(kinds: &[Kind], values: &[u128], bool_bits: u32) -> String {
    let mut text = String::from("ret");
    for (kind, value) in kinds.iter().zip(values) {
        let bits = match kind {
            Kind::Int(1) => bool_bits,
            other => bits_of(*other),
        };
        text.push_str(&format!(" {:#x}", mask128(*value, bits)));
    }
    text
}

/// Raw argument registers (RDI, RSI, ...) and XMM0-XMM7 (low 64 bits),
/// each drawn independently: small words, overflow and sign boundaries,
/// repeating patterns, zero, random words; one input in eight gives every
/// register the same word, one in eight pairs each register with its
/// neighbour (equal halves of two `I128`s).
fn gt_registers(seed: u64) -> Vec<u64> {
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
    let mode = mix(seed, 0xC000) % 8;
    let mut registers: Vec<u64> = (0..18)
        .map(|i| {
            let i = if mode == 0 { 0 } else { i };
            let r = mix(seed, 0xA000 + i);
            match mix(seed, 0xB000 + i) % 9 {
                0 => r % 16,
                1 => r % 130,
                2 | 3 => EDGES[(r % EDGES.len() as u64) as usize],
                4 => r & 0x00ff_00ff_00ff_00ff,
                5 => r | (1 << 63),
                6 => 0,
                _ => r,
            }
        })
        .collect();
    if mode == 1 {
        // Two `I128`s with equal high halves (RSI = RCX) or equal low ones.
        registers[3] = registers[1];
    } else if mode == 2 {
        registers[2] = registers[0];
    }
    registers
}

/// Run the LIR source on argument registers `raw`.
fn run_source(source: &Function, raw: &[u64], world: &mut World, bool_bits: u32) -> String {
    let mut vals: HashMap<Value, (u128, u32)> = HashMap::new();
    let param_kinds: Option<Vec<Kind>> = source.signature.params.iter().map(kind).collect();
    let Some(param_kinds) = param_kinds else {
        return "gt-unsupported parameter type".into();
    };
    let Some(placed) = placement(&param_kinds) else {
        return "gt-unsupported placement".into();
    };
    let register = |index: u16| -> u64 {
        if index >= 200 {
            raw[14 + usize::from(index - 200)]
        } else if index >= 100 {
            raw[6 + usize::from(index - 100)]
        } else {
            raw[usize::from(index)]
        }
    };
    for (i, (kind, registers)) in param_kinds.iter().zip(&placed).enumerate() {
        let value = match kind {
            Kind::Wide => {
                (u128::from(register(registers[1])) << 64) | u128::from(register(registers[0]))
            }
            Kind::Pair => {
                // The callee's copy of the caller's two eightbytes.
                let base = PARAM_BASE + SLOT_STRIDE * i as u64;
                world.write(base, 8, u128::from(register(registers[0])));
                world.write(base + 8, 8, u128::from(register(registers[1])));
                vals.insert(Value(i as u32), (u128::from(base), 64));
                continue;
            }
            Kind::Bytes(n) => {
                // The callee's copy of the caller's low `n` register bytes.
                let base = PARAM_BASE + SLOT_STRIDE * i as u64;
                world.write(base, *n, u128::from(register(registers[0])));
                vals.insert(Value(i as u32), (u128::from(base), 64));
                continue;
            }
            Kind::Int(1) => u128::from(register(registers[0]) & 1),
            other => mask128(u128::from(register(registers[0])), bits_of(*other)),
        };
        vals.insert(Value(i as u32), (value, bits_of(*kind)));
    }
    let mut block = source.entry_block;
    let mut steps = 0u64;
    loop {
        let Some(body) = source.blocks.get(&block) else {
            return format!("fault: no block {block:?}");
        };
        let mut next_block = None;
        for inst in &body.instructions {
            steps += 1;
            if steps > 10_000 {
                return "fault: step limit".into();
            }
            let get = |k: usize| -> Result<(u128, u32), String> {
                inst.args
                    .get(k)
                    .and_then(|value| vals.get(value).copied())
                    .ok_or_else(|| format!("fault: undefined operand of {:?}", inst.opcode))
            };
            let ty_bits = |ty: &Type| kind(ty).map(bits_of);
            let def: Result<Option<(u128, u32)>, String> = (|| {
                Ok(match &inst.opcode {
                    L::Iconst { ty, imm } => {
                        let bits = ty_bits(ty).ok_or("gt-unsupported const")?;
                        Some((mask128(*imm as i128 as u128, bits), bits))
                    }
                    L::Iconst128 { lo, hi } => {
                        Some((((*hi as u64 as u128) << 64) | (*lo as u64 as u128), 128))
                    }
                    L::Copy => Some(get(0)?),
                    // trust-ir's float constant: the f64 narrowed with `as`
                    // at F32 (a NaN's payload is not pinned: unsupported).
                    L::Fconst { ty, imm } => match ty {
                        Type::F32 if !imm.is_nan() => {
                            Some((u128::from((*imm as f32).to_bits()), 32))
                        }
                        Type::F64 => Some((u128::from(imm.to_bits()), 64)),
                        _ => return Err("gt-unsupported float constant".into()),
                    },
                    // trust-ir's `-x` and `x.abs()` of the bit pattern.
                    L::Fneg | L::Fabs => {
                        let (bits_value, bits) = get(0)?;
                        let neg = matches!(inst.opcode, L::Fneg);
                        let value = match bits {
                            32 => {
                                let x = f32::from_bits(bits_value as u32);
                                u128::from(if neg { -x } else { x.abs() }.to_bits())
                            }
                            64 => {
                                let x = f64::from_bits(bits_value as u64);
                                u128::from(if neg { -x } else { x.abs() }.to_bits())
                            }
                            _ => return Err("gt-unsupported float width".into()),
                        };
                        Some((value, bits))
                    }
                    L::Bitcast { to_ty } => {
                        let bits = ty_bits(to_ty).ok_or("gt-unsupported bitcast")?;
                        Some((mask128(get(0)?.0, bits), bits))
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
                        if matches!(inst.opcode, L::Ishl | L::Ushr | L::Sshr)
                            && b >= u128::from(bits)
                        {
                            return Err("ub".into());
                        }
                        let amount = b as u32;
                        let value = match &inst.opcode {
                            L::Iadd => a.wrapping_add(b),
                            L::Isub => a.wrapping_sub(b),
                            L::Imul => a.wrapping_mul(b),
                            L::Band => a & b,
                            L::Bor => a | b,
                            L::Bxor => a ^ b,
                            L::Ishl => a << amount,
                            L::Ushr => a >> amount,
                            _ => (sext128(a, bits) >> amount) as u128,
                        };
                        Some((mask128(value, bits), bits))
                    }
                    L::Bnot => {
                        let (a, bits) = get(0)?;
                        Some((mask128(!a, bits), bits))
                    }
                    L::Ineg => {
                        let (a, bits) = get(0)?;
                        Some((mask128(0u128.wrapping_sub(a), bits), bits))
                    }
                    L::Uextend { to_ty, .. } => {
                        Some((get(0)?.0, ty_bits(to_ty).ok_or("gt-unsupported zext")?))
                    }
                    L::Sextend { from_ty, to_ty } => {
                        let from = ty_bits(from_ty).ok_or("gt-unsupported sext")?;
                        let bits = ty_bits(to_ty).ok_or("gt-unsupported sext")?;
                        Some((mask128(sext128(get(0)?.0, from) as u128, bits), bits))
                    }
                    L::Trunc { to_ty } => {
                        let bits = ty_bits(to_ty).ok_or("gt-unsupported trunc")?;
                        Some((mask128(get(0)?.0, bits), bits))
                    }
                    L::Icmp { cond } => {
                        let (a, bits) = get(0)?;
                        let (b, _) = get(1)?;
                        let (sa, sb) = (sext128(a, bits), sext128(b, bits));
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
                        Some((u128::from(holds), 1))
                    }
                    L::Select {
                        cond: IntCC::NotEqual,
                    } => {
                        let (test, _) = get(0)?;
                        Some(if test != 0 { get(1)? } else { get(2)? })
                    }
                    L::StackAddr { slot } => Some((u128::from(slot_base(*slot)), 64)),
                    L::StructGep {
                        struct_ty,
                        field_index,
                    } => {
                        let offset = struct_ty
                            .offset_of(*field_index as usize)
                            .ok_or("fault: struct gep")?;
                        Some((
                            (get(0)?.0 as u64).wrapping_add(u64::from(offset)) as u128,
                            64,
                        ))
                    }
                    L::Load { ty, .. } | L::AtomicLoad { ty, .. } => {
                        let (address, _) = get(0)?;
                        let bits = ty_bits(ty).ok_or("gt-unsupported load type")?;
                        let value = world.read(address as u64, bits.div_ceil(8));
                        Some(if bits == 1 {
                            (u128::from(value != 0), 1)
                        } else {
                            (value, bits)
                        })
                    }
                    L::Memcpy | L::Memmove | L::Memset => {
                        let name = match &inst.opcode {
                            L::Memcpy => "memcpy",
                            L::Memmove => "memmove",
                            _ => "memset",
                        };
                        let args = [get(0)?.0 as u64, get(1)?.0 as u64, get(2)?.0 as u64];
                        world.memory_routine(name, args)?;
                        None
                    }
                    L::Store { ty, .. } | L::AtomicStore { ty, .. } => {
                        let (value, _) = get(0)?;
                        let (address, _) = get(1)?;
                        let bits = ty_bits(ty).ok_or("gt-unsupported store type")?;
                        world.write(address as u64, bits.div_ceil(8), value);
                        None
                    }
                    L::Call { name, .. } => {
                        let (params, results) = callee(name).ok_or("gt: callee")?;
                        let mut values = Vec::new();
                        for (k, param) in params.iter().enumerate() {
                            values.push(match param {
                                // An aggregate by value: the bytes at its
                                // address.
                                Kind::Bytes(n) => world.read(get(k)?.0 as u64, *n),
                                other => mask128(get(k)?.0, bits_of(*other)),
                            });
                        }
                        let out = world
                            .call(name, &values)
                            .map_err(|e| format!("fault: {e}"))?;
                        match (results.first(), inst.results.first()) {
                            (_, None) => None,
                            (Some(Kind::Bytes(n)), Some(_)) => {
                                // Into a slot of its own, whose address the
                                // LIR result is.
                                let base = RESULT_BASE + SLOT_STRIDE * steps;
                                world.write(base, *n, out[0]);
                                Some((u128::from(base), 64))
                            }
                            (Some(kind), Some(_)) => Some((out[0], bits_of(*kind))),
                            _ => return Err("gt: call result".into()),
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
                    L::Return => {
                        let kinds: Option<Vec<Kind>> =
                            source.signature.returns.iter().map(kind).collect();
                        let kinds = kinds.ok_or("gt-unsupported return")?;
                        let mut values = Vec::new();
                        for (k, kind) in kinds.iter().enumerate() {
                            let (value, _) = get(k)?;
                            values.push(match kind {
                                Kind::Pair => world.read(value as u64, 16),
                                Kind::Bytes(n) => world.read(value as u64, *n),
                                _ => value,
                            });
                        }
                        return Err(returned_text(&kinds, &values, bool_bits));
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

/// An operand's register, the bits it names, and whether it is an SSE one.
fn operand_reg(operand: &O) -> Option<(Key, u32, bool)> {
    match operand {
        O::VReg(vreg) => Some(match vreg.class {
            RegClass::Gpr64 => (Key::V(vreg.id), 64, false),
            RegClass::Gpr32 => (Key::V(vreg.id), 32, false),
            RegClass::Fpr64 => (Key::V(vreg.id), 64, true),
            RegClass::Fpr32 => (Key::V(vreg.id), 32, true),
            _ => return None,
        }),
        O::PReg(preg) => {
            let e = preg.encoding();
            Some(match e {
                0..=15 => (Key::P(e), 64, false),
                16..=31 => (Key::P(e - 16), 32, false),
                32..=47 => (Key::P(e - 32), 16, false),
                48..=63 => (Key::P(e - 48), 8, false),
                64..=79 => (Key::P(e), 128, true),
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
    let r = mask64(result, bits);
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

/// A callee-saved register's value at entry: the frame pointer is the
/// frame's (before register allocation the selector names RBP only to read
/// the incoming stack area), every other one the caller's garbage.
fn preserved_value(world: &World, root: u16) -> u64 {
    if root == RBP {
        FRAME_BASE
    } else {
        world.garbage(0xCA11_EE, u64::from(root))
    }
}
const PRESERVED: [u16; 6] = [RBX, RBP, R12, R13, R14, R15];
const XMM0: u16 = 64;

/// Run the pre-RA machine stream on argument registers `raw`.
fn run_machine(
    machine: &X86ISelFunction,
    returns: &[Type],
    raw: &[u64],
    world: &mut World,
    bool_bits: u32,
) -> String {
    // General-purpose registers hold 64 bits, SSE registers 128.
    let mut regs: HashMap<Key, u128> = HashMap::new();
    for (i, value) in raw.iter().enumerate().take(6) {
        regs.insert(Key::P(ARG_REGS[i]), u128::from(*value));
    }
    for i in 0..8usize {
        let garbage = world.garbage(0x3333, i as u64);
        regs.insert(
            Key::P(XMM0 + i as u16),
            (u128::from(garbage) << 64) | u128::from(raw[6 + i]),
        );
    }
    for root in PRESERVED {
        regs.insert(Key::P(root), u128::from(preserved_value(world, root)));
    }
    regs.insert(Key::P(RSP), u128::from(INITIAL_RSP));
    // The caller's incoming stack eightbytes, above the saved frame pointer
    // and the return address.
    for (k, value) in raw.iter().skip(14).enumerate() {
        world.write(FRAME_BASE + 16 + 8 * k as u64, 8, u128::from(*value));
    }
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
        let garbage_wide = (u128::from(world.garbage(0x6A6B, steps)) << 64) | u128::from(garbage);
        let read = |regs: &HashMap<Key, u128>,
                    operand: &O,
                    world: &World|
         -> Result<(u128, u32), String> {
            let (key, bits, _) =
                operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
            let value = regs.get(&key).copied().unwrap_or_else(|| {
                u128::from(world.garbage(
                    0x0DEF,
                    steps
                        ^ (u64::from(match key {
                            Key::V(id) => id,
                            Key::P(p) => 100_000 + u32::from(p),
                        }) << 20),
                ))
            });
            Ok((mask128(value, bits), bits))
        };
        // A write of `bits` bits. A general-purpose register: 64 is the whole
        // root, 32 zero-extends, an 8- or 16-bit write keeps the bits above
        // in a physical register and leaves garbage there in a virtual one.
        // An SSE register: `zero` zero-extends (a load, `movd`/`movq` to
        // XMM), else the bits above are kept in a physical register (the
        // hardware merge of `movss`/`movsd` between registers) and garbage in
        // a virtual one (the allocator's pure definition).
        let write = |regs: &mut HashMap<Key, u128>,
                     operand: &O,
                     bits: u32,
                     value: u128,
                     zero: bool|
         -> Result<(), String> {
            let (key, _, sse) =
                operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
            let width = if sse { 128 } else { 64 };
            let above = match key {
                Key::P(_) => regs.get(&key).copied().unwrap_or(garbage_wide),
                Key::V(_) => garbage_wide,
            };
            let value = if bits >= width || (!sse && bits == 32) || zero {
                mask128(value, bits)
            } else {
                (above & !mask128(u128::MAX, bits)) | mask128(value, bits)
            };
            regs.insert(key, mask128(value, width));
            Ok(())
        };
        // A general-purpose register's whole 64 bits as a REX.W row reads
        // them: a 32-bit virtual register's bits above 31 are garbage.
        let read_wide =
            |regs: &HashMap<Key, u128>, operand: &O, world: &World| -> Result<u128, String> {
                let (key, bits, _) =
                    operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
                let (low, _) = read(regs, operand, world)?;
                Ok(match (key, bits) {
                    (Key::V(_), 32) => (u128::from(garbage) << 32) | low,
                    (Key::P(_), _) => mask128(regs.get(&key).copied().unwrap_or(low), 64),
                    _ => low,
                })
            };
        // A REX.W write: all 64 bits of the destination's register.
        let write_wide = |regs: &mut HashMap<Key, u128>, operand: &O, value: u128| {
            let (key, _, _) =
                operand_reg(operand).ok_or_else(|| format!("gt: operand {operand:?}"))?;
            regs.insert(key, mask128(value, 64));
            Ok::<(), String>(())
        };
        let address =
            |regs: &HashMap<Key, u128>, operand: &O, world: &World| -> Result<u64, String> {
                match operand {
                    O::MemAddr { base, disp } => {
                        let base = match base.as_ref() {
                            O::StackSlot(slot) => slot_base(*slot),
                            other => read(regs, other, world)?.0 as u64,
                        };
                        Ok(base.wrapping_add(i64::from(*disp) as u64))
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
        // The two-operand (tied) forms compute `d = d op x`; a one-operand
        // shift by CL `d = d op CL`.
        let ops: Vec<O> = match (inst.opcode, inst.operands.as_slice()) {
            (
                X86Opcode::OrRR
                | X86Opcode::AndRR
                | X86Opcode::XorRR
                | X86Opcode::AddRR
                | X86Opcode::SubRR
                | X86Opcode::AdcRR
                | X86Opcode::SbbRR
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
            (X86Opcode::ShlRR | X86Opcode::ShrRR | X86Opcode::SarRR | X86Opcode::Not, [d]) => {
                vec![d.clone(), d.clone()]
            }
            _ => inst.operands.clone(),
        };
        let gpr_bits = |operand: &O| operand_reg(operand).map(|(_, bits, _)| bits);
        let step: Result<Option<String>, String> = (|| {
            use X86Opcode as X;
            match inst.opcode {
                X::Nop => {}
                // A copy of mixed widths: REX.W, all 64 bits of the source's
                // register, whose bits above 31 are garbage when it is a
                // 32-bit virtual register (the allocator keeps its low half).
                X::MovRR if gpr_bits(&ops[0]) != gpr_bits(&ops[1]) => {
                    let v = read_wide(&regs, &ops[1], world)?;
                    write_wide(&mut regs, &ops[0], v)?;
                }
                X::MovRR => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], gpr_bits(&ops[0]).ok_or("gt")?, v, false)?;
                }
                // The constant pool: the entry's bytes, the rest of the
                // register zeroed.
                X::MovssRipRel | X::MovsdRipRel => {
                    let O::ConstPoolEntry(index) = ops[1] else {
                        return Err("gt: constant-pool operand".into());
                    };
                    let data = &machine
                        .const_pool_entries
                        .get(index)
                        .ok_or("fault: no constant-pool entry")?
                        .data;
                    let bytes = if inst.opcode == X::MovssRipRel { 4 } else { 8 };
                    if data.len() < bytes {
                        return Err("fault: short constant-pool entry".into());
                    }
                    let value = data[..bytes]
                        .iter()
                        .rev()
                        .fold(0u128, |v, b| (v << 8) | u128::from(*b));
                    write(&mut regs, &ops[0], 128, value, true)?;
                }
                // Bitwise over the whole 128-bit registers.
                X::Pxor | X::Andps | X::Andpd => {
                    let whole = |regs: &HashMap<Key, u128>, operand: &O| -> Result<u128, String> {
                        let (key, _, _) = operand_reg(operand)
                            .ok_or_else(|| format!("gt: operand {operand:?}"))?;
                        Ok(regs.get(&key).copied().unwrap_or(garbage_wide))
                    };
                    let a = whole(&regs, &ops[1])?;
                    let b = whole(&regs, &ops[2])?;
                    let value = if inst.opcode == X::Pxor { a ^ b } else { a & b };
                    write(&mut regs, &ops[0], 128, value, true)?;
                }
                X::MovRR32 => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], 32, v, false)?;
                }
                X::MovRI => {
                    let O::Imm(imm) = ops[1] else {
                        return Err("gt: MovRI".into());
                    };
                    let bits = gpr_bits(&ops[0]).ok_or("gt")?;
                    write(&mut regs, &ops[0], bits, u128::from(imm as u64), false)?;
                }
                X::Movzx | X::MovzxW | X::MovsxB | X::MovsxW | X::Movsx => {
                    let (v, _) = read(&regs, &ops[1], world)?;
                    let from = match inst.opcode {
                        X::Movzx | X::MovsxB => 8,
                        X::MovzxW | X::MovsxW => 16,
                        _ => 32,
                    };
                    let v = v as u64;
                    let value = if matches!(inst.opcode, X::Movzx | X::MovzxW) {
                        mask64(v, from)
                    } else {
                        sext64(v, from)
                    };
                    write(&mut regs, &ops[0], 64, u128::from(value), false)?;
                }
                // SSE moves.
                X::MovssRR | X::MovsdRR => {
                    let bits = if inst.opcode == X::MovssRR { 32 } else { 64 };
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], bits, v, false)?;
                }
                X::MovdFromXmm | X::MovqFromXmm => {
                    let bits = if inst.opcode == X::MovdFromXmm {
                        32
                    } else {
                        64
                    };
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], bits, mask128(v, bits), false)?;
                }
                X::MovdToXmm | X::MovqToXmm => {
                    let bits = if inst.opcode == X::MovdToXmm { 32 } else { 64 };
                    let (v, _) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], 128, mask128(v, bits), true)?;
                }
                X::AddRR | X::SubRR | X::ImulRR | X::AndRR | X::OrRR | X::XorRR
                    if ops.len() == 3
                        && matches!(&ops[2], O::VReg(_) | O::PReg(_))
                        && (gpr_bits(&ops[0]) != gpr_bits(&ops[1])
                            || gpr_bits(&ops[1]) != gpr_bits(&ops[2])) =>
                {
                    // Mixed widths: REX.W, a 64-bit operation of the
                    // registers' whole contents.
                    let a = read_wide(&regs, &ops[1], world)? as u64;
                    let b = read_wide(&regs, &ops[2], world)? as u64;
                    let r = match inst.opcode {
                        X::AddRR => a.wrapping_add(b),
                        X::SubRR => a.wrapping_sub(b),
                        X::ImulRR => a.wrapping_mul(b),
                        X::AndRR => a & b,
                        X::OrRR => a | b,
                        _ => a ^ b,
                    };
                    flags = None;
                    write_wide(&mut regs, &ops[0], u128::from(r))?;
                }
                X::AddRR
                | X::SubRR
                | X::AdcRR
                | X::SbbRR
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
                    let bits = gpr_bits(&ops[0]).ok_or("gt")?;
                    let a = read(&regs, &ops[1], world)?.0 as u64;
                    let b = match &ops[2] {
                        O::Imm(imm) => mask64(i64::from(*imm as i32) as u64, bits),
                        other => read(&regs, other, world)?.0 as u64,
                    };
                    let carry_in = match inst.opcode {
                        X::AdcRR | X::SbbRR => match flags {
                            Some(f) => u64::from(f.cf),
                            // Undefined flags: a garbage carry.
                            None => garbage & 1,
                        },
                        _ => 0,
                    };
                    let shift = (b & if bits == 64 { 63 } else { 31 }) as u32;
                    let wide = |x: u64| u128::from(mask64(x, bits));
                    let r = match inst.opcode {
                        X::AddRR | X::AddRI => a.wrapping_add(b),
                        X::AdcRR => a.wrapping_add(b).wrapping_add(carry_in),
                        X::SubRR | X::SubRI => a.wrapping_sub(b),
                        X::SbbRR => a.wrapping_sub(b).wrapping_sub(carry_in),
                        X::ImulRR => a.wrapping_mul(b),
                        X::AndRR | X::AndRI => a & b,
                        X::OrRR | X::OrRI => a | b,
                        X::XorRR | X::XorRI => a ^ b,
                        X::ShlRI => a << shift,
                        X::ShrRI => mask64(a, bits) >> shift,
                        _ => (sext64(a, bits) as i64 >> shift) as u64,
                    };
                    let r = mask64(r, bits);
                    let msb = |x: u64| (x >> (bits - 1)) & 1 == 1;
                    flags = match inst.opcode {
                        X::AddRR | X::AddRI | X::AdcRR => {
                            let full = wide(a) + wide(b) + u128::from(carry_in);
                            Some(eflags_of(
                                r,
                                bits,
                                full >> bits != 0,
                                msb(!(a ^ b) & (a ^ r)),
                            ))
                        }
                        X::SubRR | X::SubRI | X::SbbRR => {
                            let borrow = wide(a) < wide(b) + u128::from(carry_in);
                            Some(eflags_of(r, bits, borrow, msb((a ^ b) & (a ^ r))))
                        }
                        X::AndRR | X::AndRI | X::OrRR | X::OrRI | X::XorRR | X::XorRI => {
                            Some(eflags_of(r, bits, false, false))
                        }
                        _ if shift == 0
                            && matches!(inst.opcode, X::ShlRI | X::ShrRI | X::SarRI) =>
                        {
                            flags
                        }
                        _ => None,
                    };
                    write(&mut regs, &ops[0], bits, u128::from(r), false)?;
                }
                X::Not => {
                    let (v, bits) = read(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], bits, !v, false)?;
                }
                X::ShlRR | X::ShrRR | X::SarRR => {
                    let (a, bits) = read(&regs, &ops[1], world)?;
                    let a = a as u64;
                    let cl = regs
                        .get(&Key::P(RCX))
                        .copied()
                        .unwrap_or(u128::from(garbage)) as u64
                        & 0xff;
                    let shift = (cl & if bits == 64 { 63 } else { 31 }) as u32;
                    let r = match inst.opcode {
                        X::ShlRR => a << shift,
                        X::ShrRR => mask64(a, bits) >> shift,
                        _ => (sext64(a, bits) as i64 >> shift) as u64,
                    };
                    if shift != 0 {
                        flags = None;
                    }
                    write(&mut regs, &ops[0], bits, u128::from(mask64(r, bits)), false)?;
                }
                X::Mul => {
                    let (source, bits) = read(&regs, &ops[0], world)?;
                    let accumulator = mask64(
                        regs.get(&Key::P(RAX))
                            .copied()
                            .unwrap_or(u128::from(garbage)) as u64,
                        bits,
                    );
                    let product = u128::from(accumulator) * source;
                    let low = mask64(product as u64, bits);
                    let high = mask64((product >> bits) as u64, bits);
                    regs.insert(Key::P(RAX), u128::from(low));
                    regs.insert(Key::P(RDX), u128::from(high));
                    flags = Some(Eflags {
                        cf: high != 0,
                        of: high != 0,
                        zf: garbage & 1 == 1,
                        sf: garbage & 2 == 2,
                        pf: garbage & 4 == 4,
                    });
                }
                X::Lea => {
                    let a = address(&regs, &ops[1], world)?;
                    write(&mut regs, &ops[0], 64, u128::from(a), false)?;
                }
                X::MovRM8 | X::MovRM16 | X::MovRM32 | X::MovRM | X::MovssRM | X::MovsdRM => {
                    let a = address(&regs, &ops[1], world)?;
                    let bytes = match inst.opcode {
                        X::MovRM8 => 1,
                        X::MovRM16 => 2,
                        X::MovRM32 | X::MovssRM => 4,
                        _ => 8,
                    };
                    let v = world.read(a, bytes);
                    let zero = matches!(inst.opcode, X::MovssRM | X::MovsdRM);
                    write(&mut regs, &ops[0], bytes * 8, v, zero)?;
                }
                // `movzx r32, m8/m16`: the bytes zero-extended into the whole
                // register (Intel SDM MOVZX).
                X::MovzxRM8 | X::MovzxRM16 => {
                    let a = address(&regs, &ops[1], world)?;
                    let bytes = if inst.opcode == X::MovzxRM8 { 1 } else { 2 };
                    let v = world.read(a, bytes);
                    write(&mut regs, &ops[0], 64, v, false)?;
                }
                X::MovMR8 | X::MovMR16 | X::MovMR32 | X::MovMR | X::MovssMR | X::MovsdMR => {
                    let a = address(&regs, &ops[0], world)?;
                    let bytes = match inst.opcode {
                        X::MovMR8 => 1,
                        X::MovMR16 => 2,
                        X::MovMR32 | X::MovssMR => 4,
                        _ => 8,
                    };
                    let (v, _) = read(&regs, &ops[1], world)?;
                    world.write(a, bytes, v);
                }
                X::CmpRR | X::CmpRI | X::TestRR | X::TestRI => {
                    let (a, bits) = read(&regs, &ops[0], world)?;
                    let a = a as u64;
                    let b = match &ops[1] {
                        O::Imm(imm) => mask64(i64::from(*imm as i32) as u64, bits),
                        other => read(&regs, other, world)?.0 as u64,
                    };
                    let msb = |x: u64| (x >> (bits - 1)) & 1 == 1;
                    flags = Some(if matches!(inst.opcode, X::CmpRR | X::CmpRI) {
                        let r = mask64(a.wrapping_sub(b), bits);
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
                    write(&mut regs, &ops[0], 8, u128::from(holds), false)?;
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
                    write(&mut regs, &ops[0], bits, value, false)?;
                }
                X::Call if matches!(&ops[0], O::Symbol(name) if matches!(name.as_str(), "memcpy" | "memmove" | "memset")) =>
                {
                    let O::Symbol(name) = &ops[0] else {
                        unreachable!()
                    };
                    let reg = |root: u16| {
                        regs.get(&Key::P(root))
                            .copied()
                            .unwrap_or_else(|| u128::from(world.garbage(0xA5A, steps)))
                            as u64
                    };
                    let args = [reg(RDI), reg(RSI), reg(RDX)];
                    world.memory_routine(name, args)?;
                    for (k, root) in [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11]
                        .iter()
                        .enumerate()
                    {
                        regs.insert(
                            Key::P(*root),
                            u128::from(world.garbage(0xC10B, steps * 16 + k as u64)),
                        );
                    }
                    flags = None;
                }
                X::Call => {
                    let O::Symbol(name) = &ops[0] else {
                        return Err("gt: call operand".into());
                    };
                    let (params, results) = callee(name).ok_or("gt: callee")?;
                    let placed = placement(&params).ok_or("gt: placement")?;
                    let rsp = regs.get(&Key::P(RSP)).copied().unwrap_or(0) as u64;
                    let reg = |index: u16| -> u128 {
                        // A stack argument: the callee's `k`-th eightbyte
                        // above RSP at the call.
                        if index >= 200 {
                            return u128::from(
                                world.peek_word(rsp.wrapping_add(8 * u64::from(index - 200))),
                            );
                        }
                        let key = if index >= 100 {
                            Key::P(XMM0 + index - 100)
                        } else {
                            Key::P(ARG_REGS[usize::from(index)])
                        };
                        regs.get(&key)
                            .copied()
                            .unwrap_or_else(|| u128::from(world.garbage(0xA59, steps)))
                    };
                    let values: Vec<u128> = params
                        .iter()
                        .zip(&placed)
                        .map(|(kind, registers)| match kind {
                            Kind::Wide | Kind::Pair => {
                                (mask128(reg(registers[1]), 64) << 64)
                                    | mask128(reg(registers[0]), 64)
                            }
                            // The clean 32-bit bool every callee reads.
                            Kind::Int(1) => mask128(reg(registers[0]), 32),
                            other => mask128(reg(registers[0]), bits_of(*other)),
                        })
                        .collect();
                    let out = world
                        .call(name, &values)
                        .map_err(|e| format!("fault: {e}"))?;
                    for (k, root) in [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11]
                        .iter()
                        .enumerate()
                    {
                        regs.insert(
                            Key::P(*root),
                            u128::from(world.garbage(0xC10B, steps * 16 + k as u64)),
                        );
                    }
                    for x in 0..16u16 {
                        regs.insert(
                            Key::P(XMM0 + x),
                            (u128::from(world.garbage(0xC10C, steps * 32 + u64::from(x))) << 64)
                                | u128::from(world.garbage(0xC10D, steps * 32 + u64::from(x))),
                        );
                    }
                    // Results: integer lanes in RAX, RDX; float lanes in
                    // XMM0, XMM1; the bits above a lane's width garbage.
                    let (mut gpr, mut sse) = (0usize, 0u16);
                    for (kind, value) in results.iter().zip(out) {
                        match kind {
                            Kind::Float(bits) => {
                                let key = Key::P(XMM0 + sse);
                                sse += 1;
                                let above = regs[&key] & !mask128(u128::MAX, *bits);
                                regs.insert(key, above | mask128(value, *bits));
                            }
                            Kind::Wide | Kind::Pair => {
                                regs.insert(Key::P(RAX), mask128(value, 64));
                                regs.insert(Key::P(RDX), value >> 64);
                                gpr += 2;
                            }
                            Kind::Bytes(n) => {
                                let key = Key::P([RAX, RDX][gpr]);
                                gpr += 1;
                                let above = regs[&key] & !mask128(u128::MAX, 8 * n);
                                regs.insert(key, above | mask128(value, 8 * n));
                            }
                            Kind::Int(bits) => {
                                let key = Key::P([RAX, RDX][gpr]);
                                gpr += 1;
                                // A `bool` defines AL as 0 or 1.
                                let bits = if *bits == 1 { 8 } else { *bits };
                                let above = regs[&key] & !mask128(u128::MAX, bits);
                                regs.insert(key, above | mask128(value, bits));
                            }
                        }
                    }
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
                            != Some(u128::from(preserved_value(world, root)))
                        {
                            return Ok(Some(format!("fault: callee-saved root {root} clobbered")));
                        }
                    }
                    if regs.get(&Key::P(RSP)).copied() != Some(u128::from(INITIAL_RSP)) {
                        return Ok(Some("fault: RSP not restored".into()));
                    }
                    let read_root = |key: Key| {
                        regs.get(&key)
                            .copied()
                            .unwrap_or_else(|| u128::from(world.garbage(0x2E7, steps)))
                    };
                    let kinds: Option<Vec<Kind>> = returns.iter().map(kind).collect();
                    let kinds = kinds.ok_or("gt: return kinds")?;
                    let (mut gpr, mut sse) = (0usize, 0u16);
                    let mut values = Vec::new();
                    for kind in &kinds {
                        values.push(match kind {
                            Kind::Float(_) => {
                                sse += 1;
                                read_root(Key::P(XMM0 + sse - 1))
                            }
                            Kind::Wide | Kind::Pair => {
                                gpr += 2;
                                (mask128(read_root(Key::P(RDX)), 64) << 64)
                                    | mask128(read_root(Key::P(RAX)), 64)
                            }
                            Kind::Int(_) | Kind::Bytes(_) => {
                                gpr += 1;
                                read_root(Key::P([RAX, RDX][gpr - 1]))
                            }
                        });
                    }
                    return Ok(Some(returned_text(&kinds, &values, bool_bits)));
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

fn ground_truth(source: &Function, machine: &X86ISelFunction) -> Truth {
    let mut truth = Truth::default();
    // A `bool` parameter's register follows the input's caller convention:
    // a psABI caller clears bits 1..7 (bit 0 the value, the bits above
    // anything) and reads AL of a `bool` result; a clean-bool caller (the
    // backend's own, LLVM's) clears bits 1..31 and reads EAX. A function
    // without a `bool` parameter returns the clean 32-bit bool to both.
    let bool_registers: Vec<u16> = source
        .signature
        .params
        .iter()
        .map(kind)
        .collect::<Option<Vec<Kind>>>()
        .and_then(|kinds| {
            let placed = placement(&kinds)?;
            Some(
                kinds
                    .iter()
                    .zip(placed)
                    .filter(|(kind, _)| **kind == Kind::Int(1))
                    .map(|(_, registers)| registers[0])
                    .collect(),
            )
        })
        .unwrap_or_default();
    for seed in 0..GT_INPUTS {
        let mut raw = gt_registers(seed);
        let psabi = seed % 2 == 0;
        for register in &bool_registers {
            let index = if *register >= 200 {
                14 + usize::from(*register - 200)
            } else {
                usize::from(*register)
            };
            raw[index] &= if psabi { !0xfe } else { !0xffff_fffe };
        }
        let bool_bits = if psabi && !bool_registers.is_empty() {
            8
        } else {
            32
        };
        let mut world = World::new(seed);
        let end = run_source(source, &raw, &mut world, bool_bits);
        if end == "ub" {
            continue;
        }
        let expected = world.finish(end);
        let mut world = World::new(seed);
        let end = run_machine(
            machine,
            &source.signature.returns,
            &raw,
            &mut world,
            bool_bits,
        );
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

const CLASSES: [&str; 14] = [
    "C0 original",
    "C1 wrong condition code",
    "C2 operands swapped",
    "C3 wrong operation (carry, shift, width, mask)",
    "C4 ABI register replaced (GPR or XMM)",
    "C5 wrong source register",
    "C6 row dropped",
    "C7 wrong immediate",
    "C8 wrong memory displacement",
    "C9 atomic origin dropped",
    "C10 constant-pool bits flipped",
    "C11 bool parameter not zero-extended",
    "C12 register width flipped",
    "C13 escaped slot written before an access",
];

struct Mutant {
    class: usize,
    label: String,
    machine: X86ISelFunction,
}

/// The ABI register a physical operand names: an integer argument or result
/// register, RCX, or XMM0-XMM2.
fn abi_root(operand: &O) -> Option<(u16, bool)> {
    match operand_reg(operand) {
        Some((Key::P(root), _, false))
            if ARG_REGS.contains(&root) || root == RAX || root == RDX || root == RCX =>
        {
            Some((root, false))
        }
        Some((Key::P(root), _, true)) if (XMM0..XMM0 + 3).contains(&root) => Some((root, true)),
        _ => None,
    }
}

/// `operand` with its physical root replaced by `root` at the same width.
fn with_root(operand: &O, root: u16, sse: bool) -> Option<O> {
    let O::PReg(preg) = operand else {
        return None;
    };
    if sse {
        return Some(O::PReg(X86PReg::new(root)));
    }
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
    for (ordinal, _, _) in &all {
        let ordinal = *ordinal;
        let row = inst(base, ordinal).clone();
        // C1: a flag reader's condition replaced by every other one.
        if let Some(k) = row
            .operands
            .iter()
            .position(|operand| matches!(operand, O::CondCode(_)))
        {
            let O::CondCode(cc) = row.operands[k] else {
                unreachable!()
            };
            for other in ALL_CONDITIONS {
                if other == cc {
                    continue;
                }
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[k] = O::CondCode(other);
                push(1, format!("row {ordinal}: {other:?} (was {cc:?})"), m);
            }
        }
        // C2: the two source operands of a three-address row swapped.
        if matches!(
            row.opcode,
            X86Opcode::AddRR
                | X86Opcode::SubRR
                | X86Opcode::AdcRR
                | X86Opcode::SbbRR
                | X86Opcode::ImulRR
                | X86Opcode::CmpRR
                | X86Opcode::OrRR
        ) && row.operands.len() >= 2
        {
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
        // C3: another operation of the same shape: the carry dropped or
        // added, the other direction or signedness of a shift, the other
        // SSE width.
        let others: &[X86Opcode] = match row.opcode {
            X86Opcode::AddRR => &[X86Opcode::AdcRR, X86Opcode::SubRR, X86Opcode::OrRR],
            X86Opcode::AdcRR => &[X86Opcode::AddRR, X86Opcode::SbbRR],
            X86Opcode::SubRR => &[X86Opcode::SbbRR, X86Opcode::AddRR],
            X86Opcode::SbbRR => &[X86Opcode::SubRR, X86Opcode::AdcRR],
            X86Opcode::ImulRR => &[X86Opcode::AddRR],
            X86Opcode::Not => &[X86Opcode::MovRR],
            X86Opcode::ShlRR => &[X86Opcode::ShrRR, X86Opcode::SarRR],
            X86Opcode::ShrRR => &[X86Opcode::SarRR, X86Opcode::ShlRR],
            X86Opcode::SarRR => &[X86Opcode::ShrRR],
            X86Opcode::SarRI => &[X86Opcode::ShrRI],
            X86Opcode::MovssRR => &[X86Opcode::MovsdRR],
            X86Opcode::MovsdRR => &[X86Opcode::MovssRR],
            X86Opcode::MovqFromXmm => &[X86Opcode::MovdFromXmm],
            X86Opcode::MovdFromXmm => &[X86Opcode::MovqFromXmm],
            X86Opcode::MovqToXmm => &[X86Opcode::MovdToXmm],
            X86Opcode::MovdToXmm => &[X86Opcode::MovqToXmm],
            X86Opcode::MovsdRM => &[X86Opcode::MovssRM],
            X86Opcode::MovssMR => &[X86Opcode::MovsdMR],
            X86Opcode::Movzx => &[X86Opcode::MovsxB],
            X86Opcode::Pxor => &[X86Opcode::Andps, X86Opcode::Andpd],
            X86Opcode::Andps => &[X86Opcode::Pxor, X86Opcode::Andpd],
            X86Opcode::Andpd => &[X86Opcode::Pxor, X86Opcode::Andps],
            X86Opcode::MovssRipRel => &[X86Opcode::MovsdRipRel],
            X86Opcode::MovsdRipRel => &[X86Opcode::MovssRipRel],
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
        // C4: an ABI register operand replaced by another of its file.
        for (k, operand) in row.operands.iter().enumerate() {
            let Some((root, sse)) = abi_root(operand) else {
                continue;
            };
            let replacements: &[u16] = if sse {
                &[XMM0, XMM0 + 1, XMM0 + 2]
            } else {
                &[RDI, RSI, RDX, RAX, RCX]
            };
            for other in replacements {
                if *other == root {
                    continue;
                }
                let Some(replaced) = with_root(operand, *other, sse) else {
                    continue;
                };
                let mut m = base.clone();
                inst_mut(&mut m, ordinal).operands[k] = replaced;
                push(
                    4,
                    format!(
                        "row {ordinal} operand {k}: {} for {}",
                        root_name(*other),
                        root_name(root)
                    ),
                    m,
                );
            }
        }
        // C5: a source register replaced by an earlier virtual register of
        // the same class.
        if let Some(k) = row
            .operands
            .iter()
            .rposition(|operand| matches!(operand, O::VReg(_)))
            && (k > 0 || matches!(row.opcode, X86Opcode::Mul))
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
            X86Opcode::Jmp | X86Opcode::Jcc | X86Opcode::Ret | X86Opcode::Call | X86Opcode::Ud2
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
            for other in [imm ^ 1, imm >> 1, imm.wrapping_add(64), -1, 0] {
                if other == imm {
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
        // C9: an atomic access's origin dropped (a plain `mov`).
        if row.proof_origin.is_some() {
            let mut m = base.clone();
            inst_mut(&mut m, ordinal).proof_origin = None;
            push(
                9,
                format!("row {ordinal}: {:?} origin dropped", row.opcode),
                m,
            );
        }
        // C8: a memory operand's displacement moved by 4 or 8 bytes.
        if let Some(k) = row
            .operands
            .iter()
            .position(|operand| matches!(operand, O::MemAddr { .. }))
        {
            for delta in [-8, -4, 4, 8] {
                let mut m = base.clone();
                if let O::MemAddr { disp, .. } = &mut inst_mut(&mut m, ordinal).operands[k] {
                    *disp += delta;
                }
                push(8, format!("row {ordinal}: displacement {delta:+}"), m);
            }
        }
        // C11: a `bool` parameter's entry `movzx` of its low byte replaced by
        // the 32-bit copy (the selector before slice 15).
        if row.opcode == X86Opcode::Movzx
            && matches!(row.operands.get(1), Some(O::PReg(p)) if (16..32).contains(&p.encoding()))
        {
            let mut m = base.clone();
            inst_mut(&mut m, ordinal).opcode = X86Opcode::MovRR32;
            push(
                11,
                format!("row {ordinal}: entry movzx as a 32-bit copy"),
                m,
            );
        }
        // C12: a general-purpose register operand's width flipped (32 <-> 64).
        for (k, operand) in row.operands.iter().enumerate() {
            let flipped = match operand {
                O::VReg(v) if v.class == RegClass::Gpr32 => {
                    O::VReg(VReg::new(v.id, RegClass::Gpr64))
                }
                O::VReg(v) if v.class == RegClass::Gpr64 => {
                    O::VReg(VReg::new(v.id, RegClass::Gpr32))
                }
                O::PReg(p) if p.encoding() < 16 => O::PReg(X86PReg::new(p.encoding() + 16)),
                O::PReg(p) if (16..32).contains(&p.encoding()) => {
                    O::PReg(X86PReg::new(p.encoding() - 16))
                }
                _ => continue,
            };
            if !matches!(
                row.opcode,
                X86Opcode::MovRR
                    | X86Opcode::MovRR32
                    | X86Opcode::OrRR
                    | X86Opcode::AddRR
                    | X86Opcode::AndRR
                    | X86Opcode::XorRR
            ) {
                continue;
            }
            let mut m = base.clone();
            inst_mut(&mut m, ordinal).operands[k] = flipped;
            push(12, format!("row {ordinal} operand {k}: width flipped"), m);
        }
    }
    // C10: each constant-pool entry with a bit flipped (the sign bit, bit 0,
    // a payload bit).
    for (index, entry) in base.const_pool_entries.iter().enumerate() {
        for bit in [0usize, 22, 31, 51, 63] {
            if bit / 8 >= entry.data.len() {
                continue;
            }
            let mut m = base.clone();
            m.const_pool_entries[index].data[bit / 8] ^= 1 << (bit % 8);
            push(10, format!("constant {index}: bit {bit} flipped"), m);
        }
    }
    // C13: a word stored into private slot 0 just before each incoming load
    // or store after the first call (an escaped slot written behind an
    // access through a derived address).
    if let Some(first_call) = all
        .iter()
        .map(|(o, _, _)| *o)
        .find(|o| inst(base, *o).opcode == X86Opcode::Call)
    {
        for (ordinal, _, _) in all.iter().filter(|(o, _, _)| *o > first_call) {
            let row = inst(base, *ordinal);
            let incoming = memory_access(row.opcode).is_some()
                && row.operands.iter().any(|operand| {
                    matches!(operand, O::MemAddr { base, .. } if matches!(**base, O::VReg(_)))
                });
            if !incoming || base.stack_slots.is_empty() {
                continue;
            }
            let mut m = base.clone();
            let word = O::VReg(VReg::new(m.next_vreg + 50, RegClass::Gpr64));
            insert_at(
                &mut m,
                *ordinal,
                X86ISelInst::new(X86Opcode::MovRI, vec![word.clone(), O::Imm(0x1234)]),
            );
            insert_at(
                &mut m,
                *ordinal + 1,
                X86ISelInst::new(
                    X86Opcode::MovMR,
                    vec![
                        O::MemAddr {
                            base: Box::new(O::StackSlot(0)),
                            disp: 0,
                        },
                        word,
                    ],
                ),
            );
            push(13, format!("slot 0 written before row {ordinal}"), m);
        }
    }
    // `describe` prints neither a row's proof origin, which C9 changes, nor
    // the constant pool, which C10 changes.
    let key = |machine: &X86ISelFunction| {
        let origins: Vec<_> = rows(machine)
            .into_iter()
            .map(|(ordinal, _, _)| inst(machine, ordinal).proof_origin)
            .collect();
        let pool: Vec<_> = machine
            .const_pool_entries
            .iter()
            .map(|entry| entry.data.clone())
            .collect();
        format!("{}{origins:?}{pool:?}", describe(machine))
    };
    let mut seen = HashSet::new();
    out.retain(|m| seen.insert(key(&m.machine)));
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
    for shape in all_slice_fifteen_shapes() {
        if only.is_some_and(|only| !format!("{shape:?}").contains(only)) {
            continue;
        }
        let (source, selected) = slice15_pair(shape);
        for (level, base) in &optimized_bases(&selected) {
            for mutant in mutants(base) {
                let row = &mut probe.table[mutant.class];
                row.n += 1;
                let tag = format!(
                    "{shape:?}@{level} [{}] {}",
                    CLASSES[mutant.class], mutant.label
                );
                let truth = ground_truth(&source, &mutant.machine);
                if let Some(reason) = &truth.unsupported {
                    row.gt_na += 1;
                    eprintln!("ROB15 GT-NA {tag}: {reason}");
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
                        eprintln!("ROB15 {tag}: unsupported ({reason}) gt_wrong={wrong}");
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
                        eprintln!("ROB15 {tag}: mismatch ({other}) gt_wrong={wrong}");
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
                    "ROB15 {tag}: theorem sample_refuted={sample_refuted} ay={ay} credited={credited} gt_wrong={wrong}"
                );
            }
        }
    }
    probe
}

#[test]
#[ignore]
fn slice_fifteen_mutation_robustness() {
    let test = "slice_fifteen_mutation_robustness";
    let only = std::env::var("ROB15_ONLY").ok();
    let edits = if std::env::var_os("ROB15_NO_REPLAY").is_some() {
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
        "\nROB15 TABLE replay={} (n | owner unsupported | owner mismatch | theorem | sample-refuted | AY CE | AY CE not sampled | AY Valid | AY other | credited || GT-wrong: total / unsupported / mismatch / refuted / CREDITED-or-VALID || GT-correct but refuted | GT n/a)",
        edits.is_some()
    );
    for (class, row) in CLASSES.iter().zip(&probe.table) {
        eprintln!(
            "ROB15 {class:<42} {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} | {:>4} || {:>4} / {:>4} / {:>4} / {:>4} / {:>4} || {:>4} | {:>3}",
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
    eprintln!("ROB15 conservative ({}):", probe.conservative.len());
    for line in &probe.conservative {
        eprintln!("ROB15-C {line}");
    }
    eprintln!("ROB15 findings ({}):", probe.findings.len());
    for line in &probe.findings {
        eprintln!("ROB15-F {line}");
    }
}
