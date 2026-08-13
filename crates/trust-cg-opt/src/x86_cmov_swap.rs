// trust-cg-opt - x86-64 branchless conditional-swap (task #77): sort-loop
// compare-and-swap diamonds -> CMOVcc min/max + unconditional store pair
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! OPT-IN (`TCG_X86_CMOV_SWAP=1`) branchless conditional-swap for the sort
//! inner-loop diamond
//!
//! ```text
//! if a[j-1] > a[j] { let t = a[j-1]; a[j-1] = a[j]; a[j] = t; }
//! ```
//!
//! # The shape converted (matched against the REAL post-`X86LoopRotate` b06
//! bubble-sort ISel stream — see the module tests, which reproduce it)
//!
//! ```text
//!   ...prefix (single-pred chain into the guard):
//!     P1:  x = j; xm1 = x-1; cmp xm1, N; jcc B P2; jmp TRAP     (bounds check)
//!     P2:  va = load [base + xm1*4]; cmp j, N; jcc B G; jmp TRAP
//!   G:     vb = load [base + j*4]
//!          cmp va, vb
//!          jcc cc  ARM          ; cc-taken = the swap arm
//!          jmp     F            ; F = empty forwarder to the join J
//!   ARM (single-pred chain, deleted by the rewrite):
//!          re-derives j-1/j, RE-CHECKS the same bounds (each check identical
//!          to a prefix check, so provably dead), RE-LOADS a[j-1]/a[j]
//!          (provably the same values — no store in between), and stores the
//!          pair CROSSED:  [base+(j-1)*4] <- vb ; [base+j*4] <- va ; jmp J
//! ```
//!
//! becomes, in `G` (the guard `cmp` stays; its flags feed the CMOVs):
//!
//! ```text
//!          cmp     va, vb
//!          mov     lo, va
//!          cmovcc  cc, lo, vb    ; lo = cc ? vb : va
//!          mov     hi, vb
//!          cmovcc  cc, hi, va    ; hi = cc ? va : vb
//!          mov     [addrA], lo   ; addrA = the a[j-1] slot (guard-load addr)
//!          mov     [addrB], hi   ; addrB = the a[j]   slot
//!          jmp     F
//! ```
//!
//! Both stores execute UNCONDITIONALLY: on the not-taken path they write back
//! the exact values just loaded from those same addresses, which is
//! observationally equivalent for single-threaded, non-volatile memory (the
//! sort array is an ordinary stack/heap object the original program itself
//! writes through the same mutable place on the taken path).
//!
//! # Soundness argument (why every fired conversion is equivalence-preserving)
//!
//! The recognizer only fires when ALL of the following are PROVEN on the
//! matched region (guard + its single-predecessor prefix chain + the arm
//! chain), via a region value-numbering that resolves copies/adds/subs/scaled
//! multiplies and memory epochs:
//!
//! 1. **The guard compares two loads** `va = load addrA`, `vb = load addrB`
//!    executed on the straight-line path into the guard with NO intervening
//!    memory write or call (same memory epoch), where `addrA`/`addrB`
//!    normalize to the SAME base value and SAME scaled index root with
//!    DIFFERENT constant offsets — i.e. provably distinct addresses
//!    (equal-base/constant-offset-distinct; difference is a small nonzero
//!    constant, exact mod 2^64).
//! 2. **The arm is a pure re-derivation + crossed store pair.** Every arm
//!    instruction is on a strict whitelist: flag-free/flag-writing PURE
//!    register arithmetic (`mov`/`movri`/`add`/`sub`/`imul-imm`), reloads
//!    whose value-number equals `va`/`vb` (same normalized address, same
//!    epoch — no store can precede them, or the epoch differs and the match
//!    fails), bounds-check terminators, and EXACTLY TWO stores writing
//!    `vb -> addrA` and `va -> addrB` (the swap). Any call, trap carrier,
//!    push/pop, unknown opcode, physical-register touch, or extra store
//!    rejects the candidate. Deleting the arm's flag writes is safe because
//!    the arm is deleted whole and flags are dead at the join (the join was
//!    already reachable from the flag-divergent not-taken path).
//! 3. **Every arm bounds check is provably dead**: each arm
//!    `cmp v, imm; jcc cc CONT; jmp TRAP` (TRAP = a `Ud2`-only block) must be
//!    IDENTICAL — same value number, same immediate, same condition code,
//!    same orientation — to a check already executed on the dominating prefix
//!    path. On entry to the arm the check therefore passed already; removing
//!    it cannot suppress a trap that the original program would have taken.
//! 4. **No arm-defined vreg is used outside the arm** (function-wide scan),
//!    so deleting the arm leaves no dangling use; the store values are the
//!    ORIGINAL guard-load vregs, whose defs dominate the guard terminator.
//! 5. **The rewritten guard's flag state at the join is unchanged**: the
//!    inserted `mov`/`cmovcc`/store instructions are all flag-preserving, so
//!    the fall-through path sees exactly the flags the deleted `jcc` left —
//!    and the CMOVs read exactly the guard compare's flags (nothing between).
//!    No condition-code inversion is performed anywhere (the taken-cc is used
//!    directly for both CMOVs), so the wrong-inversion trap class cannot
//!    arise by construction.
//! 6. **The store addresses are re-materialized from the guard-load address
//!    operands**, re-validated (their base/index vregs still value-number to
//!    the load-time address at the guard terminator), never from the deleted
//!    arm.
//!
//! Downstream, every existing fail-closed stage (regalloc + validators,
//! per-instruction certs — `Cmovcc`/`Cmovcc32` are inside the cert-covered
//! surface — function verifier, decode-check) re-verifies the rewritten
//! function exactly as any ISel output.
//!
//! # Kill switch
//!
//! The pass is registered ONLY under `TCG_X86_CMOV_SWAP=1` (mirrors
//! `TCG_X86_TWOADDR_EXPAND` / the pre-flip `TCG_X86_WINDOW_SCAN` staging
//! pattern): the default pipeline is byte-identical with the variable unset.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::mach_view::predecessor_map;
use crate::x86_pass_manager::X86MachinePass;

/// Maximum blocks walked backwards from the guard (prefix chain) and forwards
/// through the arm chain. The b06 shape needs 3 and 5 respectively.
const MAX_CHAIN_BLOCKS: usize = 8;
/// Maximum conversions per run (defensive bound; each conversion strictly
/// shrinks the function so this is never hit in practice).
const MAX_CONVERSIONS: usize = 64;
/// Depth cap for the out-of-region single-def copy-chain resolver.
const MAX_COPY_CHAIN: usize = 16;

/// Branchless conditional-swap pass. See the module docs.
pub struct X86CmovSwap {
    /// Number of diamonds converted by the most recent run (diagnostics/tests).
    pub last_run_conversions: usize,
}

impl X86CmovSwap {
    pub fn new() -> Self {
        Self {
            last_run_conversions: 0,
        }
    }
}

impl Default for X86CmovSwap {
    fn default() -> Self {
        Self::new()
    }
}

impl X86MachinePass for X86CmovSwap {
    fn name(&self) -> &str {
        "x86-cmov-swap"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        self.last_run_conversions = 0;
        let mut changed = false;
        while self.last_run_conversions < MAX_CONVERSIONS {
            let Some(plan) = find_one(func) else {
                break;
            };
            apply(func, &plan);
            self.last_run_conversions += 1;
            changed = true;
        }
        if changed {
            renumber_blocks_contiguous(func);
        }
        changed
    }
}

// ---------------------------------------------------------------------------
// Region value numbering
// ---------------------------------------------------------------------------

/// Interned value key. Two vregs with the same value id are proven to hold the
/// same runtime value at their respective read points within the region.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum VKey {
    /// A region-external value: either the use itself (value at region entry;
    /// region redefinitions overwrite the vn map so later uses cannot alias
    /// it) or a globally-single-def vreg reached through a single-def copy
    /// chain (its value is fixed for the whole function).
    Leaf(VReg),
    /// Unique, never equal to anything (unmodeled def).
    Opaque(u32),
    Const(i64),
    /// `lea` of a fixed stack slot.
    LeaSlot(u32, i32),
    /// Unary op with immediate: `op(a, imm)` at the given width.
    Un {
        op: X86Opcode,
        w64: bool,
        a: u32,
        imm: i64,
    },
    /// Binary register op.
    Bin {
        op: X86Opcode,
        w64: bool,
        a: u32,
        b: u32,
    },
    /// `MovRR32` into a 64-bit destination (zero-extend).
    Zext(u32),
    /// A memory load: normalized address + width + memory epoch.
    Load {
        base: u32,
        root: Option<u32>,
        coeff: i64,
        c: i64,
        width: u8,
        epoch: u32,
    },
}

/// Normalized address: `value(base) + coeff * value(root) + c` (mod 2^64),
/// with `root == None` meaning a constant offset only.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct NormAddr {
    base: u32,
    root: Option<u32>,
    coeff: i64,
    c: i64,
}

impl NormAddr {
    /// Provably distinct addresses: same base value, same scaled root, and a
    /// different (wrapped) constant term — the byte difference is a nonzero
    /// constant mod 2^64, so the two addresses can never be equal.
    fn provably_distinct_from(&self, other: &NormAddr) -> bool {
        self.base == other.base
            && self.root == other.root
            && self.coeff == other.coeff
            && self.c != other.c
    }
}

struct Vn<'f> {
    func: &'f X86ISelFunction,
    intern: HashMap<VKey, u32>,
    keys: Vec<VKey>,
    map: HashMap<VReg, u32>,
    epoch: u32,
    opaque_counter: u32,
    /// Global def counts + single-def sites, for out-of-region resolution.
    def_count: HashMap<VReg, u32>,
    def_site: HashMap<VReg, (Block, usize)>,
    /// First (prefix-side) load instruction seen for a given load value id:
    /// the cloned address operand + the base/index vregs and their ids at
    /// load time (for re-validation at the guard).
    load_addr_ops: HashMap<u32, LoadAddrOp>,
}

#[derive(Clone)]
struct LoadAddrOp {
    operand: X86ISelOperand,
    /// The base register, if the SIB base is a `VReg` — re-validated at the
    /// guard. `None` when the base is a literal frame-invariant `StackSlot`
    /// (produced by the SIB-base address fold), which cannot go stale.
    base_vreg: Option<VReg>,
    index_vreg: Option<VReg>,
    base_id: u32,
    index_id: Option<u32>,
}

impl<'f> Vn<'f> {
    fn new(func: &'f X86ISelFunction) -> Self {
        let mut def_count: HashMap<VReg, u32> = HashMap::new();
        let mut def_site: HashMap<VReg, (Block, usize)> = HashMap::new();
        for bid in &func.block_order {
            let Some(block) = func.blocks.get(bid) else {
                continue;
            };
            for (i, inst) in block.insts.iter().enumerate() {
                if let Some(d) = inst_def_vreg(inst) {
                    *def_count.entry(d).or_insert(0) += 1;
                    def_site.insert(d, (*bid, i));
                }
            }
        }
        Self {
            func,
            intern: HashMap::new(),
            keys: Vec::new(),
            map: HashMap::new(),
            epoch: 0,
            opaque_counter: 0,
            def_count,
            def_site,
            load_addr_ops: HashMap::new(),
        }
    }

    fn intern(&mut self, key: VKey) -> u32 {
        if let VKey::Opaque(_) = key {
            // Never merged.
            let id = self.keys.len() as u32;
            self.keys.push(key);
            return id;
        }
        if let Some(&id) = self.intern.get(&key) {
            return id;
        }
        let id = self.keys.len() as u32;
        self.keys.push(key);
        self.intern.insert(key, id);
        id
    }

    fn fresh_opaque(&mut self) -> u32 {
        self.opaque_counter += 1;
        self.intern(VKey::Opaque(self.opaque_counter))
    }

    fn key(&self, id: u32) -> VKey {
        self.keys[id as usize]
    }

    /// Value id for a USE of `v` at the current scan point.
    fn use_of(&mut self, v: VReg) -> u32 {
        if let Some(&id) = self.map.get(&v) {
            return id;
        }
        let id = self.resolve_external(v);
        // Cache under the vreg so repeated uses are cheap. A later region def
        // overwrites this entry, preserving the linear-scan semantics.
        self.map.insert(v, id);
        id
    }

    /// Resolve a region-external use: walk plain same-class copies while every
    /// vreg on the chain is globally single-def (value fixed for the whole
    /// function); represent the terminal as `Leaf`/`Const`/`LeaSlot`. A
    /// multi-def vreg reached THROUGH a copy has an unknowable snapshot time
    /// -> opaque. The original use itself being multi-def is fine: its value
    /// at region entry is a valid leaf (region defs overwrite the vn map).
    fn resolve_external(&mut self, v: VReg) -> u32 {
        let mut cur = v;
        for step in 0..MAX_COPY_CHAIN {
            let single = self.def_count.get(&cur).copied().unwrap_or(0) == 1;
            if !single {
                if step == 0 {
                    return self.intern(VKey::Leaf(cur));
                }
                return self.fresh_opaque();
            }
            let Some(&(b, i)) = self.def_site.get(&cur) else {
                return self.intern(VKey::Leaf(cur));
            };
            let inst = &self.func.blocks[&b].insts[i];
            match (inst.opcode, inst.operands.as_slice()) {
                (X86Opcode::MovRR, [X86ISelOperand::VReg(_), X86ISelOperand::VReg(src)]) => {
                    cur = *src;
                }
                (X86Opcode::MovRR32, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(src)])
                    if d.class == src.class =>
                {
                    cur = *src;
                }
                (X86Opcode::MovRI, [X86ISelOperand::VReg(_), X86ISelOperand::Imm(k)]) => {
                    return self.intern(VKey::Const(*k));
                }
                (
                    X86Opcode::Lea,
                    [
                        X86ISelOperand::VReg(_),
                        X86ISelOperand::MemAddr { base, disp },
                    ],
                ) => {
                    if let X86ISelOperand::StackSlot(s) = base.as_ref() {
                        return self.intern(VKey::LeaSlot(*s, *disp));
                    }
                    return self.intern(VKey::Leaf(cur));
                }
                _ => {
                    // Single-def non-copy: its value is fixed after its def, so
                    // the vreg itself is a sound identity.
                    return self.intern(VKey::Leaf(cur));
                }
            }
        }
        self.fresh_opaque()
    }

    /// Linearize a value id into `(root, coeff, c)` with wrapped arithmetic
    /// (exact mod 2^64). Only 64-bit ops are looked through.
    fn linearize(&self, id: u32) -> (Option<u32>, i64, i64) {
        match self.key(id) {
            VKey::Const(k) => (None, 0, k),
            VKey::Un {
                op: X86Opcode::AddRI,
                w64: true,
                a,
                imm,
            } => {
                let (r, m, c) = self.linearize(a);
                (r, m, c.wrapping_add(imm))
            }
            VKey::Un {
                op: X86Opcode::SubRI,
                w64: true,
                a,
                imm,
            } => {
                let (r, m, c) = self.linearize(a);
                (r, m, c.wrapping_sub(imm))
            }
            VKey::Un {
                op: X86Opcode::ImulRRI,
                w64: true,
                a,
                imm,
            } => {
                let (r, m, c) = self.linearize(a);
                (r, m.wrapping_mul(imm), c.wrapping_mul(imm))
            }
            _ => (Some(id), 1, 0),
        }
    }

    /// Normalize a memory address to `(base id, index root, coeff, const)` from a
    /// base already resolved to a value id (see `sib_base`).
    fn norm_addr_id(
        &mut self,
        base_id: u32,
        index: Option<VReg>,
        scale: u8,
        disp: i32,
    ) -> NormAddr {
        match index {
            None => NormAddr {
                base: base_id,
                root: None,
                coeff: 0,
                c: disp as i64,
            },
            Some(idx) => {
                let idx_id = self.use_of(idx);
                let (root, m, c) = self.linearize(idx_id);
                let s = scale as i64;
                NormAddr {
                    base: base_id,
                    root,
                    coeff: m.wrapping_mul(s),
                    c: c.wrapping_mul(s).wrapping_add(disp as i64),
                }
            }
        }
    }

    /// Resolve a SIB memory-operand base to `(base value-id, Some(vreg) | None)`.
    /// A `VReg` base numbers as usual and is re-validated at the guard. A literal
    /// `StackSlot(s)` base (emitted by the SIB-base address fold) is modeled
    /// identically to a `VReg` that `Lea`s that slot — `VKey::LeaSlot(s, 0)`
    /// (the fold folds the LEA's displacement into the SIB `disp` field, so the
    /// slot base carries no displacement of its own) — so folded and unfolded
    /// accesses to the same slot value-number to the same base id. A frame slot
    /// is invariant, so it has no vreg to re-validate (`None`). Returns `None`
    /// for any other base form (leaves the access `Unmodeled`, as before).
    fn sib_base(&mut self, base: &X86ISelOperand) -> Option<(u32, Option<VReg>)> {
        match base {
            X86ISelOperand::VReg(bv) => Some((self.use_of(*bv), Some(*bv))),
            X86ISelOperand::StackSlot(s) => Some((self.intern(VKey::LeaSlot(*s, 0)), None)),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Instruction modeling
// ---------------------------------------------------------------------------

/// Single defined vreg of an instruction, mirroring the DCE model: operand 0
/// when the opcode produces a value.
fn inst_def_vreg(inst: &X86ISelInst) -> Option<VReg> {
    if !crate::effects::x86_produces_value(inst.opcode) {
        return None;
    }
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

fn operand_has_preg(op: &X86ISelOperand) -> bool {
    match op {
        X86ISelOperand::PReg(_) => true,
        X86ISelOperand::MemAddr { base, .. } => operand_has_preg(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_has_preg(base) || operand_has_preg(index)
        }
        _ => false,
    }
}

fn inst_has_preg(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(operand_has_preg)
}

fn collect_operand_vregs(op: &X86ISelOperand, out: &mut Vec<VReg>) {
    match op {
        X86ISelOperand::VReg(v) => out.push(*v),
        X86ISelOperand::MemAddr { base, .. } => collect_operand_vregs(base, out),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_vregs(base, out);
            collect_operand_vregs(index, out);
        }
        _ => {}
    }
}

/// Result of evaluating one instruction into the value-numbering state.
enum Eval {
    /// Modeled precisely (def value recorded / store recorded).
    Modeled,
    /// Not modeled: defs opaqued, memory conservatively clobbered. Acceptable
    /// in the PREFIX (facts-only), fatal in the ARM.
    Unmodeled,
}

struct StoreRec {
    addr: NormAddr,
    value_id: u32,
    width: u8,
}

/// Evaluate `inst` (a non-terminator) into the VN state. `stores` collects
/// arm-side stores when `Some`.
fn eval_inst(vn: &mut Vn<'_>, inst: &X86ISelInst, stores: Option<&mut Vec<StoreRec>>) -> Eval {
    use X86Opcode::*;
    match (inst.opcode, inst.operands.as_slice()) {
        (MovRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)]) => {
            let id = vn.intern(VKey::Const(*k));
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (MovRR, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)]) => {
            let id = vn.use_of(*s);
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (MovRR32, [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)]) => {
            let sid = vn.use_of(*s);
            let id = if d.class == s.class {
                sid
            } else if d.class == RegClass::Gpr64 {
                vn.intern(VKey::Zext(sid))
            } else {
                // Truncating direction: model as a deterministic unary node.
                vn.intern(VKey::Un {
                    op: MovRR32,
                    w64: false,
                    a: sid,
                    imm: 0,
                })
            };
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (
            AddRI | SubRI | ImulRRI,
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(k),
            ],
        ) => {
            let a = vn.use_of(*s);
            let id = vn.intern(VKey::Un {
                op: inst.opcode,
                w64: d.class == RegClass::Gpr64,
                a,
                imm: *k,
            });
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (AddRI | SubRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)]) => {
            // Two-operand def-and-use form.
            let a = vn.use_of(*d);
            let id = vn.intern(VKey::Un {
                op: inst.opcode,
                w64: d.class == RegClass::Gpr64,
                a,
                imm: *k,
            });
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (
            AddRR | SubRR | ImulRR | XorRR | AndRR | OrRR,
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(a),
                X86ISelOperand::VReg(b),
            ],
        ) => {
            let mut ia = vn.use_of(*a);
            let mut ib = vn.use_of(*b);
            // Commutative normalization (Sub excluded).
            if matches!(inst.opcode, AddRR | ImulRR | XorRR | AndRR | OrRR) && ia > ib {
                std::mem::swap(&mut ia, &mut ib);
            }
            let id = vn.intern(VKey::Bin {
                op: inst.opcode,
                w64: d.class == RegClass::Gpr64,
                a: ia,
                b: ib,
            });
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (
            Lea,
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::MemAddr { base, disp },
            ],
        ) => {
            if let X86ISelOperand::StackSlot(s) = base.as_ref() {
                let id = vn.intern(VKey::LeaSlot(*s, *disp));
                vn.map.insert(*d, id);
                Eval::Modeled
            } else {
                unmodeled(vn, inst);
                Eval::Unmodeled
            }
        }
        (
            MovRM32Sib | MovRMSib,
            [
                X86ISelOperand::VReg(d),
                sib @ X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ],
        ) => {
            let X86ISelOperand::VReg(iv) = index.as_ref() else {
                unmodeled(vn, inst);
                return Eval::Unmodeled;
            };
            let Some((base_id, base_vreg)) = vn.sib_base(base.as_ref()) else {
                unmodeled(vn, inst);
                return Eval::Unmodeled;
            };
            let width = if inst.opcode == MovRM32Sib { 32 } else { 64 };
            let addr = vn.norm_addr_id(base_id, Some(*iv), *scale, *disp);
            let epoch = vn.epoch;
            let id = vn.intern(VKey::Load {
                base: addr.base,
                root: addr.root,
                coeff: addr.coeff,
                c: addr.c,
                width,
                epoch,
            });
            let index_id = vn.use_of(*iv);
            vn.load_addr_ops.entry(id).or_insert(LoadAddrOp {
                operand: sib.clone(),
                base_vreg,
                index_vreg: Some(*iv),
                base_id,
                index_id: Some(index_id),
            });
            vn.map.insert(*d, id);
            Eval::Modeled
        }
        (
            MovMR32Sib | MovMRSib,
            [
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
                X86ISelOperand::VReg(s),
            ],
        ) => {
            let X86ISelOperand::VReg(iv) = index.as_ref() else {
                unmodeled(vn, inst);
                return Eval::Unmodeled;
            };
            let Some((base_id, _base_vreg)) = vn.sib_base(base.as_ref()) else {
                unmodeled(vn, inst);
                return Eval::Unmodeled;
            };
            let width = if inst.opcode == MovMR32Sib { 32 } else { 64 };
            let addr = vn.norm_addr_id(base_id, Some(*iv), *scale, *disp);
            let value_id = vn.use_of(*s);
            vn.epoch += 1;
            if let Some(st) = stores {
                st.push(StoreRec {
                    addr,
                    value_id,
                    width,
                });
                Eval::Modeled
            } else {
                // A prefix store is not fatal — later loads simply get a new
                // epoch and cannot alias older ones.
                Eval::Modeled
            }
        }
        (CmpRR | CmpRI | CmpRI8 | TestRR | TestRI, _) => Eval::Modeled,
        _ => {
            unmodeled(vn, inst);
            Eval::Unmodeled
        }
    }
}

fn unmodeled(vn: &mut Vn<'_>, inst: &X86ISelInst) {
    if let Some(d) = inst_def_vreg(inst) {
        let id = vn.fresh_opaque();
        vn.map.insert(d, id);
    }
    let eff = crate::effects::x86_inst_effect(inst);
    if eff.writes_memory() || eff.is_barrier() || inst.flags.is_call() {
        vn.epoch += 1;
    }
}

// ---------------------------------------------------------------------------
// Structural matching
// ---------------------------------------------------------------------------

/// A bounds-style check fact: `cmp value, imm; jcc cc -> continue; jmp -> trap`
/// (`jcc_to_trap == false`) or the inverted orientation. Arm checks must match
/// a prefix fact EXACTLY (same tuple).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct CheckFact {
    value_id: u32,
    imm: i64,
    cc: X86CondCode,
    jcc_to_trap: bool,
}

/// Classified terminator SHAPE of a block within the matched region (purely
/// structural — the checked value is value-numbered by the caller AFTER the
/// block body has been evaluated, so the fact reflects the in-block def).
enum Term {
    /// `jmp target`
    Jump(Block),
    /// `cmp v, imm; jcc cc t1; jmp t2` where exactly one target is a trap
    /// block: `cont` is the other one.
    Check {
        value: VReg,
        imm: i64,
        cc: X86CondCode,
        jcc_to_trap: bool,
        cont: Block,
    },
    Other,
}

fn is_trap_block(func: &X86ISelFunction, b: Block) -> bool {
    match func.blocks.get(&b) {
        Some(blk) => {
            blk.successors.is_empty()
                && blk.insts.len() == 1
                && blk.insts[0].opcode == X86Opcode::Ud2
        }
        None => false,
    }
}

/// Classify a block terminator structurally (no value numbering). Returns the
/// number of instructions consumed from the tail (1 for Jump, 3 for Check).
fn classify_terminator(func: &X86ISelFunction, block: &X86ISelBlock) -> (Term, usize) {
    let n = block.insts.len();
    if n >= 1
        && block.insts[n - 1].opcode == X86Opcode::Jmp
        && let [X86ISelOperand::Block(t)] = block.insts[n - 1].operands.as_slice()
    {
        // Plain jump — but if the two preceding insts are a Jcc pair this is
        // a two-way exit, classified below.
        if n < 2 || block.insts[n - 2].opcode != X86Opcode::Jcc {
            return (Term::Jump(*t), 1);
        }
        let jcc = &block.insts[n - 2];
        let [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(jt)] = jcc.operands.as_slice()
        else {
            return (Term::Other, 0);
        };
        if n >= 3
            && block.insts[n - 3].opcode == X86Opcode::CmpRI
            && let [X86ISelOperand::VReg(v), X86ISelOperand::Imm(k)] =
                block.insts[n - 3].operands.as_slice()
        {
            let jcc_trap = is_trap_block(func, *jt);
            let jmp_trap = is_trap_block(func, *t);
            if jcc_trap != jmp_trap {
                let cont = if jcc_trap { *t } else { *jt };
                return (
                    Term::Check {
                        value: *v,
                        imm: *k,
                        cc: *cc,
                        jcc_to_trap: jcc_trap,
                        cont,
                    },
                    3,
                );
            }
        }
        (Term::Other, 0)
    } else {
        (Term::Other, 0)
    }
}

/// A fully-validated conversion plan for one conditional-swap diamond.
struct SwapPlan {
    guard: Block,
    /// Blocks of the (deleted) swap arm, in chain order.
    arm_blocks: Vec<Block>,
    /// The guard's fall-through target (kept as the sole successor).
    fall_target: Block,
    /// Guard compare operands (the two loaded values).
    va: VReg,
    vb: VReg,
    /// Taken condition code (used directly for both CMOVs; no inversion).
    cc: X86CondCode,
    /// Cloned guard-load address operands (validated still-current at the
    /// guard terminator).
    addr_a_operand: X86ISelOperand,
    addr_b_operand: X86ISelOperand,
    /// 32 or 64.
    width: u8,
}

fn find_one(func: &X86ISelFunction) -> Option<SwapPlan> {
    let preds = predecessor_map(func);
    for &guard in &func.block_order {
        if let Some(plan) = try_guard(func, &preds, guard) {
            return Some(plan);
        }
    }
    None
}

fn try_guard(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    guard: Block,
) -> Option<SwapPlan> {
    let gblock = func.blocks.get(&guard)?;
    let n = gblock.insts.len();
    if n < 3 {
        return None;
    }
    // Terminator shape: CmpRR va, vb ; Jcc cc ARM ; Jmp FALL
    let cmp = &gblock.insts[n - 3];
    let jcc = &gblock.insts[n - 2];
    let jmp = &gblock.insts[n - 1];
    if cmp.opcode != X86Opcode::CmpRR
        || jcc.opcode != X86Opcode::Jcc
        || jmp.opcode != X86Opcode::Jmp
    {
        return None;
    }
    let [X86ISelOperand::VReg(va), X86ISelOperand::VReg(vb)] = cmp.operands.as_slice() else {
        return None;
    };
    let [
        X86ISelOperand::CondCode(cc),
        X86ISelOperand::Block(arm_entry),
    ] = jcc.operands.as_slice()
    else {
        return None;
    };
    let [X86ISelOperand::Block(fall_target)] = jmp.operands.as_slice() else {
        return None;
    };
    let (va, vb, cc, arm_entry, fall_target) = (*va, *vb, *cc, *arm_entry, *fall_target);
    if arm_entry == fall_target || arm_entry == guard {
        return None;
    }
    if va.class != vb.class || !matches!(va.class, RegClass::Gpr32 | RegClass::Gpr64) {
        return None;
    }
    let width: u8 = if va.class == RegClass::Gpr32 { 32 } else { 64 };

    // Join: the fall-through target directly, or through an empty forwarder.
    let fall_block = func.blocks.get(&fall_target)?;
    let join = if fall_block.insts.len() == 1
        && fall_block.insts[0].opcode == X86Opcode::Jmp
        && preds.get(&fall_target).map(Vec::as_slice) == Some(&[guard])
    {
        let [X86ISelOperand::Block(j)] = fall_block.insts[0].operands.as_slice() else {
            return None;
        };
        *j
    } else {
        fall_target
    };
    if join == guard || join == arm_entry {
        return None;
    }

    // --- Prefix chain: walk back through unique predecessors. -------------
    let mut prefix: Vec<Block> = vec![guard];
    let mut cur = guard;
    while prefix.len() < MAX_CHAIN_BLOCKS {
        match preds.get(&cur).map(Vec::as_slice) {
            Some(&[p]) if p != cur && !prefix.contains(&p) => {
                prefix.push(p);
                cur = p;
            }
            _ => break,
        }
    }
    prefix.reverse();

    // --- Evaluate the prefix, collecting check facts. ---------------------
    let mut vn = Vn::new(func);
    let mut facts: HashSet<CheckFact> = HashSet::new();
    for (pi, &b) in prefix.iter().enumerate() {
        let block = func.blocks.get(&b)?;
        let is_guard = pi + 1 == prefix.len();
        // Determine how many tail insts belong to the terminator.
        let (term, term_len) = if is_guard {
            (Term::Other, 3) // guard terminator handled explicitly below
        } else {
            classify_terminator(func, block)
        };
        let body_end = block.insts.len().saturating_sub(term_len);
        for inst in &block.insts[..body_end] {
            // Prefix instructions are never modified; unmodeled ones only
            // degrade knowledge (opaque defs, epoch bumps).
            let _ = eval_inst(&mut vn, inst, None);
        }
        if !is_guard {
            match term {
                Term::Check {
                    value,
                    imm,
                    cc,
                    jcc_to_trap,
                    cont,
                } => {
                    // Fact only usable if the continue edge stays on the chain.
                    let next = prefix[pi + 1];
                    if cont == next {
                        let value_id = vn.use_of(value);
                        facts.insert(CheckFact {
                            value_id,
                            imm,
                            cc,
                            jcc_to_trap,
                        });
                    }
                }
                Term::Jump(_) | Term::Other => {}
            }
        }
    }

    // Guard loads: both compare operands must value-number to same-epoch
    // loads at provably-distinct constant-offset addresses.
    let va_id = vn.use_of(va);
    let vb_id = vn.use_of(vb);
    if va_id == vb_id {
        return None;
    }
    let (addr_a, ea, wa) = match vn.key(va_id) {
        VKey::Load {
            base,
            root,
            coeff,
            c,
            width,
            epoch,
        } => (
            NormAddr {
                base,
                root,
                coeff,
                c,
            },
            epoch,
            width,
        ),
        _ => return None,
    };
    let (addr_b, eb, wb) = match vn.key(vb_id) {
        VKey::Load {
            base,
            root,
            coeff,
            c,
            width,
            epoch,
        } => (
            NormAddr {
                base,
                root,
                coeff,
                c,
            },
            epoch,
            width,
        ),
        _ => return None,
    };
    if wa != width || wb != width {
        return None;
    }
    // Loads must still be current (no store/call between load and guard).
    if ea != vn.epoch || eb != vn.epoch {
        return None;
    }
    if !addr_a.provably_distinct_from(&addr_b) {
        return None;
    }

    // Re-materializable address operands, still current at the guard end.
    let a_op = validate_addr_operand(&mut vn, va_id)?;
    let b_op = validate_addr_operand(&mut vn, vb_id)?;

    // --- Arm chain scan. ---------------------------------------------------
    let mut arm_blocks: Vec<Block> = Vec::new();
    let mut arm_defs: HashSet<VReg> = HashSet::new();
    let mut stores: Vec<StoreRec> = Vec::new();
    let mut cur = arm_entry;
    let mut prev = guard;
    loop {
        if arm_blocks.len() >= MAX_CHAIN_BLOCKS {
            return None;
        }
        if cur == join || cur == guard || cur == fall_target || arm_blocks.contains(&cur) {
            return None;
        }
        if preds.get(&cur).map(Vec::as_slice) != Some(&[prev]) {
            return None;
        }
        let block = func.blocks.get(&cur)?;
        arm_blocks.push(cur);
        let (term, term_len) = classify_terminator(func, block);
        if term_len == 0 {
            return None; // unrecognized terminator
        }
        let body_end = block.insts.len() - term_len;
        for inst in &block.insts[..body_end] {
            if inst_has_preg(inst) {
                return None;
            }
            if stores.len() == 2 {
                // Nothing may follow the completed store pair except the
                // terminator.
                return None;
            }
            match eval_inst(&mut vn, inst, Some(&mut stores)) {
                Eval::Modeled => {}
                Eval::Unmodeled => return None,
            }
            if stores.len() > 2 {
                return None;
            }
            if let Some(d) = inst_def_vreg(inst) {
                arm_defs.insert(d);
            }
        }
        match term {
            Term::Jump(t) => {
                if t == join {
                    break;
                }
                prev = cur;
                cur = t;
            }
            Term::Check {
                value,
                imm,
                cc,
                jcc_to_trap,
                cont,
            } => {
                // The arm check must be identical to an established prefix
                // fact — otherwise it is (or may be) live, and deleting it
                // could suppress a real trap.
                let fact = CheckFact {
                    value_id: vn.use_of(value),
                    imm,
                    cc,
                    jcc_to_trap,
                };
                if !facts.contains(&fact) {
                    return None;
                }
                if cont == join {
                    break;
                }
                prev = cur;
                cur = cont;
            }
            Term::Other => return None,
        }
    }

    // --- The crossed store pair. -------------------------------------------
    if stores.len() != 2 {
        return None;
    }
    let (sa, sb) = if stores[0].addr == addr_a && stores[1].addr == addr_b {
        (&stores[0], &stores[1])
    } else if stores[0].addr == addr_b && stores[1].addr == addr_a {
        (&stores[1], &stores[0])
    } else {
        return None;
    };
    // sa writes the a[j-1] slot; it must store the guard's vb value. sb
    // writes the a[j] slot; it must store va. (The exact swap.)
    if sa.value_id != vb_id || sb.value_id != va_id {
        return None;
    }
    if sa.width != width || sb.width != width {
        return None;
    }

    // --- No arm-defined vreg used outside the arm. -------------------------
    let arm_set: HashSet<Block> = arm_blocks.iter().copied().collect();
    for bid in &func.block_order {
        if arm_set.contains(bid) {
            continue;
        }
        let Some(block) = func.blocks.get(bid) else {
            continue;
        };
        for inst in &block.insts {
            let mut used: Vec<VReg> = Vec::new();
            for (oi, op) in inst.operands.iter().enumerate() {
                // Skip the pure-def operand-0 (writes don't count as uses;
                // conservative: only skip when the opcode defines op0 and the
                // inst is not a def-and-use form we model — counting a def as
                // a use can only make us MORE conservative).
                let _ = oi;
                collect_operand_vregs(op, &mut used);
            }
            if used.iter().any(|v| arm_defs.contains(v)) {
                // A def-vreg re-used outside: reject unless it is only the
                // def operand of this instruction... conservative: reject.
                return None;
            }
        }
    }

    Some(SwapPlan {
        guard,
        arm_blocks,
        fall_target,
        va,
        vb,
        cc,
        addr_a_operand: a_op,
        addr_b_operand: b_op,
        width,
    })
}

/// The guard-load address operand for a load value id, validated to still
/// evaluate to the load-time address at the CURRENT (guard-terminator) scan
/// point: every vreg in the operand must value-number to the same id it had
/// when the load executed.
fn validate_addr_operand(vn: &mut Vn<'_>, load_id: u32) -> Option<X86ISelOperand> {
    let rec = vn.load_addr_ops.get(&load_id)?.clone();
    // A VReg base must still value-number to the same id at the guard. A literal
    // StackSlot base is frame-invariant and has no vreg — nothing can go stale.
    if let Some(bv) = rec.base_vreg
        && vn.use_of(bv) != rec.base_id
    {
        return None;
    }
    if let (Some(iv), Some(iid)) = (rec.index_vreg, rec.index_id)
        && vn.use_of(iv) != iid
    {
        return None;
    }
    Some(rec.operand)
}

fn apply(func: &mut X86ISelFunction, plan: &SwapPlan) {
    let (mov_op, cmov_op, store_op) = if plan.width == 32 {
        (
            X86Opcode::MovRR32,
            X86Opcode::Cmovcc32,
            X86Opcode::MovMR32Sib,
        )
    } else {
        (X86Opcode::MovRR, X86Opcode::Cmovcc, X86Opcode::MovMRSib)
    };
    let class = if plan.width == 32 {
        RegClass::Gpr32
    } else {
        RegClass::Gpr64
    };
    let lo = VReg::new(func.next_vreg, class);
    let hi = VReg::new(func.next_vreg + 1, class);
    func.next_vreg += 2;
    func.vreg_nominal_widths.insert(lo, plan.width as u32);
    func.vreg_nominal_widths.insert(hi, plan.width as u32);

    let guard = func
        .blocks
        .get_mut(&plan.guard)
        .expect("planned guard exists");
    let n = guard.insts.len();
    // Drop `jcc; jmp`, keep the CmpRR flag-setter for the CMOVs.
    guard.insts.truncate(n - 2);
    // lo = cc ? vb : va
    guard.insts.push(X86ISelInst::new(
        mov_op,
        vec![X86ISelOperand::VReg(lo), X86ISelOperand::VReg(plan.va)],
    ));
    guard.insts.push(X86ISelInst::new(
        cmov_op,
        vec![
            X86ISelOperand::VReg(lo),
            X86ISelOperand::VReg(plan.vb),
            X86ISelOperand::CondCode(plan.cc),
        ],
    ));
    // hi = cc ? va : vb
    guard.insts.push(X86ISelInst::new(
        mov_op,
        vec![X86ISelOperand::VReg(hi), X86ISelOperand::VReg(plan.vb)],
    ));
    guard.insts.push(X86ISelInst::new(
        cmov_op,
        vec![
            X86ISelOperand::VReg(hi),
            X86ISelOperand::VReg(plan.va),
            X86ISelOperand::CondCode(plan.cc),
        ],
    ));
    // Unconditional store pair (identical writes on the not-taken path).
    guard.insts.push(X86ISelInst::new(
        store_op,
        vec![plan.addr_a_operand.clone(), X86ISelOperand::VReg(lo)],
    ));
    guard.insts.push(X86ISelInst::new(
        store_op,
        vec![plan.addr_b_operand.clone(), X86ISelOperand::VReg(hi)],
    ));
    guard.insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(plan.fall_target)],
    ));
    guard.successors = vec![plan.fall_target];

    // Delete the now-unreachable arm chain (single-pred throughout; the trap
    // blocks it jumped to are shared and stay).
    for b in &plan.arm_blocks {
        func.blocks.remove(b);
    }
    func.block_order.retain(|b| !plan.arm_blocks.contains(b));

    // Structural self-check.
    let guard = func.blocks.get(&plan.guard).expect("guard present");
    let gn = guard.insts.len();
    assert!(
        gn >= 8
            && guard.insts[gn - 8].opcode == X86Opcode::CmpRR
            && guard.insts[gn - 1].opcode == X86Opcode::Jmp,
        "x86-cmov-swap: guard terminator not rewritten as expected"
    );
    assert_eq!(guard.successors, vec![plan.fall_target]);
    for b in &plan.arm_blocks {
        assert!(!func.blocks.contains_key(b), "arm block not deleted");
    }
}

/// Renumber every block to a gap-free `0..n` range following `block_order`
/// (mirrors `x86_if_convert::renumber_blocks_contiguous`; required by the
/// regalloc replay).
fn renumber_blocks_contiguous(func: &mut X86ISelFunction) {
    let len = func.block_order.len();
    let remap: HashMap<Block, Block> = func
        .block_order
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, Block(i as u32)))
        .collect();

    let order = std::mem::take(&mut func.block_order);
    let mut new_blocks: HashMap<Block, X86ISelBlock> = HashMap::with_capacity(len);
    for old_id in &order {
        let Some(mut blk) = func.blocks.remove(old_id) else {
            continue;
        };
        for s in &mut blk.successors {
            if let Some(&n) = remap.get(s) {
                *s = n;
            }
        }
        for inst in &mut blk.insts {
            for op in &mut inst.operands {
                if let X86ISelOperand::Block(b) = op
                    && let Some(&n) = remap.get(b)
                {
                    *b = n;
                }
            }
        }
        new_blocks.insert(remap[old_id], blk);
    }
    for table in &mut func.jump_tables {
        for target in &mut table.targets {
            if let Some(&n) = remap.get(target) {
                *target = n;
            }
        }
    }
    for pad in &mut func.eh_info.landing_pads {
        if let Some(&new_block) = remap.get(&pad.block) {
            pad.block = new_block;
        }
    }
    for site in &mut func.eh_info.call_sites {
        if let Some(&new_block) = remap.get(&site.call_block) {
            site.call_block = new_block;
        }
        if let Some(&new_block) = remap.get(&site.landing_pad_block) {
            site.landing_pad_block = new_block;
        }
    }
    func.blocks = new_blocks;
    func.block_order = (0..len as u32).map(Block).collect();
}

// ---------------------------------------------------------------------------
// Tests: the b06 bubble-sort inner-loop shape (mirrors the real
// post-`X86LoopRotate` pm-dump of reports/perf/benches/b06_bubblesort.rs).
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;

    fn v64(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }
    fn v32(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr32)
    }
    fn ovr(v: VReg) -> X86ISelOperand {
        X86ISelOperand::VReg(v)
    }
    fn imm(k: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(k)
    }
    fn blk(b: u32) -> X86ISelOperand {
        X86ISelOperand::Block(Block(b))
    }
    fn cc(c: X86CondCode) -> X86ISelOperand {
        X86ISelOperand::CondCode(c)
    }
    fn sib(base: VReg, index: VReg, scale: u8, disp: i32) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(ovr(base)),
            index: Box::new(ovr(index)),
            scale,
            disp,
        }
    }
    fn inst(op: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, operands)
    }
    fn add_block(f: &mut X86ISelFunction, b: Block, insts: Vec<X86ISelInst>, succs: Vec<Block>) {
        f.ensure_block(b);
        let blk = f.blocks.get_mut(&b).unwrap();
        blk.insts = insts;
        blk.successors = succs;
    }
    fn empty_sig() -> Signature {
        Signature {
            params: vec![],
            returns: vec![],
        }
    }

    /// Build the b06-like inner-loop function:
    ///
    /// Block(0) entry: base = lea slot; jmp 1
    /// Block(1) header (j-1 bounds check): copies + sub + check
    /// Block(2) load a[j-1] + check j
    /// Block(3) GUARD: load a[j]; cmp; jcc A -> 5 (arm); jmp 4 (forwarder)
    /// Block(4) forwarder -> 9 (join)
    /// Block(5..8) ARM: re-derive, re-check, re-load, crossed stores
    /// Block(9) join latch; Block(10) trap (Ud2); Block(11) exit
    ///
    /// VReg map (mirrors the dump's roles):
    ///   v0 base lea; v1 j (multi-def: also written in join latch)
    ///   prefix: v2=copy j, v3=j-1, v4=copy j-1 (index), v5=load a[j-1]
    ///           v6=copy j (index), v7=load a[j]
    ///   arm: v10=copy j, v11=j-1, v12=copy, v13=reload a[j-1],
    ///        v14=copy j, v15=reload a[j], v16=copy j, v17=j-1 (store idx)
    ///        v18=copy j, v19=j*4 (imul store idx scale-1)
    fn build_b06_like() -> X86ISelFunction {
        let mut f = X86ISelFunction::new("t".into(), empty_sig());
        let base = v64(0);
        let j = v64(1);

        // Block 0: entry
        add_block(
            &mut f,
            Block(0),
            vec![
                inst(
                    X86Opcode::Lea,
                    vec![
                        ovr(base),
                        X86ISelOperand::MemAddr {
                            base: Box::new(X86ISelOperand::StackSlot(0)),
                            disp: 0,
                        },
                    ],
                ),
                inst(X86Opcode::MovRI, vec![ovr(j), imm(1)]),
                inst(X86Opcode::Jmp, vec![blk(1)]),
            ],
            vec![Block(1)],
        );
        // Block 1: prefix check j-1 < 256
        add_block(
            &mut f,
            Block(1),
            vec![
                inst(X86Opcode::MovRR, vec![ovr(v64(2)), ovr(j)]),
                inst(X86Opcode::SubRI, vec![ovr(v64(3)), ovr(v64(2)), imm(1)]),
                inst(X86Opcode::CmpRI, vec![ovr(v64(3)), imm(256)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::B), blk(2)]),
                inst(X86Opcode::Jmp, vec![blk(10)]),
            ],
            vec![Block(2), Block(10)],
        );
        // Block 2: load a[j-1]; check j < 256
        add_block(
            &mut f,
            Block(2),
            vec![
                inst(X86Opcode::MovRR, vec![ovr(v64(4)), ovr(v64(3))]),
                inst(
                    X86Opcode::MovRM32Sib,
                    vec![ovr(v32(5)), sib(base, v64(4), 4, 0)],
                ),
                inst(X86Opcode::CmpRI, vec![ovr(j), imm(256)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::B), blk(3)]),
                inst(X86Opcode::Jmp, vec![blk(10)]),
            ],
            vec![Block(3), Block(10)],
        );
        // Block 3: GUARD
        add_block(
            &mut f,
            Block(3),
            vec![
                inst(X86Opcode::MovRR, vec![ovr(v64(6)), ovr(j)]),
                inst(
                    X86Opcode::MovRM32Sib,
                    vec![ovr(v32(7)), sib(base, v64(6), 4, 0)],
                ),
                inst(X86Opcode::CmpRR, vec![ovr(v32(5)), ovr(v32(7))]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::A), blk(5)]),
                inst(X86Opcode::Jmp, vec![blk(4)]),
            ],
            vec![Block(5), Block(4)],
        );
        // Block 4: forwarder to join
        add_block(
            &mut f,
            Block(4),
            vec![inst(X86Opcode::Jmp, vec![blk(9)])],
            vec![Block(9)],
        );
        // Block 5 (ARM): re-derive j-1; re-check
        add_block(
            &mut f,
            Block(5),
            vec![
                inst(X86Opcode::MovRR, vec![ovr(v64(10)), ovr(j)]),
                inst(X86Opcode::SubRI, vec![ovr(v64(11)), ovr(v64(10)), imm(1)]),
                inst(X86Opcode::CmpRI, vec![ovr(v64(11)), imm(256)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::B), blk(6)]),
                inst(X86Opcode::Jmp, vec![blk(10)]),
            ],
            vec![Block(6), Block(10)],
        );
        // Block 6 (ARM): reload a[j-1]; re-check j
        add_block(
            &mut f,
            Block(6),
            vec![
                inst(X86Opcode::MovRR, vec![ovr(v64(12)), ovr(v64(11))]),
                inst(
                    X86Opcode::MovRM32Sib,
                    vec![ovr(v32(13)), sib(base, v64(12), 4, 0)],
                ),
                inst(X86Opcode::CmpRI, vec![ovr(j), imm(256)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::B), blk(7)]),
                inst(X86Opcode::Jmp, vec![blk(10)]),
            ],
            vec![Block(7), Block(10)],
        );
        // Block 7 (ARM): reload a[j]; derive store index j-1; check; store
        add_block(
            &mut f,
            Block(7),
            vec![
                inst(X86Opcode::MovRR, vec![ovr(v64(14)), ovr(j)]),
                inst(
                    X86Opcode::MovRM32Sib,
                    vec![ovr(v32(15)), sib(base, v64(14), 4, 0)],
                ),
                inst(X86Opcode::MovRR, vec![ovr(v64(16)), ovr(j)]),
                inst(X86Opcode::SubRI, vec![ovr(v64(17)), ovr(v64(16)), imm(1)]),
                inst(X86Opcode::CmpRI, vec![ovr(v64(17)), imm(256)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::B), blk(8)]),
                inst(X86Opcode::Jmp, vec![blk(10)]),
            ],
            vec![Block(8), Block(10)],
        );
        // Block 8 (ARM): store a[j-1] <- reload-of-a[j]; imul store idx;
        // store a[j] <- reload-of-a[j-1] (scale-1 imul'd index, as in the
        // real dump); jmp join
        add_block(
            &mut f,
            Block(8),
            vec![
                inst(
                    X86Opcode::MovMR32Sib,
                    vec![sib(base, v64(17), 4, 0), ovr(v32(15))],
                ),
                inst(X86Opcode::MovRR, vec![ovr(v64(18)), ovr(j)]),
                inst(X86Opcode::ImulRRI, vec![ovr(v64(19)), ovr(v64(18)), imm(4)]),
                inst(
                    X86Opcode::MovMR32Sib,
                    vec![sib(base, v64(19), 1, 0), ovr(v32(13))],
                ),
                inst(X86Opcode::Jmp, vec![blk(9)]),
            ],
            vec![Block(9)],
        );
        // Block 9: join latch (redefines j)
        add_block(
            &mut f,
            Block(9),
            vec![
                inst(X86Opcode::AddRI, vec![ovr(v64(20)), ovr(j), imm(1)]),
                inst(X86Opcode::MovRR, vec![ovr(j), ovr(v64(20))]),
                inst(X86Opcode::CmpRI, vec![ovr(j), imm(256)]),
                inst(X86Opcode::Jcc, vec![cc(X86CondCode::B), blk(1)]),
                inst(X86Opcode::Jmp, vec![blk(11)]),
            ],
            vec![Block(1), Block(11)],
        );
        // Block 10: trap
        add_block(
            &mut f,
            Block(10),
            vec![inst(X86Opcode::Ud2, vec![])],
            vec![],
        );
        // Block 11: exit
        add_block(
            &mut f,
            Block(11),
            vec![inst(X86Opcode::Ret, vec![])],
            vec![],
        );
        f.next_vreg = 64;
        f
    }

    fn run_pass(f: &mut X86ISelFunction) -> usize {
        let mut p = X86CmovSwap::new();
        p.run(f);
        p.last_run_conversions
    }

    #[test]
    fn converts_b06_shape() {
        let mut f = build_b06_like();
        let n_before = f.block_order.len();
        assert_eq!(run_pass(&mut f), 1);
        // 4 arm blocks deleted.
        assert_eq!(f.block_order.len(), n_before - 4);
        // Guard (renumbered, but findable by its CmpRR+Cmovcc content).
        let mut found = false;
        for b in f.blocks.values() {
            let ops: Vec<X86Opcode> = b.insts.iter().map(|i| i.opcode).collect();
            if ops.contains(&X86Opcode::Cmovcc32) {
                found = true;
                let n = b.insts.len();
                assert_eq!(b.insts[n - 8].opcode, X86Opcode::CmpRR);
                assert_eq!(b.insts[n - 7].opcode, X86Opcode::MovRR32);
                assert_eq!(b.insts[n - 6].opcode, X86Opcode::Cmovcc32);
                assert_eq!(b.insts[n - 5].opcode, X86Opcode::MovRR32);
                assert_eq!(b.insts[n - 4].opcode, X86Opcode::Cmovcc32);
                assert_eq!(b.insts[n - 3].opcode, X86Opcode::MovMR32Sib);
                assert_eq!(b.insts[n - 2].opcode, X86Opcode::MovMR32Sib);
                assert_eq!(b.insts[n - 1].opcode, X86Opcode::Jmp);
                // Both CMOVs carry the ORIGINAL (non-inverted) cc.
                for i in [n - 6, n - 4] {
                    let X86ISelOperand::CondCode(c) = b.insts[i].operands[2] else {
                        panic!("cmov cc operand");
                    };
                    assert_eq!(c, X86CondCode::A);
                }
                assert_eq!(b.successors.len(), 1);
            }
        }
        assert!(found, "rewritten guard not found");
        // Contiguous renumbering held.
        for (i, b) in f.block_order.iter().enumerate() {
            assert_eq!(b.0 as usize, i);
            assert!(f.blocks.contains_key(b));
        }
        // Idempotent.
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn converts_b06_shape_folded_stackslot_base() {
        // The SIB-base address fold (TCG_X86_SIB_BASE_FOLD) rewrites each array
        // access's base from the `Lea`-result VReg to the literal StackSlot the
        // LEA addressed. cmov-swap must STILL recognize the swap diamond and fire
        // on the folded shape (the StackSlot-SIB value-numbering: StackSlot(s) is
        // modeled identically to a VReg that Leas slot s). Before the fix this
        // regressed b06 (+55%) because the folded loads were left Unmodeled.
        let mut f = build_b06_like();
        // Simulate the fold: SibMemAddr{ base: VReg(0=the &arr Lea), .. } ->
        // base: StackSlot(0). The fold folds the LEA disp (0 here) into the SIB
        // disp, so index/scale/disp are unchanged.
        for b in f.blocks.values_mut() {
            for i in &mut b.insts {
                for op in &mut i.operands {
                    if let X86ISelOperand::SibMemAddr { base, .. } = op
                        && matches!(base.as_ref(), X86ISelOperand::VReg(v) if v.id == 0)
                    {
                        **base = X86ISelOperand::StackSlot(0);
                    }
                }
            }
        }
        // Still fires exactly once, and is idempotent.
        assert_eq!(
            run_pass(&mut f),
            1,
            "cmov-swap must fire on the folded shape"
        );
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn rejects_unchecked_arm_bounds_check() {
        // Change one arm check bound (257 vs 256): no dominating identical
        // check -> the check may be live -> must NOT fire.
        let mut f = build_b06_like();
        let b5 = f.blocks.get_mut(&Block(5)).unwrap();
        b5.insts[2] = inst(X86Opcode::CmpRI, vec![ovr(v64(11)), imm(257)]);
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn rejects_non_crossed_stores() {
        // Make the second store write the same value as the first (not a
        // swap): must NOT fire.
        let mut f = build_b06_like();
        let b8 = f.blocks.get_mut(&Block(8)).unwrap();
        b8.insts[3] = inst(
            X86Opcode::MovMR32Sib,
            vec![sib(v64(0), v64(19), 1, 0), ovr(v32(15))],
        );
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn rejects_same_address_stores() {
        // Point the second store at the SAME slot as the first (j-1):
        // addresses no longer provably distinct/crossed -> must NOT fire.
        let mut f = build_b06_like();
        let b8 = f.blocks.get_mut(&Block(8)).unwrap();
        b8.insts[3] = inst(
            X86Opcode::MovMR32Sib,
            vec![sib(v64(0), v64(17), 4, 0), ovr(v32(13))],
        );
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn rejects_call_in_arm() {
        let mut f = build_b06_like();
        let b6 = f.blocks.get_mut(&Block(6)).unwrap();
        b6.insts.insert(
            0,
            inst(X86Opcode::Call, vec![X86ISelOperand::Symbol("x".into())]),
        );
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn rejects_arm_def_used_outside() {
        // Use an arm-defined vreg in the join: deleting the arm would leave a
        // dangling use -> must NOT fire.
        let mut f = build_b06_like();
        let b9 = f.blocks.get_mut(&Block(9)).unwrap();
        b9.insts
            .insert(0, inst(X86Opcode::MovRR, vec![ovr(v64(40)), ovr(v64(17))]));
        assert_eq!(run_pass(&mut f), 0);
    }

    #[test]
    fn rejects_store_between_load_and_guard() {
        // A store between the a[j-1] load and the guard bumps the epoch: the
        // guard operand no longer proves the loaded value is current.
        let mut f = build_b06_like();
        let b2 = f.blocks.get_mut(&Block(2)).unwrap();
        b2.insts.insert(
            2,
            inst(
                X86Opcode::MovMR32Sib,
                vec![sib(v64(0), v64(4), 4, 0), ovr(v32(5))],
            ),
        );
        assert_eq!(run_pass(&mut f), 0);
    }
}
