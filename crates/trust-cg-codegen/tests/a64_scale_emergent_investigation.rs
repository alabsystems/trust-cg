// trust-cg-codegen/tests/a64_scale_emergent_investigation.rs
//
// A64-4 / JIT-2 / TV-6 INVESTIGATION HARNESS (host-independent).
//
// The two historical aarch64-JIT miscompiles (shape_matches_ty 2-case
// wrong-boolean and fold_binop-Shl arm never reached) are pinned as
// cfg(aarch64) known-sets that cannot run on an x86 host. But the
// ENTIRE aarch64 lowering pipeline (adapter -> isel.rs -> O1 passes -> LinearScan
// jit_latency regalloc -> frame lowering -> branch resolution) is host-independent
// Rust: it constructs the exact machine IR the JIT encodes, on any host.
//
// This harness (1) cross-constructs that machine IR on x86 from the pinned trust-ir
// fixtures (extracted from e2e_x86_64_scale_emergent.rs into tests/fixtures/*.tir),
// and (2) EXECUTES it with a struct-level AArch64 MachInst interpreter, using the
// same failing inputs as the aarch64 pins. The interpreter models registers
// (X/W aliasing, NZCV), a flat memory, the AAPCS64 call boundary, and the
// jump-table dispatch pattern — enough to run Constant__shape_matches_ty and
// fold_binop end to end and observe exactly where the dataflow goes wrong.
//
// If the interpreter reproduces the pinned wrong answers, the bug is in the
// pre-encoding pipeline (isel/regalloc) and the divergence trace localizes it.
// If it does NOT reproduce them, the bug is in the encoder/JIT-runtime layer.
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.

#![allow(clippy::all)]

use trust_cg_codegen::pipeline::{DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::MachFunction;
use trust_cg_ir::operand::MachOperand;

// ---------------------------------------------------------------------------
// Pipeline cross-construction (mirrors CompilerConfig::jit_fast(Target::Aarch64))
// ---------------------------------------------------------------------------

fn load_fixture(name: &str) -> trust_ir::Module {
    let path = format!("{}/tests/fixtures/{name}", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("parse {name}: {e:?}"))
}

/// Prepare every function of the module through the EXACT jit_fast aarch64
/// pipeline: O1, enable_jit_fast_regalloc (LinearScan jit_latency profile).
fn prepare_aarch64_jit_fast(module: &trust_ir::Module) -> Vec<MachFunction> {
    let lir_functions = trust_cg_lower::translate_module_for_arch(
        module,
        trust_cg_lower::GuardCarrierArch::AArch64,
    )
    .expect("adapter must translate the pinned IR");

    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O1,
        emit_debug: false,
        verify_dispatch: DispatchVerifyMode::FallbackOnFailure,
        verify: false,
        cegis_superopt_budget_sec: None,
        target_triple: String::new(),
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: true,
        skip_cse_gvn: false,
        disabled_passes_override: None,
        contains4_scanner_batch_rewrite_override: None,
    });

    lir_functions
        .iter()
        .map(|(lir_func, proof_ctx)| {
            pipeline
                .prepare_function_with_proofs(lir_func, Some(proof_ctx))
                .unwrap_or_else(|e| panic!("prepare {}: {e:?}", lir_func.name))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Listing dump
// ---------------------------------------------------------------------------

fn fmt_operand(op: &MachOperand) -> String {
    match op {
        MachOperand::VReg(v) => format!("v{}:{:?}", v.id, v.class),
        MachOperand::PReg(p) => format!("{}", preg_name(p.encoding())),
        MachOperand::Imm(i) => format!("#{i}"),
        MachOperand::FImm(f) => format!("#f{f}"),
        MachOperand::Block(b) => format!("b{}", b.0),
        MachOperand::StackSlot(s) => format!("ss{}", s.0),
        MachOperand::FrameIndex(f) => format!("fi{}", f.0),
        MachOperand::MemOp { base, offset } => {
            format!("[{}, #{offset}]", preg_name(base.encoding()))
        }
        MachOperand::Special(s) => format!("{s:?}"),
        MachOperand::Symbol(s) => format!("@{s}"),
        MachOperand::JumpTableIndex(i) => format!("jt{i}"),
        MachOperand::IncomingArg(o) => format!("inarg+{o}"),
    }
}

fn preg_name(enc: u16) -> String {
    match enc {
        0..=30 => format!("x{enc}"),
        31 => "sp".to_string(),
        32..=62 => format!("w{}", enc - 32),
        63 => "wsp".to_string(),
        64..=95 => format!("v{}", enc - 64),
        96..=127 => format!("d{}", enc - 96),
        128..=159 => format!("s{}", enc - 128),
        _ => format!("preg{enc}"),
    }
}

fn dump_function(func: &MachFunction) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "=== {} === ({} blocks, {} insts arena, {} stack slots, {} jump tables)\n",
        func.name,
        func.block_order.len(),
        func.insts.len(),
        func.stack_slots.len(),
        func.jump_tables.len()
    ));
    for (jti, jt) in func.jump_tables.iter().enumerate() {
        out.push_str(&format!(
            "  jt{jti}: min={} targets={:?}\n",
            jt.min_val,
            jt.targets.iter().map(|b| b.0).collect::<Vec<_>>()
        ));
    }
    let mut flat_idx = 0usize;
    for &bid in &func.block_order {
        let block = &func.blocks[bid.0 as usize];
        out.push_str(&format!(
            "b{}:  ; preds={:?} succs={:?}\n",
            bid.0,
            block.preds.iter().map(|b| b.0).collect::<Vec<_>>(),
            block.succs.iter().map(|b| b.0).collect::<Vec<_>>()
        ));
        for &iid in &block.insts {
            let inst = &func.insts[iid.0 as usize];
            let ops: Vec<String> = inst.operands.iter().map(fmt_operand).collect();
            if inst.is_pseudo() {
                out.push_str(&format!(
                    "        [pseudo] {:?} {}\n",
                    inst.opcode,
                    ops.join(", ")
                ));
            } else {
                out.push_str(&format!(
                    "  {flat_idx:5}: {:?} {}\n",
                    inst.opcode,
                    ops.join(", ")
                ));
                flat_idx += 1;
            }
        }
    }
    out
}

/// Dump the ADAPTER's LIR (pre-ISel): block ids in layout order, params,
/// terminators with explicit target block ids. This exposes the raw Block id
/// space that `select_switch_binary_search`'s next_block_id bump must clear.
#[test]
fn dump_aarch64_lir_blocks() {
    let dump_dir = std::env::var("TCG_A64_DUMP_DIR").unwrap_or_else(|_| {
        std::env::temp_dir()
            .join("a64_scale_dump")
            .display()
            .to_string()
    });
    std::fs::create_dir_all(&dump_dir).unwrap();
    for fixture in ["mir_value_matches.tir", "mir_fold_binop.tir"] {
        let module = load_fixture(fixture);
        let lir_functions = trust_cg_lower::translate_module_for_arch(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
        )
        .expect("adapter");
        let mut out = String::new();
        for (f, _) in &lir_functions {
            out.push_str(&format!(
                "=== {} === entry=b{} ({} blocks)\n",
                f.name,
                f.entry_block.0,
                f.blocks.len()
            ));
            for b in &f.block_order {
                let bb = &f.blocks[b];
                let params: Vec<String> = bb
                    .params
                    .iter()
                    .map(|(v, t)| format!("v{}:{:?}", v.0, t))
                    .collect();
                out.push_str(&format!("b{}({}):\n", b.0, params.join(", ")));
                for inst in &bb.instructions {
                    out.push_str(&format!("    {:?}\n", inst));
                }
            }
            out.push('\n');
        }
        let out_path = format!("{dump_dir}/{fixture}.lir");
        std::fs::write(&out_path, &out).unwrap();
        eprintln!("wrote {out_path} ({} bytes)", out.len());
    }
}

/// Dump the prepared aarch64 machine IR for both pinned modules to
/// $TCG_A64_DUMP_DIR (or the target tmp dir). Always passes; the artifact is
/// the dump.
#[test]
fn dump_aarch64_jit_fast_lowering() {
    let dump_dir = std::env::var("TCG_A64_DUMP_DIR").unwrap_or_else(|_| {
        std::env::temp_dir()
            .join("a64_scale_dump")
            .display()
            .to_string()
    });
    std::fs::create_dir_all(&dump_dir).unwrap();

    for fixture in ["mir_value_matches.tir", "mir_fold_binop.tir"] {
        let module = load_fixture(fixture);
        let funcs = prepare_aarch64_jit_fast(&module);
        let mut listing = String::new();
        for f in &funcs {
            listing.push_str(&dump_function(f));
            listing.push('\n');
        }
        let out_path = format!("{dump_dir}/{fixture}.lst");
        std::fs::write(&out_path, &listing).unwrap();
        eprintln!("wrote {out_path} ({} bytes)", listing.len());
    }
}

/// Structural lock on the REAL pinned IRs: after the full jit_fast pipeline,
/// no block may carry a second code segment fused behind an unconditional
/// branch/return — the signature shape of the BST-node/real-block id
/// collision (pre-fix, fold_binop's b24/b25 and shape_matches_ty's b29/b30
/// violated this).
#[test]
fn pinned_irs_have_no_fused_block_segments() {
    use trust_cg_ir::inst::AArch64Opcode as Op;
    for fixture in ["mir_value_matches.tir", "mir_fold_binop.tir"] {
        let module = load_fixture(fixture);
        for func in prepare_aarch64_jit_fast(&module) {
            for &bid in &func.block_order {
                let block = &func.blocks[bid.0 as usize];
                let real: Vec<_> = block
                    .insts
                    .iter()
                    .map(|iid| &func.insts[iid.0 as usize])
                    .filter(|i| !i.is_pseudo())
                    .collect();
                for (idx, inst) in real.iter().enumerate() {
                    if matches!(inst.opcode, Op::B | Op::Ret | Op::Br) {
                        assert_eq!(
                            idx,
                            real.len() - 1,
                            "{} b{}: unconditional {:?} at {} of {} — fused block \
                             segments (the A64-4 collision shape)",
                            func.name,
                            bid.0,
                            inst.opcode,
                            idx,
                            real.len()
                        );
                    }
                }
            }
        }
    }
}

/// The edge_bounds ISel limit (4xi128 sret / i128 pair binding) was a
/// fail-closed "value ... not defined before use" refusal rooted in
/// `select_bitcast` defining only the LOW half of a same-width i128<->u128
/// bitcast (no `i128_high_map` entry for pair consumers). That defect was
/// FIXED (b3618e0c: define BOTH register-pair halves, the aarch64 mirror of
/// the x86 fix), which LIFTS the limit: the fixture now compiles end to end.
/// This pin locks the lifted state — a reappearing "not defined before use"
/// on edge_bounds is a regression of the pair-tracking fix.
#[test]
fn edge_bounds_isel_limit_lifted() {
    let module = load_fixture("mir_edge_bounds.tir");
    let lir_functions = trust_cg_lower::translate_module_for_arch(
        &module,
        trust_cg_lower::GuardCarrierArch::AArch64,
    )
    .expect("adapter");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O1,
        emit_debug: false,
        verify_dispatch: DispatchVerifyMode::FallbackOnFailure,
        verify: false,
        cegis_superopt_budget_sec: None,
        target_triple: String::new(),
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: true,
        skip_cse_gvn: false,
        disabled_passes_override: None,
        contains4_scanner_batch_rewrite_override: None,
    });
    let mut errors = Vec::new();
    for (lir_func, proof_ctx) in &lir_functions {
        if let Err(e) = pipeline.prepare_function_with_proofs(lir_func, Some(proof_ctx)) {
            errors.push(format!("{}: {e:?}", lir_func.name));
        }
    }
    assert!(
        errors.is_empty(),
        "edge_bounds compiles fully since the i128-pair bitcast fix (b3618e0c) \
         lifted the pinned ISel limit; a reappearing failure here is a \
         pair-tracking regression: {errors:#?}"
    );
}

// ===========================================================================
// Struct-level AArch64 MachInst interpreter.
//
// Executes the PREPARED (post-regalloc, post-frame-lowering, post-branch-
// resolution) machine IR on this x86 host: registers with X/W aliasing, NZCV,
// a flat little-endian memory, the Apple-arm64 call boundary (i128 pairs in
// consecutive GPRs — verified against clang -arch arm64), and the jump-table
// dispatch pattern (Adr JumpTableIndex base tagging; the 32-bit table-entry
// encoding is abstracted, index->target dispatch is faithful).
//
// This is the behavioral oracle that lets the aarch64-JIT pins run WITHOUT
// aarch64 hardware. Against the PRE-fix compiler it reproduces exactly the
// two pinned miscompile sets (validating the model); against the FIXED
// compiler every case must match the native oracle.
// ===========================================================================

mod interp {
    use std::collections::HashMap;
    use trust_cg_ir::MachFunction;
    use trust_cg_ir::inst::AArch64Opcode as Op;
    use trust_cg_ir::operand::MachOperand as O;
    use trust_cg_ir::regs::{RegClass, SpecialReg};

    const MEM_SIZE: usize = 4 << 20;
    const JT_TAG: u64 = 0xA100_0000_0000_0000;

    pub struct FlatFunc {
        pub name: String,
        pub insts: Vec<trust_cg_ir::inst::MachInst>,
        /// jump-table id -> (per-entry flat target index)
        pub jt_flat_targets: Vec<Vec<u64>>,
    }

    /// Flatten in layout order, skipping pseudos — the exact walk
    /// `resolve_branches` and the encoder use, so the Imm branch offsets are
    /// interpreted in the same instruction-index space they were computed in.
    pub fn flatten(func: &MachFunction) -> FlatFunc {
        let mut insts = Vec::new();
        let mut block_start: HashMap<u32, u64> = HashMap::new();
        for &bid in &func.block_order {
            block_start.insert(bid.0, insts.len() as u64);
            for &iid in &func.blocks[bid.0 as usize].insts {
                let inst = &func.insts[iid.0 as usize];
                if !inst.is_pseudo() {
                    insts.push(inst.clone());
                }
            }
        }
        let jt_flat_targets = func
            .jump_tables
            .iter()
            .map(|jt| {
                jt.targets
                    .iter()
                    .map(|b| {
                        *block_start
                            .get(&b.0)
                            .unwrap_or_else(|| panic!("jump table target b{} not laid out", b.0))
                    })
                    .collect()
            })
            .collect();
        FlatFunc {
            name: func.name.clone(),
            insts,
            jt_flat_targets,
        }
    }

    pub type HostShim<'h> = Box<dyn Fn(&mut Machine) + 'h>;

    pub struct Machine {
        pub regs: [u64; 31], // x0..x30
        pub sp: u64,
        n: bool,
        z: bool,
        c: bool,
        v: bool,
        pub mem: Vec<u8>,
        pub steps: u64,
    }

    impl Machine {
        pub fn new() -> Self {
            Machine {
                regs: [0xDEAD_BEEF_DEAD_BEEF; 31],
                sp: (MEM_SIZE - 64) as u64,
                n: false,
                z: false,
                c: false,
                v: false,
                mem: vec![0u8; MEM_SIZE],
                steps: 0,
            }
        }

        pub fn write_bytes(&mut self, addr: u64, bytes: &[u8]) {
            self.mem[addr as usize..addr as usize + bytes.len()].copy_from_slice(bytes);
        }
        pub fn read_u64(&self, addr: u64) -> u64 {
            u64::from_le_bytes(
                self.mem[addr as usize..addr as usize + 8]
                    .try_into()
                    .unwrap(),
            )
        }
        pub fn write_u64(&mut self, addr: u64, v: u64) {
            self.write_bytes(addr, &v.to_le_bytes());
        }
        pub fn read_i128(&self, addr: u64) -> i128 {
            i128::from_le_bytes(
                self.mem[addr as usize..addr as usize + 16]
                    .try_into()
                    .unwrap(),
            )
        }
        pub fn write_i128(&mut self, addr: u64, v: i128) {
            self.write_bytes(addr, &v.to_le_bytes());
        }

        fn read_op(&self, op: &O) -> u64 {
            match op {
                O::PReg(p) => self.read_preg(p.encoding()),
                O::Special(SpecialReg::SP) => self.sp,
                O::Special(SpecialReg::XZR) | O::Special(SpecialReg::WZR) => 0,
                O::Imm(i) => *i as u64,
                other => panic!("read of unsupported operand {other:?}"),
            }
        }
        fn read_preg(&self, enc: u16) -> u64 {
            match enc {
                0..=30 => self.regs[enc as usize],
                31 => self.sp,
                32..=62 => self.regs[(enc - 32) as usize] & 0xFFFF_FFFF,
                63 => self.sp & 0xFFFF_FFFF,
                other => panic!("read of unsupported preg encoding {other}"),
            }
        }
        fn write_op(&mut self, op: &O, val: u64) {
            match op {
                O::PReg(p) => self.write_preg(p.encoding(), val),
                O::Special(SpecialReg::SP) => self.sp = val,
                O::Special(SpecialReg::XZR) | O::Special(SpecialReg::WZR) => {}
                other => panic!("write to unsupported operand {other:?}"),
            }
        }
        fn write_preg(&mut self, enc: u16, val: u64) {
            match enc {
                0..=30 => self.regs[enc as usize] = val,
                31 => self.sp = val,
                32..=62 => self.regs[(enc - 32) as usize] = val & 0xFFFF_FFFF,
                63 => self.sp = val & 0xFFFF_FFFF,
                other => panic!("write to unsupported preg encoding {other}"),
            }
        }
        /// Width (32/64) of a register-ish operand, for flag/result semantics.
        fn op_is32(op: &O) -> bool {
            match op {
                O::PReg(p) => {
                    let e = p.encoding();
                    (32..=63).contains(&e)
                }
                O::VReg(v) => v.class == RegClass::Gpr32,
                O::Special(SpecialReg::WZR) => true,
                _ => false,
            }
        }
        fn set_flags_sub(&mut self, a: u64, b: u64, is32: bool) {
            if is32 {
                let (a, b) = (a as u32, b as u32);
                let r = a.wrapping_sub(b);
                self.n = (r as i32) < 0;
                self.z = r == 0;
                self.c = a >= b;
                self.v = ((a ^ b) & (a ^ r)) >> 31 == 1;
            } else {
                let r = a.wrapping_sub(b);
                self.n = (r as i64) < 0;
                self.z = r == 0;
                self.c = a >= b;
                self.v = ((a ^ b) & (a ^ r)) >> 63 == 1;
            }
        }
        fn cond(&self, cc: i64) -> bool {
            match cc {
                0 => self.z,                       // EQ
                1 => !self.z,                      // NE
                2 => self.c,                       // HS/CS
                3 => !self.c,                      // LO/CC
                4 => self.n,                       // MI
                5 => !self.n,                      // PL
                6 => self.v,                       // VS
                7 => !self.v,                      // VC
                8 => self.c && !self.z,            // HI
                9 => !self.c || self.z,            // LS
                10 => self.n == self.v,            // GE
                11 => self.n != self.v,            // LT
                12 => !self.z && self.n == self.v, // GT
                13 => self.z || self.n != self.v,  // LE
                14 => true,                        // AL
                other => panic!("unsupported condition code {other}"),
            }
        }

        /// Effective address for [base, #imm] and MemOp forms.
        fn addr2(&self, base: &O, off: &O) -> u64 {
            self.read_op(base).wrapping_add(self.read_op(off))
        }

        /// Run `entry` to completion (outermost Ret). Extern `Bl` targets not
        /// in `funcs` dispatch to `shims`.
        pub fn run(
            &mut self,
            funcs: &HashMap<String, FlatFunc>,
            shims: &HashMap<String, HostShim>,
            entry: &str,
        ) {
            // call stack of (function, resume pc)
            let mut stack: Vec<(&FlatFunc, u64)> = Vec::new();
            let mut cur = funcs
                .get(entry)
                .unwrap_or_else(|| panic!("entry {entry} not found"));
            let mut pc: u64 = 0;
            loop {
                self.steps += 1;
                assert!(
                    self.steps < 5_000_000,
                    "interpreter exceeded step budget (control-flow loop?) in {}",
                    cur.name
                );
                let inst = &cur.insts[pc as usize];
                let ops = &inst.operands;
                let mut next = pc + 1;
                match inst.opcode {
                    Op::Movz => {
                        let imm = self.read_op(&ops[1]);
                        let sh = ops.get(2).map(|o| self.read_op(o)).unwrap_or(0);
                        self.write_op(&ops[0], imm << sh);
                    }
                    Op::Movn => {
                        let imm = self.read_op(&ops[1]);
                        let sh = ops.get(2).map(|o| self.read_op(o)).unwrap_or(0);
                        let v = !(imm << sh);
                        let v = if Self::op_is32(&ops[0]) {
                            v & 0xFFFF_FFFF
                        } else {
                            v
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::Movk => {
                        let old = self.read_op(&ops[0]);
                        let imm = self.read_op(&ops[1]);
                        let sh = ops.get(2).map(|o| self.read_op(o)).unwrap_or(0);
                        self.write_op(&ops[0], (old & !(0xFFFFu64 << sh)) | (imm << sh));
                    }
                    Op::MovR | Op::MOVXrr | Op::MOVWrr | Op::Copy => {
                        let v = self.read_op(&ops[1]);
                        self.write_op(&ops[0], v);
                    }
                    Op::AddRI | Op::AddRR => {
                        let v = self.read_op(&ops[1]).wrapping_add(self.read_op(&ops[2]));
                        self.write_op(&ops[0], v);
                    }
                    Op::SubRI | Op::SubRR => {
                        let v = self.read_op(&ops[1]).wrapping_sub(self.read_op(&ops[2]));
                        self.write_op(&ops[0], v);
                    }
                    Op::Madd => {
                        let v = self.read_op(&ops[3]).wrapping_add(
                            self.read_op(&ops[1]).wrapping_mul(self.read_op(&ops[2])),
                        );
                        self.write_op(&ops[0], v);
                    }
                    Op::AndRR | Op::AndRI => {
                        let v = self.read_op(&ops[1]) & self.read_op(&ops[2]);
                        self.write_op(&ops[0], v);
                    }
                    Op::OrrRR | Op::OrrRI => {
                        let v = self.read_op(&ops[1]) | self.read_op(&ops[2]);
                        self.write_op(&ops[0], v);
                    }
                    Op::EorRR | Op::EorRI => {
                        let v = self.read_op(&ops[1]) ^ self.read_op(&ops[2]);
                        self.write_op(&ops[0], v);
                    }
                    Op::AsrRI => {
                        let a = self.read_op(&ops[1]);
                        let sh = self.read_op(&ops[2]) as u32;
                        let v = if Self::op_is32(&ops[0]) {
                            (((a as u32) as i32) >> (sh & 31)) as u32 as u64
                        } else {
                            ((a as i64) >> (sh & 63)) as u64
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::LslRI => {
                        let a = self.read_op(&ops[1]);
                        let sh = self.read_op(&ops[2]) as u32;
                        let v = if Self::op_is32(&ops[0]) {
                            (((a as u32) << (sh & 31)) as u64) & 0xFFFF_FFFF
                        } else {
                            a << (sh & 63)
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::LsrRI => {
                        let a = self.read_op(&ops[1]);
                        let sh = self.read_op(&ops[2]) as u32;
                        let v = if Self::op_is32(&ops[0]) {
                            ((a as u32) >> (sh & 31)) as u64
                        } else {
                            a >> (sh & 63)
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::Sxtb => {
                        let v = self.read_op(&ops[1]) as u8 as i8 as i64 as u64;
                        let v = if Self::op_is32(&ops[0]) {
                            v & 0xFFFF_FFFF
                        } else {
                            v
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::Sxth => {
                        let v = self.read_op(&ops[1]) as u16 as i16 as i64 as u64;
                        let v = if Self::op_is32(&ops[0]) {
                            v & 0xFFFF_FFFF
                        } else {
                            v
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::Sxtw => {
                        let v = self.read_op(&ops[1]) as u32 as i32 as i64 as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::Uxtb => {
                        let v = self.read_op(&ops[1]) as u8 as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::Uxth => {
                        let v = self.read_op(&ops[1]) as u16 as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::Uxtw => {
                        let v = self.read_op(&ops[1]) as u32 as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::CmpRI | Op::CmpRR => {
                        let is32 = Self::op_is32(&ops[0]);
                        let a = self.read_op(&ops[0]);
                        let b = self.read_op(&ops[1]);
                        self.set_flags_sub(a, b, is32);
                    }
                    Op::CSet => {
                        let cc = match &ops[1] {
                            O::Imm(i) => *i,
                            other => panic!("CSet cc operand {other:?}"),
                        };
                        let v = self.cond(cc) as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::Csel => {
                        let cc = match &ops[3] {
                            O::Imm(i) => *i,
                            other => panic!("Csel cc operand {other:?}"),
                        };
                        let v = if self.cond(cc) {
                            self.read_op(&ops[1])
                        } else {
                            self.read_op(&ops[2])
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::B => {
                        let rel = match &ops[0] {
                            O::Imm(i) => *i,
                            other => panic!("unresolved B target {other:?}"),
                        };
                        next = pc.wrapping_add_signed(rel);
                    }
                    Op::BCond => {
                        let (cc, rel) = match (&ops[0], &ops[1]) {
                            (O::Imm(cc), O::Imm(rel)) => (*cc, *rel),
                            other => panic!("unresolved BCond {other:?}"),
                        };
                        if self.cond(cc) {
                            next = pc.wrapping_add_signed(rel);
                        }
                    }
                    Op::Cbz | Op::Cbnz => {
                        let v = self.read_op(&ops[0]);
                        let rel = match &ops[1] {
                            O::Imm(i) => *i,
                            other => panic!("unresolved Cbz/Cbnz {other:?}"),
                        };
                        let v = if Self::op_is32(&ops[0]) {
                            v & 0xFFFF_FFFF
                        } else {
                            v
                        };
                        let taken = (inst.opcode == Op::Cbz) == (v == 0);
                        if taken {
                            next = pc.wrapping_add_signed(rel);
                        }
                    }
                    Op::Adr => {
                        let jti = match &ops[1] {
                            O::JumpTableIndex(i) => *i as u64,
                            other => panic!("Adr with non-jump-table operand {other:?}"),
                        };
                        self.write_op(&ops[0], JT_TAG | (jti << 32));
                    }
                    Op::LdrswRO => {
                        let base = self.read_op(&ops[1]);
                        assert_eq!(
                            base & 0xFF00_0000_0000_0000,
                            JT_TAG,
                            "LdrswRO base is not a jump-table tag (modeled only for switch dispatch)"
                        );
                        let jti = ((base >> 32) & 0xFFFF) as usize;
                        let index = self.read_op(&ops[2]) as usize;
                        let flat = cur.jt_flat_targets[jti]
                            .get(index)
                            .copied()
                            .unwrap_or_else(|| panic!("jump table {jti} index {index} OOB"));
                        // offset such that ADD target = base + offset = flat index
                        self.write_op(&ops[0], flat.wrapping_sub(base));
                    }
                    Op::Br => {
                        // Jump-table dispatch tail: register holds the flat index.
                        next = self.read_op(&ops[0]);
                        assert!(
                            (next as usize) < cur.insts.len(),
                            "Br to out-of-range flat index {next}"
                        );
                    }
                    Op::LdrRI => {
                        let (addr, is32) = match ops.as_slice() {
                            [dst, O::MemOp { base, offset }] => (
                                self.read_preg(base.encoding()).wrapping_add(*offset as u64),
                                Self::op_is32(dst),
                            ),
                            [dst, base, off] => (self.addr2(base, off), Self::op_is32(dst)),
                            other => panic!("LdrRI operands {other:?}"),
                        };
                        let v = if is32 {
                            u32::from_le_bytes(
                                self.mem[addr as usize..addr as usize + 4]
                                    .try_into()
                                    .unwrap(),
                            ) as u64
                        } else {
                            self.read_u64(addr)
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::StrRI => {
                        let (addr, is32) = match ops.as_slice() {
                            [src, O::MemOp { base, offset }] => (
                                self.read_preg(base.encoding()).wrapping_add(*offset as u64),
                                Self::op_is32(src),
                            ),
                            [src, base, off] => (self.addr2(base, off), Self::op_is32(src)),
                            other => panic!("StrRI operands {other:?}"),
                        };
                        let v = self.read_op(&ops[0]);
                        if is32 {
                            self.write_bytes(addr, &(v as u32).to_le_bytes());
                        } else {
                            self.write_u64(addr, v);
                        }
                    }
                    Op::LdrbRI => {
                        let addr = match ops.as_slice() {
                            [_, O::MemOp { base, offset }] => {
                                self.read_preg(base.encoding()).wrapping_add(*offset as u64)
                            }
                            [_, base, off] => self.addr2(base, off),
                            other => panic!("LdrbRI operands {other:?}"),
                        };
                        let v = self.mem[addr as usize] as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::StrbRI => {
                        let addr = match ops.as_slice() {
                            [_, O::MemOp { base, offset }] => {
                                self.read_preg(base.encoding()).wrapping_add(*offset as u64)
                            }
                            [_, base, off] => self.addr2(base, off),
                            other => panic!("StrbRI operands {other:?}"),
                        };
                        let v = self.read_op(&ops[0]) as u8;
                        self.mem[addr as usize] = v;
                    }
                    Op::LdrshRI => {
                        let addr = match ops.as_slice() {
                            [_, base, off] => self.addr2(base, off),
                            other => panic!("LdrshRI operands {other:?}"),
                        };
                        let raw = u16::from_le_bytes(
                            self.mem[addr as usize..addr as usize + 2]
                                .try_into()
                                .unwrap(),
                        );
                        let v = raw as i16 as i64 as u64;
                        let v = if Self::op_is32(&ops[0]) {
                            v & 0xFFFF_FFFF
                        } else {
                            v
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::LdrsbRI => {
                        let addr = match ops.as_slice() {
                            [_, base, off] => self.addr2(base, off),
                            other => panic!("LdrsbRI operands {other:?}"),
                        };
                        let v = self.mem[addr as usize] as i8 as i64 as u64;
                        let v = if Self::op_is32(&ops[0]) {
                            v & 0xFFFF_FFFF
                        } else {
                            v
                        };
                        self.write_op(&ops[0], v);
                    }
                    Op::LdrhRI => {
                        let addr = match ops.as_slice() {
                            [_, base, off] => self.addr2(base, off),
                            other => panic!("LdrhRI operands {other:?}"),
                        };
                        let v = u16::from_le_bytes(
                            self.mem[addr as usize..addr as usize + 2]
                                .try_into()
                                .unwrap(),
                        ) as u64;
                        self.write_op(&ops[0], v);
                    }
                    Op::StpRI => {
                        let base = self.read_op(&ops[2]);
                        let off = self.read_op(&ops[3]);
                        let addr = base.wrapping_add(off);
                        let a = self.read_op(&ops[0]);
                        let b = self.read_op(&ops[1]);
                        self.write_u64(addr, a);
                        self.write_u64(addr + 8, b);
                    }
                    Op::LdpRI => {
                        let base = self.read_op(&ops[2]);
                        let off = self.read_op(&ops[3]);
                        let addr = base.wrapping_add(off);
                        let a = self.read_u64(addr);
                        let b = self.read_u64(addr + 8);
                        self.write_op(&ops[0], a);
                        self.write_op(&ops[1], b);
                    }
                    Op::StpPreIndex => {
                        let base = self.read_op(&ops[2]).wrapping_add(self.read_op(&ops[3]));
                        self.write_op(&ops[2], base);
                        let a = self.read_op(&ops[0]);
                        let b = self.read_op(&ops[1]);
                        self.write_u64(base, a);
                        self.write_u64(base + 8, b);
                    }
                    Op::LdpPostIndex => {
                        let base = self.read_op(&ops[2]);
                        let a = self.read_u64(base);
                        let b = self.read_u64(base + 8);
                        self.write_op(&ops[0], a);
                        self.write_op(&ops[1], b);
                        let nb = base.wrapping_add(self.read_op(&ops[3]));
                        self.write_op(&ops[2], nb);
                    }
                    Op::Bl => {
                        let sym = match &ops[0] {
                            O::Symbol(s) => s.clone(),
                            other => panic!("Bl operand {other:?}"),
                        };
                        if let Some(callee) = funcs.get(&sym) {
                            stack.push((cur, pc + 1));
                            cur = callee;
                            next = 0;
                        } else if let Some(shim) = shims.get(&sym) {
                            shim(self);
                        } else {
                            panic!("call to unbound extern symbol {sym}");
                        }
                    }
                    Op::Ret => match stack.pop() {
                        Some((caller, resume)) => {
                            cur = caller;
                            next = resume;
                        }
                        None => return,
                    },
                    ref other => panic!(
                        "unsupported opcode {other:?} at {}:{pc} (operands {ops:?})",
                        cur.name
                    ),
                }
                pc = next;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Faithful input construction (identical to the aarch64 roundtrip pins and
// the x86 faithful tests: LP64, same rustc => byte-identical layouts).
// ---------------------------------------------------------------------------

#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmStructId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmTyId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmFuncTyId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmEnumId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmRecordId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmClosureTyId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmFuncId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, Default)]
enum VmSetRepr {
    Bitset,
    #[default]
    Boxed,
}
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum VmFatPtrKind {
    Slice(VmTyId),
    Str,
    TraitObject { trait_id: u32 },
}

#[allow(dead_code)]
#[derive(Clone, PartialEq, Eq)]
enum VmTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F16,
    F32,
    F64,
    Bool,
    Vector(Box<VmTy>, u32),
    Ptr,
    FatPtr(VmFatPtrKind),
    Unit,
    Never,
    Struct(VmStructId),
    Array(VmTyId, u64),
    Tuple(Vec<VmTy>),
    Enum(VmEnumId),
    Func(VmFuncTyId),
    Ref(Box<VmTy>),
    RefMut(Box<VmTy>),
    PtrConst(Box<VmTy>),
    PtrMut(Box<VmTy>),
    Rc(Box<VmTy>),
    Set(VmTyId, VmSetRepr),
    Sequence(VmTyId),
    Record(VmRecordId),
    Closure(VmClosureTyId),
}
impl VmTy {
    fn is_integer(&self) -> bool {
        self.is_signed() || self.is_unsigned()
    }
    fn is_signed(&self) -> bool {
        matches!(
            self,
            VmTy::I8 | VmTy::I16 | VmTy::I32 | VmTy::I64 | VmTy::I128
        )
    }
    fn is_unsigned(&self) -> bool {
        matches!(
            self,
            VmTy::U8 | VmTy::U16 | VmTy::U32 | VmTy::U64 | VmTy::U128
        )
    }
    fn is_float(&self) -> bool {
        matches!(self, VmTy::F16 | VmTy::F32 | VmTy::F64)
    }
}
#[allow(dead_code)]
#[derive(Clone)]
enum VmConstant {
    Int(i128),
    Float(f64),
    Bool(bool),
    Aggregate(Vec<VmConstant>),
    Array(Vec<VmConstant>),
    Vector(Vec<VmConstant>),
    Sequence(Vec<VmConstant>),
    Set(Vec<VmConstant>),
    Record(Vec<(String, VmConstant)>),
    Closure {
        func: VmFuncId,
        captures: Vec<VmConstant>,
    },
    FnDef(VmFuncId),
    SymbolAddr {
        symbol: String,
        addend: i64,
    },
    PhantomData,
}
impl VmConstant {
    fn shape_matches_ty(&self, ty: &VmTy) -> bool {
        match (self, ty) {
            (VmConstant::Int(_), t) if t.is_integer() => true,
            (VmConstant::Int(_), VmTy::Ptr) => true,
            (VmConstant::Float(_), t) if t.is_float() => true,
            (VmConstant::Bool(_), VmTy::Bool) => true,
            (VmConstant::Aggregate(_), VmTy::Tuple(_))
            | (VmConstant::Aggregate(_), VmTy::Array(_, _))
            | (VmConstant::Aggregate(_), VmTy::Struct(_))
            | (VmConstant::Aggregate(_), VmTy::Record(_)) => true,
            (VmConstant::Array(_), VmTy::Array(_, _)) => true,
            (VmConstant::Vector(_), VmTy::Vector(_, _)) => true,
            (VmConstant::Sequence(_), VmTy::Sequence(_)) => true,
            (VmConstant::Set(_), VmTy::Set(_, _)) => true,
            (VmConstant::Record(_), VmTy::Record(_)) => true,
            (VmConstant::Closure { .. }, VmTy::Closure(_)) => true,
            (VmConstant::FnDef(_), VmTy::Func(_)) => true,
            (VmConstant::SymbolAddr { .. }, VmTy::Ptr) => true,
            (VmConstant::SymbolAddr { .. }, VmTy::Func(_)) => true,
            (VmConstant::PhantomData, VmTy::Unit) => true,
            _ => false,
        }
    }
}

fn bytes_of<T>(v: &T) -> Vec<u8> {
    unsafe {
        std::slice::from_raw_parts(v as *const T as *const u8, std::mem::size_of::<T>()).to_vec()
    }
}

fn flatten_module(funcs: &[MachFunction]) -> std::collections::HashMap<String, interp::FlatFunc> {
    funcs
        .iter()
        .map(|f| (f.name.clone(), interp::flatten(f)))
        .collect()
}

/// BEHAVIORAL pin, aarch64 semantics on an x86 host: `Constant__shape_matches_ty`
/// must return the native-oracle boolean for every case — INCLUDING the two
/// documented aarch64-JIT miscompiles (Int vs Ptr, Float vs F64). Against the
/// pre-fix compiler this test fails on exactly those two cases (verified),
/// reproducing KNOWN_TRUSTCG_SHAPE_FALLBACK_MISCOMPILES without hardware.
#[test]
fn interp_shape_matches_ty_matches_native_oracle() {
    let module = load_fixture("mir_value_matches.tir");
    let funcs = prepare_aarch64_jit_fast(&module);
    let flat = flatten_module(&funcs);

    let cases: Vec<(VmConstant, VmTy, &str)> = vec![
        (
            VmConstant::Int(5),
            VmTy::Ptr,
            "Int vs Ptr [was aarch64 MISCOMPILE -> false]",
        ),
        (
            VmConstant::Float(1.0),
            VmTy::F64,
            "Float vs F64 [was aarch64 MISCOMPILE -> false]",
        ),
        (VmConstant::Int(5), VmTy::I32, "Int vs I32"),
        (VmConstant::Int(5), VmTy::U64, "Int vs U64"),
        (VmConstant::Int(5), VmTy::Bool, "Int vs Bool"),
        (VmConstant::Bool(true), VmTy::Bool, "Bool vs Bool"),
        (VmConstant::Float(2.5), VmTy::I32, "Float vs I32"),
        (VmConstant::Int(5), VmTy::Unit, "Int vs Unit"),
        (VmConstant::PhantomData, VmTy::Unit, "PhantomData vs Unit"),
        (VmConstant::Float(2.5), VmTy::F32, "Float vs F32"),
        (VmConstant::Bool(false), VmTy::U8, "Bool vs U8"),
    ];

    let mut failures = Vec::new();
    for (c, ty, label) in &cases {
        let want = c.shape_matches_ty(ty);
        let mut m = interp::Machine::new();
        let caddr = 0x1000u64;
        let taddr = 0x2000u64;
        m.write_bytes(caddr, &bytes_of(c));
        m.write_bytes(taddr, &bytes_of(ty));
        m.regs[0] = caddr;
        m.regs[1] = taddr;
        m.run(
            &flat,
            &std::collections::HashMap::new(),
            "Constant__shape_matches_ty",
        );
        let got = (m.regs[0] & 0xFF) != 0;
        eprintln!("[shape {label}] native={want} interp(a64)={got}");
        if got != want {
            failures.push(format!("{label}: native={want} interp={got}"));
        }
    }
    assert!(
        failures.is_empty(),
        "aarch64 lowering behavioral mismatches (the A64-4 miscompile class): {failures:#?}"
    );
}

/// Same behavioral pin for the scalar paths of `Constant__value_matches_ty`
/// (Int -> in-module int_value_fits_ty; non-Int/non-Vector -> shape fallback).
/// Vector cases need the container externs and are exercised natively by the
/// aarch64 roundtrip; scalar coverage here is what the pinned mismatch set
/// lived in.
#[test]
fn interp_value_matches_ty_scalar_matches_native_oracle() {
    let module = load_fixture("mir_value_matches.tir");
    let funcs = prepare_aarch64_jit_fast(&module);
    let flat = flatten_module(&funcs);

    fn vm_int_value_fits_ty(value: i128, ty: &VmTy) -> bool {
        match ty {
            VmTy::I8 => value >= i8::MIN as i128 && value <= i8::MAX as i128,
            VmTy::I16 => value >= i16::MIN as i128 && value <= i16::MAX as i128,
            VmTy::I32 => value >= i32::MIN as i128 && value <= i32::MAX as i128,
            VmTy::I64 => value >= i64::MIN as i128 && value <= i64::MAX as i128,
            VmTy::I128 => true,
            VmTy::U8 => value >= 0 && value <= u8::MAX as i128,
            VmTy::U16 => value >= 0 && value <= u16::MAX as i128,
            VmTy::U32 => value >= 0 && value <= u32::MAX as i128,
            VmTy::U64 => value >= 0 && value <= u64::MAX as i128,
            VmTy::U128 => value >= 0,
            _ => false,
        }
    }
    fn native(c: &VmConstant, ty: &VmTy) -> bool {
        match (c, ty) {
            (VmConstant::Int(v), t) if t.is_integer() => vm_int_value_fits_ty(*v, t),
            _ => c.shape_matches_ty(ty),
        }
    }

    let cases: Vec<(VmConstant, VmTy, &str)> = vec![
        (VmConstant::Int(127), VmTy::I8, "127:i8 fit"),
        (VmConstant::Int(128), VmTy::I8, "128:i8 past"),
        (VmConstant::Int(-128), VmTy::I8, "-128:i8 fit"),
        (VmConstant::Int(-129), VmTy::I8, "-129:i8 past"),
        (VmConstant::Int(255), VmTy::U8, "255:u8 fit"),
        (VmConstant::Int(256), VmTy::U8, "256:u8 past"),
        (VmConstant::Int(-1), VmTy::U8, "-1:u8 neg"),
        (VmConstant::Int(u64::MAX as i128), VmTy::U64, "u64::MAX:u64"),
        (
            VmConstant::Int(u64::MAX as i128 + 1),
            VmTy::U64,
            "u64::MAX+1:u64",
        ),
        (VmConstant::Int(i128::MAX), VmTy::I128, "i128::MAX:i128"),
        (VmConstant::Int(i128::MIN), VmTy::I128, "i128::MIN:i128"),
        (
            VmConstant::Int(5),
            VmTy::Ptr,
            "5:ptr (shape Int->Ptr) [was MISCOMPILE]",
        ),
        (
            VmConstant::Float(1.5),
            VmTy::F64,
            "Float vs F64 (shape) [was MISCOMPILE]",
        ),
        (VmConstant::Float(1.5), VmTy::I32, "Float vs I32 (shape)"),
        (VmConstant::Bool(true), VmTy::Bool, "Bool vs Bool (shape)"),
        (
            VmConstant::PhantomData,
            VmTy::Unit,
            "PhantomData vs Unit (shape)",
        ),
    ];

    let mut failures = Vec::new();
    for (c, ty, label) in &cases {
        let want = native(c, ty);
        let mut m = interp::Machine::new();
        let caddr = 0x1000u64;
        let taddr = 0x2000u64;
        m.write_bytes(caddr, &bytes_of(c));
        m.write_bytes(taddr, &bytes_of(ty));
        m.regs[0] = caddr;
        m.regs[1] = taddr;
        m.run(
            &flat,
            &std::collections::HashMap::new(),
            "Constant__value_matches_ty",
        );
        let got = (m.regs[0] & 0xFF) != 0;
        eprintln!("[value {label}] native={want} interp(a64)={got}");
        if got != want {
            failures.push(format!("{label}: native={want} interp={got}"));
        }
    }
    assert!(
        failures.is_empty(),
        "aarch64 lowering behavioral mismatches (the A64-4 miscompile class): {failures:#?}"
    );
}

/// BEHAVIORAL pin for fold_binop: every case — including all the pinned
/// KNOWN_TRUSTCG_FOLD_SHL_MISCOMPILES inputs (Shl must produce Some, not
/// None) — must match the native oracle. Pre-fix, every Shl input either
/// returned None or looped in the collided dispatch blocks.
#[test]
fn interp_fold_binop_matches_native_oracle() {
    let module = load_fixture("mir_fold_binop.tir");
    let funcs = prepare_aarch64_jit_fast(&module);
    let flat = flatten_module(&funcs);

    // The extern shims, byte-for-byte the semantics of the roundtrip test's
    // Rust shims, at the Apple-arm64 boundary trust-cg emits (out in x0,
    // i128 args in CONSECUTIVE GPR pairs — verified against clang arm64).
    fn read_pair(m: &interp::Machine, lo: usize, hi: usize) -> i128 {
        ((m.regs[hi] as u128) << 64 | m.regs[lo] as u128) as i128
    }
    fn write_opt(m: &mut interp::Machine, out: u64, v: Option<i128>) {
        match v {
            Some(x) => {
                m.write_i128(out, 1);
                m.write_i128(out + 16, x);
            }
            None => {
                m.write_i128(out, 0);
                m.write_i128(out + 16, 0);
            }
        }
    }
    let mut shims: std::collections::HashMap<String, interp::HostShim> =
        std::collections::HashMap::new();
    shims.insert(
        "_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnENtNtNtB7_3ops9try_trait3Try6branchCs99MkpMfQ48c_23trust_fold_binop2_slice".to_string(),
        Box::new(|m: &mut interp::Machine| {
            let (out, opt) = (m.regs[0], m.regs[1]);
            let disc = m.read_i128(opt);
            if disc == 1 {
                let v = m.read_i128(opt + 16);
                m.write_i128(out, 0);
                m.write_i128(out + 16, v);
            } else {
                m.write_i128(out, 1);
                m.write_i128(out + 16, 0);
            }
        }),
    );
    shims.insert(
        "_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualCs99MkpMfQ48c_23trust_fold_binop2_slice".to_string(),
        Box::new(|m: &mut interp::Machine| {
            let out = m.regs[0];
            write_opt(m, out, None);
        }),
    );
    shims.insert(
        "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_addCs99MkpMfQ48c_23trust_fold_binop2_slice"
            .to_string(),
        Box::new(|m: &mut interp::Machine| {
            let out = m.regs[0];
            let (a, b) = (read_pair(m, 1, 2), read_pair(m, 3, 4));
            write_opt(m, out, a.checked_add(b));
        }),
    );
    shims.insert(
        "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_subCs99MkpMfQ48c_23trust_fold_binop2_slice"
            .to_string(),
        Box::new(|m: &mut interp::Machine| {
            let out = m.regs[0];
            let (a, b) = (read_pair(m, 1, 2), read_pair(m, 3, 4));
            write_opt(m, out, a.checked_sub(b));
        }),
    );
    shims.insert(
        "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_mulCs99MkpMfQ48c_23trust_fold_binop2_slice"
            .to_string(),
        Box::new(|m: &mut interp::Machine| {
            let out = m.regs[0];
            let (a, b) = (read_pair(m, 1, 2), read_pair(m, 3, 4));
            write_opt(m, out, a.checked_mul(b));
        }),
    );
    shims.insert(
        "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_shlCs99MkpMfQ48c_23trust_fold_binop2_slice"
            .to_string(),
        Box::new(|m: &mut interp::Machine| {
            let out = m.regs[0];
            let val = read_pair(m, 1, 2);
            let shift = (m.regs[3] & 0xFFFF_FFFF) as u32;
            write_opt(m, out, val.checked_shl(shift));
        }),
    );

    // (op, lhs, rhs) with the same case list as the x86 faithful test /
    // aarch64 pin; expected per the native oracle.
    fn native(op: u8, lhs: Option<i128>, rhs: Option<i128>) -> Option<i128> {
        let (a, b) = (lhs?, rhs?);
        match op {
            0 => a.checked_add(b),
            1 => a.checked_sub(b),
            2 => a.checked_mul(b),
            14 => Some(a & b),
            15 => Some(a | b),
            16 => Some(a ^ b),
            17 => {
                if b < 0 || b >= 128 {
                    return None;
                }
                1i128.checked_shl(b as u32).and_then(|m| a.checked_mul(m))
            }
            _ => None,
        }
    }
    let cases: Vec<(u8, Option<i128>, Option<i128>, &str)> = vec![
        (0, Some(2), Some(3), "Add 2,3"),
        (1, Some(10), Some(4), "Sub 10,4"),
        (2, Some(6), Some(7), "Mul 6,7"),
        (14, Some(12), Some(10), "And 12,10"),
        (15, Some(12), Some(3), "Or 12,3"),
        (16, Some(12), Some(10), "Xor 12,10"),
        (0, None, Some(3), "Add None,3"),
        (0, Some(3), None, "Add 3,None"),
        (
            17,
            Some(3),
            Some(4),
            "Shl 3<<4 [was aarch64 MISCOMPILE -> None]",
        ),
        (
            17,
            Some(1),
            Some(0),
            "Shl 1<<0 [was aarch64 MISCOMPILE -> None]",
        ),
        (
            17,
            Some(3),
            Some(63),
            "Shl 3<<63 [was aarch64 MISCOMPILE -> None]",
        ),
        (
            17,
            Some(1),
            Some(127),
            "Shl 1<<127 [was aarch64 MISCOMPILE -> None]",
        ),
        (17, Some(3), Some(126), "Shl 3<<126 overflow -> None"),
        (17, Some(5), Some(128), "Shl b>=128 -> None"),
        (17, Some(5), Some(-1), "Shl b<0 -> None"),
        (9, Some(5), Some(1), "unknown op -> None"),
    ];

    let mut failures = Vec::new();
    for (op, lhs, rhs, label) in &cases {
        let want = native(*op, *lhs, *rhs);
        let mut m = interp::Machine::new();
        let (out, l, r) = (0x1000u64, 0x2000u64, 0x3000u64);
        let enc = |m: &mut interp::Machine, addr: u64, v: &Option<i128>| match v {
            Some(x) => {
                m.write_i128(addr, 1);
                m.write_i128(addr + 16, *x);
            }
            None => {
                m.write_i128(addr, 0);
                m.write_i128(addr + 16, 0);
            }
        };
        enc(&mut m, l, lhs);
        enc(&mut m, r, rhs);
        m.write_i128(out, 99); // canary
        m.regs[0] = out;
        m.regs[1] = *op as u64;
        m.regs[2] = l;
        m.regs[3] = r;
        m.run(&flat, &shims, "fold_binop");
        let disc = m.read_i128(out);
        let val = m.read_i128(out + 16);
        let got = match disc {
            0 => None,
            1 => Some(val),
            d => panic!("{label}: bad out disc {d}"),
        };
        eprintln!("[fold {label}] native={want:?} interp(a64)={got:?}");
        if got != want {
            failures.push(format!("{label}: native={want:?} interp={got:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "aarch64 fold_binop behavioral mismatches (the A64-4 miscompile class): {failures:#?}"
    );
}
