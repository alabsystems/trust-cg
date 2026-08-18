// trust-cg-cli/tests/emit_proofs_flag.rs - Integration tests for --emit-proofs=<dir> (#421)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Exercises the CLI binary end-to-end at its current authority boundary:
//   1. `--emit-proofs=<dir>` PROMOTES an AOT object whose relocation kinds are
//      all covered by the aarch64 Mach-O Certified composition (solver-backed
//      value-proof lanes + default-Enforce ENC-9 reparse binding): the object
//      and its proof sidecars are published.
//   2. The composition stays fail-closed where no lane exists: the aarch64
//      ELF production registry is empty, so the same modules are rejected at
//      the object-authority boundary on `--target=aarch64-unknown-linux-gnu`.
//   3. Omitting the flag keeps ordinary (non-promoting) object emission working.
//   4. `--help` documents the flag and its fail-closed contract.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::inst::FCmpOp;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, Inst, InstrNode, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

/// Build a load-plus-add function with both reconstructed arithmetic coverage
/// and a genuine static memory proof. Its instruction bundle is promotable, so
/// a proof-required AOT compile reaches the later object-relocation gate.
fn make_test_module() -> TrustIrModule {
    // #62/#63: pure scalar ALU/div is covered by OPERAND RECONSTRUCTION and the
    // register-copy/RET epilogue is covered-elsewhere structural — neither produces
    // a STATIC ProofDatabase `.smt2` sidecar. Include a memory LOAD so the function
    // also exercises a genuine STATIC-DB lowering proof: the load opcode binds the
    // Memory effective-address family (store-then-load Roundtrip), which is NOT
    // reconstructed and would serialize to a per-rule `.smt2`/`.cert` pair once
    // the complete object authority gate can pass. (The add keeps an ALU row too.)
    let mut mb = ModuleBuilder::new("emit_proofs_flag_test");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("_add_load", ty);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let loaded = fb.load(Ty::I64, p);
    let r = fb.add(Ty::I64, loaded, b);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Build a floating-point comparison fixture. `Fcmp` now has a genuine static
/// value proof; this guards against mistaking the later object-relocation
/// rejection for an instruction-coverage failure.
fn make_fcmp_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("emit_proofs_fcmp_test");
    let ty = mb.add_func_type(vec![Ty::F32, Ty::F32], vec![Ty::Bool]);
    let mut fb = mb.function("_flt_cmp", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::F32);
    let b = fb.add_block_param(entry, Ty::F32);
    fb.switch_to_block(entry);
    let r = fb.fcmp(FCmpOp::OLt, Ty::F32, a, b);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

struct SpillFixtureBuilder {
    next_value: u32,
    body: Vec<InstrNode>,
}

impl SpillFixtureBuilder {
    fn new() -> Self {
        Self {
            next_value: 0,
            body: Vec::new(),
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let id = ValueId(self.next_value);
        self.next_value += 1;
        id
    }

    fn reserve_params(&mut self, count: u32) -> Vec<ValueId> {
        (0..count).map(|_| self.fresh_value()).collect()
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh_value();
        self.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn emit_void(&mut self, inst: Inst) {
        self.body.push(InstrNode::new(inst));
    }

    fn const_i64(&mut self, value: i64) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::I64,
            value: Constant::i64(value),
        })
    }

    fn binop(&mut self, op: BinOp, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs,
            rhs,
        })
    }

    fn index(&mut self, base: ValueId, index: ValueId) -> ValueId {
        self.emit(Inst::GEP {
            pointee_ty: Ty::I64,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn load_i64(&mut self, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty: Ty::I64,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn seal(self, block_id: BlockId, params: Vec<(ValueId, Ty)>) -> Block {
        let mut block = Block::new(block_id);
        for (value, ty) in params {
            block = block.with_param(value, ty);
        }
        block.body = self.body;
        block
    }
}

/// Build a real high-pressure trust_ir function that the AArch64 compiler lowers
/// through register allocation and frame lowering with spill slots.
fn make_frame_spill_module() -> TrustIrModule {
    const LANES: usize = 24;

    let mut b = SpillFixtureBuilder::new();
    let params = b.reserve_params(1);
    let input = params[0];
    let mut live_values = Vec::with_capacity(LANES);

    for lane in 0..LANES {
        let idx = b.const_i64(lane as i64);
        let addr = b.index(input, idx);
        let loaded = b.load_i64(addr);
        let multiplier = b.const_i64(((lane as i64) % 7) + 2);
        let product = b.binop(BinOp::Mul, loaded, multiplier);
        let bias = b.const_i64((lane as i64 * 17) - 31);
        live_values.push(b.binop(BinOp::Add, product, bias));
    }

    let mut acc = live_values[0];
    for value in live_values.into_iter().skip(1) {
        acc = b.binop(BinOp::Add, acc, value);
    }
    b.emit_void(Inst::Return { values: vec![acc] });

    let mut module = TrustIrModule::new("emit_proofs_real_frame_spill_test");
    let ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId(0), "_proof_frame_spill_reduce", ty_id, BlockId(0));
    func.blocks = vec![b.seal(BlockId(0), vec![(input, Ty::Ptr)])];
    module.add_function(func);
    module
}

fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_emit_proofs_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

fn find_files_with_suffix(root: &std::path::Path, suffix: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(p) = stack.pop() {
        let entries = match std::fs::read_dir(&p) {
            Ok(e) => e,
            Err(_) => continue,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path
                .file_name()
                .and_then(|s| s.to_str())
                .is_some_and(|name| name.ends_with(suffix))
            {
                out.push(path);
            }
        }
    }
    out
}

fn assert_object_authority_rejection(
    output: &std::process::Output,
    out_path: &std::path::Path,
    proofs_dir: &std::path::Path,
) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "proof-required AOT compile must fail closed while relocation authority is unbound. stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof promotion rejected")
            && stderr.contains("object relocation inventory")
            && stderr.contains("no object relocation proof is registered"),
        "rejection must identify the exact object-authority gap. stderr: {stderr}"
    );
    assert!(
        !out_path.exists(),
        "unpromotable object bytes must not be published. stderr: {stderr}"
    );
    assert!(
        find_files_with_suffix(proofs_dir, ".lowering.json").is_empty(),
        "lowering sidecars must not be published past a failed object gate. stderr: {stderr}"
    );
    assert!(
        find_files_with_suffix(proofs_dir, ".trust-proof-cert.json").is_empty(),
        "trust sidecars must not be published past a failed object gate. stderr: {stderr}"
    );
}

/// The aarch64 Mach-O relocation registry now carries the Certified
/// composition (solver-backed value-proof lanes + the default-Enforce ENC-9
/// reparse binding), so a proof-required AOT compile whose relocation kinds
/// are all lane-covered must PROMOTE: object published, sidecars written.
fn assert_object_promotes(
    output: &std::process::Output,
    out_path: &std::path::Path,
    proofs_dir: &std::path::Path,
) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "proof-required AOT compile with lane-covered relocation kinds must promote. stderr: {stderr}"
    );
    assert!(
        out_path.exists(),
        "the promoted object must be published. stderr: {stderr}"
    );
    assert!(
        !find_files_with_suffix(proofs_dir, ".lowering.json").is_empty(),
        "lowering sidecars must be published for a promoted object. stderr: {stderr}"
    );
    assert!(
        !find_files_with_suffix(proofs_dir, ".trust-proof-cert.json").is_empty(),
        "trust sidecars must be published for a promoted object. stderr: {stderr}"
    );
}

// ---------------------------------------------------------------------------
// Case 1: proof-required AOT emission clears the object-authority boundary.
//
// The aarch64 Mach-O production registry now cites the solver-backed
// aarch64_macho_data/call/tlvp_reloc_proofs lanes and the report is built
// under the default-Enforce ENC-9 reparse binding, so a module whose
// relocation kinds are all lane-covered promotes end to end.
//
// The promoting cases pass `--target=aarch64-apple-darwin` EXPLICITLY: they
// exercise the Mach-O Certified composition, which is target property, not a
// host property. With the target implicit they compile for the host default,
// and on an aarch64-Linux host that is the aarch64-ELF lane — whose registry
// is empty BY DESIGN (every function emits a DWARF FDE pc-begin PREL32 row,
// uncovered), directly contradicting Case 4b below, which pins that the same
// module under --target=aarch64-unknown-linux-gnu must be REJECTED.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_promotes_covered_object_relocations() {
    let dir = scratch_dir("promotes_covered_object_relocations");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    assert_object_promotes(&output, &out_path, &proofs_dir);

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 2: the same composition covers a real frame/spill object whose
// unwind table necessarily carries a relocation row (compact unwind /
// fallback FDE UNSIGNED rows are lane-covered too).
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_promotes_frame_spill_object() {
    let dir = scratch_dir("promotes_frame_spill_object");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_frame_spill_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    assert_object_promotes(&output, &out_path, &proofs_dir);

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 3: a formerly partial FCMP fixture clears instruction coverage AND the
// object-authority boundary. The negative opcode-coverage assert stays: a
// promotion must never be the by-product of skipping instruction coverage.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_fcmp_clears_object_authority_gate() {
    let dir = scratch_dir("fcmp_clears_object_authority_gate");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_fcmp_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_object_promotes(&output, &out_path, &proofs_dir);
    assert!(
        !stderr.contains("uncovered non-pseudo opcode")
            && !stderr.contains("no proof mapping for opcode"),
        "FCMP must clear instruction coverage, not skip it. stderr: {stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 4: sidecar I/O failures still fail the run loudly after the object
// gate passes. The serializer's own I/O failure behavior is covered in
// `emit_proofs` unit tests; the CLI must surface the sidecar failure with a
// non-zero exit instead of reporting a silently partial proof tree.
// ---------------------------------------------------------------------------

#[test]
fn cli_sidecar_io_failure_fails_loudly_after_object_promotes() {
    let dir = scratch_dir("sidecar_io_failure_fails_loudly");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    std::fs::create_dir_all(&proofs_dir).expect("create proofs dir");
    let lowering_sidecar_path = proofs_dir.join("_add_load.lowering.json");
    std::fs::create_dir(&lowering_sidecar_path).expect("create conflicting sidecar directory");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "a sidecar I/O failure must fail the run, not report a partial proof tree. stderr: {stderr}"
    );
    assert!(
        stderr.contains("failed to emit proof files"),
        "the failure must name the sidecar emission step. stderr: {stderr}"
    );
    assert!(
        lowering_sidecar_path.is_dir(),
        "the pre-existing conflict must remain untouched"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 4b: the LIVING FAIL-CLOSED CONTROL. The aarch64 ELF production
// registry is deliberately empty (no ELF-bound aarch64 value-proof lanes
// yet), so the same modules that promote on the Mach-O path must still hit
// the object-authority rejection on the ELF path. This keeps
// `assert_object_authority_rejection` exercised end to end.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_keeps_uncovered_aarch64_elf_target_fail_closed() {
    let dir = scratch_dir("keeps_uncovered_aarch64_elf_fail_closed");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_frame_spill_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg("--target=aarch64-unknown-linux-gnu")
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    assert_object_authority_rejection(&output, &out_path, &proofs_dir);

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 5: no flag => no proof files written.
// ---------------------------------------------------------------------------

#[test]
fn cli_no_flag_writes_no_proof_files() {
    let dir = scratch_dir("no_flag");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs_unused");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "plain compile should succeed. stderr: {}",
        stderr
    );
    assert!(
        !proofs_dir.exists(),
        "no proofs directory should be created without --emit-proofs"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 6: --help documents the flag.
// ---------------------------------------------------------------------------

#[test]
fn cli_help_documents_emit_proofs_flag() {
    let output = Command::new(trust_cg_bin())
        .arg("--help")
        .output()
        .expect("run trust-cg --help");
    assert!(output.status.success(), "--help should succeed");
    let help = String::from_utf8_lossy(&output.stdout);
    assert!(
        help.contains("--emit-proofs"),
        "--help must mention --emit-proofs. stdout:\n{}",
        help
    );
    assert!(
        help.contains("DIR"),
        "--help must show --emit-proofs accepts a directory. stdout:\n{}",
        help
    );
}
