// trust-cg-cli/tests/emit_proofs_flag.rs - Integration tests for --emit-proofs=<dir> (#421)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Certified export requires complete instruction evidence plus certified
// object relocation inventory. A leaf that only returns exercises the
// structural slice: it exports an object and per-rule audit .cert files, with
// no static SMT obligation or per-function lowering sidecar. Positive object
// publication and withdrawn-container controls use it on explicit AArch64
// Mach-O. Returning an argument keeps the FP/LR envelope in a proof-required
// compile on every target, so the identity exercises the narrow source-bound
// leaf frame with independent replay, object binding and formal export; on an
// aarch64 Linux host that certified ELF object is also linked with `cc`,
// compared word for word with the executable's `_identity`, and executed.
//
// Load-plus-add retains Statistical evidence. Floating comparisons and
// frame/spill programs additionally emit opcodes whose proof mappings were
// withdrawn. Each fixture pins its current exact rejection before publication.
// Keeping the original programs as negative controls prevents a weaker evidence
// tier from silently becoming certified output. Sidecar serialization itself is
// covered in emit_proofs.rs.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::inst::FCmpOp;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, Inst, InstrNode, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

/// Returning an argument binds its source/return relation through the
/// source-bound leaf frame, whose theorem must be independently replayed.
fn make_test_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("emit_proofs_flag_test");
    let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("_identity", ty);
    let entry = fb.create_block();
    let result = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A leaf that only returns. The zero-storage leaf policy keeps it frameless in
/// a proof-required compile on every target, so its only row is the RET the
/// covered-elsewhere allowlist admits: it exercises object authority without a
/// solver, sampled arithmetic, constants, memory rows or a frame theorem.
fn make_structural_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("emit_proofs_flag_structural_test");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("_structural", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The former load-plus-add promotion fixture. Reconstructed Iadd64 still
/// carries Statistical evidence, so it must not produce certified sidecars.
fn make_statistical_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("emit_proofs_statistical_test");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("_add_load", ty);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let loaded = fb.load(Ty::I64, p);
    let result = fb.add(Ty::I64, loaded, b);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// FCMP and its CSET name their NZCV producer/consumer theorems per instruction
/// (packed FCMP NZCV; FCMP -> CSET for the reaching FCMP). Since E0.2 a
/// registry theorem selected by name is not proof credit, so certified export
/// must still refuse this module — for that evidence limitation, naming both
/// theorems, not for a missing mapping.
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
    mb.build().expect("ModuleBuilder::build: test fixture")
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
    let ty_id = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId(0), "_proof_frame_spill_reduce", ty_id, BlockId(0));
    func.blocks = vec![b.seal(BlockId(0), vec![(input, Ty::Ptr)])];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// A new scratch directory, removed when the returned guard is dropped.
fn scratch_dir(test_name: &str) -> scratch::ScratchDir {
    scratch::create(&format!("trust_cg_cli_emit_proofs_{test_name}_"))
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

// ---------------------------------------------------------------------------
// Minimal ELF64 little-endian reader for the linked-image assertions. It reads
// only what the identity case needs (section headers, .symtab, PT_LOAD) and
// panics on anything else; the certificate is not involved in this parse.
// ---------------------------------------------------------------------------

struct ElfSection {
    name: String,
    kind: u32,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
}

fn le_u16(data: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(data[at..at + 2].try_into().unwrap())
}

fn le_u32(data: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(data[at..at + 4].try_into().unwrap())
}

fn le_u64(data: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(data[at..at + 8].try_into().unwrap())
}

fn c_string(data: &[u8], at: usize) -> String {
    let end = at + data[at..].iter().position(|&byte| byte == 0).unwrap();
    String::from_utf8_lossy(&data[at..end]).into_owned()
}

fn elf_sections(data: &[u8]) -> Vec<ElfSection> {
    assert!(
        data.starts_with(b"\x7fELF") && data[4] == 2 && data[5] == 1,
        "expected an ELF64 little-endian file"
    );
    assert_eq!(le_u16(data, 0x12), 183, "expected EM_AARCH64");
    assert_eq!(le_u16(data, 0x3a), 64, "ELF64 section header size");
    let shoff = le_u64(data, 0x28) as usize;
    let shnum = le_u16(data, 0x3c) as usize;
    let shstrndx = le_u16(data, 0x3e) as usize;
    let header = |index: usize| shoff + index * 64;
    let names = &data[le_u64(data, header(shstrndx) + 24) as usize..];
    (0..shnum)
        .map(|index| {
            let at = header(index);
            ElfSection {
                name: c_string(names, le_u32(data, at) as usize),
                kind: le_u32(data, at + 4),
                flags: le_u64(data, at + 8),
                addr: le_u64(data, at + 16),
                offset: le_u64(data, at + 24),
                size: le_u64(data, at + 32),
                link: le_u32(data, at + 40),
            }
        })
        .collect()
}

fn section_bytes<'a>(data: &'a [u8], section: &ElfSection) -> &'a [u8] {
    &data[section.offset as usize..(section.offset + section.size) as usize]
}

/// Every defined `.symtab` symbol named `name`: (st_info, st_shndx, st_value, st_size).
fn defined_symbols(data: &[u8], sections: &[ElfSection], name: &str) -> Vec<(u8, u16, u64, u64)> {
    let symtabs: Vec<&ElfSection> = sections.iter().filter(|s| s.kind == 2).collect();
    assert_eq!(symtabs.len(), 1, "expected exactly one .symtab");
    let strings = section_bytes(data, &sections[symtabs[0].link as usize]);
    section_bytes(data, symtabs[0])
        .as_chunks::<24>()
        .0
        .iter()
        .filter(|row| {
            le_u16(row.as_slice(), 6) != 0
                && c_string(strings, le_u32(row.as_slice(), 0) as usize) == name
        })
        .map(|row| {
            (
                row[4],
                le_u16(row.as_slice(), 6),
                le_u64(row.as_slice(), 8),
                le_u64(row.as_slice(), 16),
            )
        })
        .collect()
}

/// The certified object's function must be the one global FUNC filling its
/// executable `.text`; returns those bytes, which `machine_code_hash` binds
/// through the whole object.
fn certified_function_text(object: &[u8], name: &str) -> Vec<u8> {
    assert_eq!(le_u16(object, 0x10), 1, "certified object is ET_REL");
    let sections = elf_sections(object);
    let symbols = defined_symbols(object, &sections, name);
    assert_eq!(symbols.len(), 1, "{name} must be defined once: {symbols:?}");
    let (info, shndx, value, size) = symbols[0];
    assert_eq!(info, 0x12, "{name} must be a global function");
    let text = &sections[shndx as usize];
    assert_eq!(text.name, ".text");
    assert_eq!(
        text.flags & 0x6,
        0x6,
        ".text must be allocated and executable"
    );
    assert_eq!((value, size), (0, text.size), "{name} must fill .text");
    assert!(size > 0 && size % 4 == 0);
    section_bytes(object, text).to_vec()
}

/// Locate `name` in a linked executable by its symbol (a PIE's addresses are
/// link-time), map it through its executable PT_LOAD and return (VA, bytes).
fn linked_function_bytes(image: &[u8], name: &str, size: u64) -> (u64, Vec<u8>) {
    let sections = elf_sections(image);
    let symbols = defined_symbols(image, &sections, name);
    assert_eq!(symbols.len(), 1, "linked image must define {name} once");
    let (info, shndx, va, linked_size) = symbols[0];
    assert_eq!(info & 0xf, 2, "linked {name} must be a function");
    assert_eq!(linked_size, size, "linked {name} size");
    let section = &sections[shndx as usize];
    assert_eq!(
        section.flags & 0x6,
        0x6,
        "linked {name} must be in executable code"
    );
    assert!(section.addr <= va && va + size <= section.addr + section.size);
    let phoff = le_u64(image, 0x20) as usize;
    assert_eq!(le_u16(image, 0x36), 56, "ELF64 program header size");
    let loads: Vec<(u32, u64, u64, u64)> = (0..le_u16(image, 0x38) as usize)
        .map(|index| phoff + index * 56)
        .filter(|&at| le_u32(image, at) == 1)
        .map(|at| {
            (
                le_u32(image, at + 4),
                le_u64(image, at + 8),
                le_u64(image, at + 16),
                le_u64(image, at + 32),
            )
        })
        .filter(|&(_, _, vaddr, filesz)| vaddr <= va && va + size <= vaddr + filesz)
        .collect();
    assert_eq!(loads.len(), 1, "one PT_LOAD must map linked {name}");
    let (flags, offset, vaddr, _) = loads[0];
    assert_eq!(
        flags & 1,
        1,
        "the PT_LOAD mapping {name} must be executable"
    );
    let file_offset = offset + (va - vaddr);
    assert_eq!(file_offset, section.offset + (va - section.addr));
    (
        va,
        image[file_offset as usize..(file_offset + size) as usize].to_vec(),
    )
}

const IDENTITY_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>
extern int64_t _identity(int64_t);
int main(void) {
    static const int64_t values[] = {0, 1, -1, INT64_MIN, INT64_MAX, INT64_C(0x0123456789abcdef)};
    for (unsigned i = 0; i < sizeof values / sizeof values[0]; i++)
        if (_identity(values[i]) != values[i]) return 1;
    puts("IDENTITY_LINKED_OK calls=6");
    return 0;
}
"#;

/// Link the certified object with the host C compiler, require the executable
/// to carry the certified words at `_identity`'s link-time address, and run
/// it. On aarch64 Linux a missing `cc` fails the test: it is never a skip.
fn link_and_run_identity(dir: &std::path::Path, object: &std::path::Path, text: &[u8]) {
    let driver = dir.join("identity_driver.c");
    let exe = dir.join("identity_linked");
    std::fs::write(&driver, IDENTITY_DRIVER).expect("write C driver");
    let linked = Command::new("cc")
        .args(["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(&driver)
        .arg(object)
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap_or_else(|error| {
            panic!("the host C compiler `cc` is required on aarch64 Linux: {error}")
        });
    assert!(
        linked.status.success(),
        "cc failed to link the certified object: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let image = std::fs::read(&exe).expect("linked executable");
    let (va, bytes) = linked_function_bytes(&image, "_identity", text.len() as u64);
    assert!(va != 0, "a linked function has a nonzero link-time address");
    for (index, (linked, certified)) in bytes
        .as_chunks::<4>()
        .0
        .iter()
        .zip(text.as_chunks::<4>().0)
        .enumerate()
    {
        assert_eq!(
            linked,
            certified,
            "linked _identity word {index} (VA {:#x}) differs from the certified object",
            va + 4 * index as u64
        );
    }
    let run = Command::new(&exe)
        .output()
        .expect("run the linked identity leaf");
    assert!(
        run.status.success(),
        "linked identity leaf exited {:?}",
        run.status
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "IDENTITY_LINKED_OK calls=6"
    );
    eprintln!(
        "linked _identity at VA {va:#x}: {} word(s) equal to the certified .text; 6 calls returned their argument",
        text.len() / 4
    );
}

/// Withdraw the per-object reparse binding for EVERY object container this
/// invocation could select, so the fixture is unbound whatever lane it takes.
///
/// The binding half of the Certified composition is container-specific: ELF
/// objects are bound by `elf::reparse` (`TCG_NO_ELF_REPARSE`), Mach-O objects
/// by the ENC-9 gate in `macho::reparse` (`TCG_NO_MACHO_REPARSE`). A knob for
/// the wrong container is silently INERT — it withdraws nothing, the real
/// binding stays Enforce, and the object promotes on its genuine authority.
///
/// Any case that means to provoke the reparse-binding gap on a target it did
/// not pin explicitly must call this, never a single knob: the host default is
/// ELF on Linux and Mach-O on macOS, so a single knob makes the case
/// host-dependent, and a case that constructs no negative on some hosts is a
/// case that tests nothing there. Withdrawing MORE than the taken lane needs
/// is always safe — an inert knob cannot loosen a gate.
///
/// A case that DOES pin its target explicitly (4c, 4d) names that container's
/// knob alone: there the exact knob is the sharper statement, and it cannot go
/// inert because the target is not the host's to choose.
fn withdrawn_container_bindings() -> [(&'static str, &'static str); 2] {
    [("TCG_NO_ELF_REPARSE", "1"), ("TCG_NO_MACHO_REPARSE", "1")]
}

/// The general object-authority rejection contract: the run must fail closed,
/// name the object-relocation gap by its exact `expected_reason`, and publish
/// NEITHER the object bytes NOR any proof sidecar.
///
/// `expected_reason` distinguishes the two ways the gate can refuse, and every
/// caller must name the one it actually provokes — a caller that accepted
/// either string would pass for the wrong reason:
///   * `"lacks an independent reparse binding"` — the REPARSE-BINDING gap: the
///     value lanes stay registered but the per-object ENC-9/ELF reparse
///     evidence is withdrawn, so Trusted formula evidence never becomes a
///     Certified object verdict.
///   * `"no object relocation proof is registered"` — the REGISTRY gap: no
///     relocation value lane exists for the emitted kind at all. No CLI
///     fixture reaches it any more (the aarch64 and x86-64 ELF/Mach-O
///     production registries are all populated), so that arm is pinned in the
///     `trust_cg_verify::object_inventory` unit tests instead.
fn assert_object_authority_rejection_for(
    output: &std::process::Output,
    out_path: &std::path::Path,
    proofs_dir: &std::path::Path,
    expected_reason: &str,
) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "proof-required AOT compile must fail closed while relocation authority is unbound. stderr: {stderr}"
    );
    assert!(
        stderr.contains("proof promotion rejected")
            && stderr.contains("object relocation inventory")
            && stderr.contains(expected_reason),
        "rejection must identify the exact object-authority gap ({expected_reason}). stderr: {stderr}"
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
/// reparse binding). The structural fixture can publish its object and audit
/// certificates without inventing a static lowering obligation.
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
    let certificates = find_files_with_suffix(proofs_dir, ".cert");
    assert!(
        !certificates.is_empty(),
        "verified audit files must be published: {stderr}"
    );
    for path in certificates {
        let cert: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(
            cert["verified"], true,
            "exported an unverified audit row: {cert}"
        );
    }
    for suffix in [".smt2", ".lowering.json", ".trust-proof-cert.json"] {
        assert!(
            find_files_with_suffix(proofs_dir, suffix).is_empty(),
            "structural-only evidence must not fabricate {suffix} sidecars: {stderr}"
        );
    }
}

fn assert_uncredited_evidence_rejection(
    output: &std::process::Output,
    out_path: &std::path::Path,
    proofs_dir: &std::path::Path,
) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "uncredited evidence must not export: {stderr}"
    );
    // E0.2: the 64-bit ADD only samples, so it is reported, never credit.
    // The load (`LDR X2, [X0]`) is no longer uncovered: owner ruling
    // 2026-09-29 credits a bound-memory row by the replayed committed
    // certificate of its form theorem (`ScalarMem[ldr.ui.gpr.w8.zx]`), after
    // its instruction-derived obligation held (not refuted) — on a host whose
    // `drat-trim` bytes the bound-memory manifest qualifies. Elsewhere the
    // load stays uncovered, as a fail-closed checker-identity miss, and its
    // reason ends with its word's memory-effect decomposition (X-OPCODES-P1:
    // every part holds; recorded, never credit).
    if trust_cg_verify::bound_memory_authority::bound_memory_checker_qualification().is_err() {
        assert!(
            stderr.contains("proof promotion rejected")
                && stderr.contains(
                    "2 uncovered non-pseudo opcode(s) across 2 distinct opcode(s) \
                     [AArch64::LdrRI, AArch64::AddRR]"
                )
                && stderr.contains(&format!(
                    "is AArch64::LdrRI ({}: `A64 instruction word LdrRI 0xf9400002` holds",
                    trust_cg_verify::function_verifier::INSTRUCTION_DERIVED_IS_NOT_CREDIT
                ))
                && stderr.contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)
                && stderr.contains(&format!(
                    "; {}: `A64 memory effect LdrRI 0xf9400002` holds in process: all 3 parts \
                     exactly",
                    trust_cg_verify::function_verifier::MEMORY_EFFECT_IS_NOT_CREDIT
                )),
            "an unqualified host must refuse the load as a checker-identity miss: {stderr}"
        );
        assert!(
            !out_path.exists(),
            "uncertified object was published: {stderr}"
        );
        assert!(
            !proofs_dir.exists(),
            "uncertified proof files were published: {stderr}"
        );
        return;
    }
    assert!(
        stderr.contains("proof promotion rejected")
            && stderr.contains(
                "1 uncovered non-pseudo opcode(s) across 1 distinct opcode(s) \
                 [AArch64::AddRR]"
            )
            && stderr.contains(&format!(
                "is AArch64::AddRR ({}: `RECONSTRUCTED Iadd_64 -> AddRR (real-operand)`",
                trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
            ))
            && !stderr.contains("AArch64::LdrRI"),
        "rejection must preserve the actual evidence limitation: {stderr}"
    );
    assert!(
        !out_path.exists(),
        "uncertified object was published: {stderr}"
    );
    assert!(
        !proofs_dir.exists(),
        "uncertified proof files were published: {stderr}"
    );
}

// Preserve the exact uncovered opcode set and refusal before any publication.
// The arithmetic-only fixture separately guards sampled evidence above.
//
// The frame/spill fixture's bound-memory rows are CREDITED now (owner ruling
// 2026-09-29, `bound_memory_authority`): every emitted `STP`/`LDP` binds its
// pair form theorem and every `LDR`/`STR` spill its scalar form theorem, each
// credited `Formal` by a committed certificate the independent checker
// replays (the concrete-word and instruction-derived obligations are the
// rows' refutation checks, not credit). So no pair or scalar memory opcode
// may appear in the uncovered set, which is exactly the fixture's uncredited
// arithmetic, and the first refused row is that arithmetic's sampled
// obligation.
//
// That credit needs a host whose `drat-trim` bytes the bound-memory manifest
// qualifies. Elsewhere every bound-memory row misses fail closed, so the
// uncovered set is `unqualified_opcodes` (the arithmetic AND the memory rows,
// in inventory order) and the first refused row is the frame `STP`'s sampled
// pair obligation carrying the checker-identity miss, then its word's
// memory-effect decomposition (recorded, never credit).
/// The frame/spill fixture's uncovered set on a host whose checker the
/// bound-memory manifest does not qualify: exactly the set this fixture had
/// before the Formal-only rule credited its memory rows.
const UNQUALIFIED_FRAME_SPILL_SET: &[&str] = &[
    "StpPreIndex",
    "StpRI",
    "AddRI",
    "SubRI",
    "Movz",
    "Madd",
    "LdrRI",
    "Movn",
    "StrRI",
    "AddRR",
    "LdpRI",
    "LdpPostIndex",
];

fn assert_frame_spill_rejection_names_only_uncredited_arithmetic(
    output: &std::process::Output,
    out_path: &std::path::Path,
    proofs_dir: &std::path::Path,
    opcodes: &[&str],
    unqualified_opcodes: &[&str],
) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    if trust_cg_verify::bound_memory_authority::bound_memory_checker_qualification().is_err() {
        let names = unqualified_opcodes
            .iter()
            .map(|name| format!("AArch64::{name}"))
            .collect::<Vec<_>>();
        assert!(
            !output.status.success()
                && stderr.contains("proof promotion rejected")
                && stderr.contains(&format!("[{}]", names.join(", ")))
                && stderr.contains(&format!(
                    "is AArch64::{} ({}: `RECONSTRUCTED PairMemory_STP_",
                    unqualified_opcodes[0],
                    trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
                ))
                && stderr.contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)
                && stderr.contains(&format!(
                    "; {}: `A64 memory effect {} 0x",
                    trust_cg_verify::function_verifier::MEMORY_EFFECT_IS_NOT_CREDIT,
                    unqualified_opcodes[0]
                )),
            "an unqualified host must refuse the exact set {unqualified_opcodes:?}, the first \
             row a checker-identity miss: {stderr}"
        );
        assert!(
            !out_path.exists(),
            "uncertified object was published: {stderr}"
        );
        assert!(
            !proofs_dir.exists(),
            "uncertified proof files were published: {stderr}"
        );
        return;
    }
    let names = opcodes
        .iter()
        .map(|name| format!("AArch64::{name}"))
        .collect::<Vec<_>>();
    assert!(
        !output.status.success(),
        "uncredited instructions must not export: {stderr}"
    );
    for opcode in [
        "StpPreIndex",
        "StpRI",
        "LdpRI",
        "LdpPostIndex",
        "LdrRI",
        "StrRI",
    ] {
        assert!(
            !stderr.contains(&format!("AArch64::{opcode}")),
            "bound-memory row {opcode} is uncovered again (its form certificate no longer \
             credits it): {stderr}"
        );
    }
    assert!(
        stderr.contains("proof promotion rejected")
            && stderr.contains("non_verified proof entry opcode_inventory_instruction_0")
            && stderr.contains("emitted opcode inventory found")
            && stderr.contains(&format!("[{}]", names.join(", ")))
            && stderr.contains(&format!(
                "is AArch64::{} ({}: `RECONSTRUCTED Iadd_64 -> {} (real-operand)`",
                opcodes[0],
                trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT,
                opcodes[0]
            )),
        "rejection must name the exact uncovered opcode set {opcodes:?}, the first row \
         refused as its sampled arithmetic obligation: {stderr}"
    );
    assert!(
        !out_path.exists(),
        "uncertified object was published: {stderr}"
    );
    assert!(
        !proofs_dir.exists(),
        "uncertified proof files were published: {stderr}"
    );
}

#[test]
fn cli_emit_proofs_rejects_uncredited_arithmetic_before_publication() {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("module.tmbc");
    let object = dir.path().join("module.o");
    let proofs = dir.path().join("proofs");
    std::fs::write(&input, encode_tmbc(&make_statistical_module()).unwrap()).unwrap();
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["-c", "--target=aarch64-apple-darwin", "-o"])
        .arg(&object)
        .arg("--emit-proofs")
        .arg(&proofs)
        .arg(&input)
        .output()
        .unwrap();
    assert_uncredited_evidence_rejection(&output, &object, &proofs);

    let ordinary = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args(["-c", "--target=aarch64-apple-darwin", "-o"])
        .arg(&object)
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        ordinary.status.success(),
        "ordinary compilation without --emit-proofs is unaffected: {}",
        String::from_utf8_lossy(&ordinary.stderr)
    );
    assert!(object.exists());
    assert!(!proofs.exists());
}

// ---------------------------------------------------------------------------
// Case 1a (Mach-O lane): proof-required AOT emission clears the
// object-authority boundary.
//
// The aarch64 Mach-O production registry now cites the solver-backed
// aarch64_macho_data/call/tlvp_reloc_proofs lanes and the report is built
// under the default-Enforce ENC-9 reparse binding, so a module whose
// relocation kinds are all lane-covered promotes end to end.
//
// The Mach-O promoting cases pass `--target=aarch64-apple-darwin`
// EXPLICITLY: they exercise the Mach-O Certified composition, which is a
// target property, not a host property. With the target implicit they compile
// for the host default, and on an aarch64-Linux host that is the aarch64-ELF
// lane — a different composition, pinned separately by the `b` cases below and
// by the registry-gap control in Case 4c.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_promotes_covered_object_relocations() {
    let dir = scratch_dir("promotes_covered_object_relocations");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_structural_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
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
// The same Mach-O compile rejects with container binding withdrawn and
// succeeds when the binding is present. Relocation formula evidence alone
// does not authorize the object.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_promotes_bound_and_rejects_unbound_object_relocations() {
    let dir = scratch_dir("promotes_bound_rejects_unbound_object_relocations");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_structural_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    // (a) Reparse binding withdrawn: registry rows alone must NOT promote.
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .envs(withdrawn_container_bindings())
        .output()
        .expect("run trust-cg (reparse off)");
    assert_object_authority_rejection_for(
        &output,
        &out_path,
        &proofs_dir,
        "lacks an independent reparse binding",
    );

    // (b) Default (reparse Enforce): the Certified composition promotes.
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg (default)");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bound object relocations must promote under the default Enforce reparse gate. \
         stderr: {stderr}"
    );
    assert!(
        out_path.exists(),
        "promoted compile must publish the object. stderr: {stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// The high-pressure fixture exercises real frame/spill lowering. Its
// pair-memory and LDR/STR spill accesses are credited by their form
// certificates (owner ruling 2026-09-29), so the export gate refuses the
// fixture for its other, uncredited rows only.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_rejects_unmapped_frame_spill_object() {
    let dir = scratch_dir("rejects_unmapped_frame_spill_object");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_frame_spill_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    // The pair and LDR/STR spill rows are credited by their form
    // certificates (owner ruling 2026-09-29); the rows whose only candidate
    // was a registry theorem found by name or a sampled reconstruction
    // (ADD/SUB immediates, MOVZ/MOVN, MADD, ADD) stay uncredited.
    assert_frame_spill_rejection_names_only_uncredited_arithmetic(
        &output,
        &out_path,
        &proofs_dir,
        &["AddRI", "SubRI", "Movz", "Madd", "Movn", "AddRR"],
        UNQUALIFIED_FRAME_SPILL_SET,
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// With container authority also withdrawn, the sampled instruction evidence
// still rejects the frame/spill fixture before publishing any artifact.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_rejects_unmapped_and_unbound_frame_spill_object() {
    let dir = scratch_dir("rejects_unbound_frame_spill_object");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_frame_spill_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .envs(withdrawn_container_bindings())
        .output()
        .expect("run trust-cg");

    assert_frame_spill_rejection_names_only_uncredited_arithmetic(
        &output,
        &out_path,
        &proofs_dir,
        &["AddRI", "SubRI", "Movz", "Madd", "Movn", "AddRR"],
        UNQUALIFIED_FRAME_SPILL_SET,
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// FCMP and CSET name their theorems per instruction, and E0.2 refuses both as
// registry name lookups. Require exactly that evidence limitation for both
// rows; an unrelated failure (or a missing mapping) must not satisfy these
// publication controls.
// ---------------------------------------------------------------------------

fn assert_registry_named_fcmp_rejection(
    output: &std::process::Output,
    out_path: &std::path::Path,
    proofs_dir: &std::path::Path,
) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "registry-named evidence must not export: {stderr}"
    );
    // The refusal names both uncredited rows and quotes the first one's
    // reason: the FCMP's exact NZCV form, found by name and not credited.
    assert!(
        stderr.contains("proof promotion rejected")
            && stderr.contains(
                "emitted opcode inventory found 2 uncovered non-pseudo opcode(s) across 2 \
                 distinct opcode(s) [AArch64::Fcmp, AArch64::CSet]"
            )
            && stderr.contains(
                "is AArch64::Fcmp (no operand-exact evidence: registry name lookup is not \
                 proof credit: query `a64 nzcv fcmp f32 packed:`"
            ),
        "the FCMP and its CSET must both be refused, the FCMP as a registry name \
         lookup: {stderr}"
    );
    assert!(
        !stderr.contains("no proof mapping for opcode"),
        "FCMP/CSET are mapped per instruction: {stderr}"
    );
    assert!(
        !out_path.exists(),
        "uncertified object was published: {stderr}"
    );
    assert!(
        !proofs_dir.exists(),
        "uncertified proof files were published: {stderr}"
    );
}

#[test]
fn cli_emit_proofs_rejects_registry_named_fcmp() {
    let dir = scratch_dir("rejects_registry_named_fcmp");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_fcmp_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    assert_registry_named_fcmp_rejection(&output, &out_path, &proofs_dir);

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// With both instruction and object evidence insufficient, the instruction
// evidence rejection still occurs before any artifact publication.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_rejects_registry_named_fcmp_with_unbound_object() {
    let dir = scratch_dir("rejects_registry_named_fcmp_with_unbound_object");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_fcmp_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    // Withdraw the object binding as well as retaining uncredited instructions.
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .envs(withdrawn_container_bindings())
        .output()
        .expect("run trust-cg");

    assert_registry_named_fcmp_rejection(&output, &out_path, &proofs_dir);

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Proof-file I/O can fail after internal object authority passes. The error
// must prevent publication of the object and preserve the conflicting path.
// ---------------------------------------------------------------------------

#[test]
fn cli_proof_io_failure_prevents_object_publication() {
    let dir = scratch_dir("sidecar_io_failure_fails_loudly");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_structural_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    std::fs::create_dir_all(&proofs_dir).expect("create proofs dir");
    let proof_file_path = proofs_dir.join("covered_elsewhere/covered_elsewhere_instruction_0.cert");
    std::fs::create_dir_all(&proof_file_path).expect("create conflicting proof-file directory");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
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
        proof_file_path.is_dir(),
        "the pre-existing conflict must remain untouched"
    );
    assert!(
        !out_path.exists(),
        "proof-file I/O failed, so the object must not be published"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// The Mach-O object gate runs BEFORE sidecar I/O. The
// serializer's own I/O failure behavior is covered in `emit_proofs` unit
// tests; the CLI must never write an object merely because a later sidecar
// path is also invalid.
// ---------------------------------------------------------------------------

#[test]
fn cli_object_authority_precedes_sidecar_io() {
    let dir = scratch_dir("object_authority_precedes_sidecar_io");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_structural_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    std::fs::create_dir_all(&proofs_dir).expect("create proofs dir");
    let proof_file_path = proofs_dir.join("covered_elsewhere/covered_elsewhere_instruction_0.cert");
    std::fs::create_dir_all(&proof_file_path).expect("create conflicting proof-file directory");

    // Reparse binding withdrawn so the object gate rejects; the sidecar
    // conflict sits later on the pipeline and must never be reached.
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("--target=aarch64-apple-darwin")
        .arg("-o")
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .envs(withdrawn_container_bindings())
        .output()
        .expect("run trust-cg");

    assert_object_authority_rejection_for(
        &output,
        &out_path,
        &proofs_dir,
        "lacks an independent reparse binding",
    );
    assert!(
        proof_file_path.is_dir(),
        "the pre-existing conflict must remain untouched when object promotion fails first"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// ELF identity has the exact source-bound 16-byte FP/LR leaf envelope. The
// CLI must establish complete source/body correspondence AND independently
// replay its frame theorem before the object gate and sidecar publication.
// Calling the public sidecar constructor with arbitrary byte hashes would
// not exercise this authority. Wider heap/spill refusals remain below, and
// source_bound_frame's changed-source/body controls guard the producer itself.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_aarch64_elf_requires_replayed_frame_and_object_binding() {
    use trust_cg_verify::lrat_cert::sha256_hex;
    use trust_cg_verify::proof_certificate::LoweringCertificate;
    use trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME;

    let dir = scratch_dir("aarch64_elf_requires_replayed_frame_and_object_binding");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    // A database theorem or old verdict is not a live independent replay.
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .args([
            "-c",
            "--target=aarch64-unknown-linux-gnu",
            "--opt-level=0",
            "-o",
        ])
        .arg(&out_path)
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .env("TCG_REFINE_SOLVER", "0")
        .env("TCG_NO_VERDICT_DB", "1")
        .env_remove("TCG_NO_ELF_REPARSE")
        .output()
        .expect("run trust-cg with independent replay withdrawn");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "unreplayed frame exported: {stderr}"
    );
    assert!(
        stderr.contains("proof promotion rejected")
            && stderr.contains("source-bound frame needs independently replayed proof"),
        "must refuse the actual replay deficit: {stderr}"
    );
    assert!(!out_path.exists());
    assert!(!proofs_dir.exists());

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg("--target=aarch64-unknown-linux-gnu")
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .env("TCG_REFINE_SOLVER", "1")
        .env("TCG_NO_VERDICT_DB", "1")
        .env("TCG_NO_ELF_REPARSE", "1")
        .output()
        .expect("run trust-cg with ELF reparse disabled");

    assert_object_authority_rejection_for(
        &output,
        &out_path,
        &proofs_dir,
        "lacks an independent reparse binding",
    );

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg("--target=aarch64-unknown-linux-gnu")
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .env("TCG_REFINE_SOLVER", "1")
        .env("TCG_NO_VERDICT_DB", "1")
        .env_remove("TCG_NO_ELF_REPARSE")
        .output()
        .expect("run trust-cg with default-Enforce ELF reparse");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bound identity must independently replay and export, not silently refuse: {stderr}"
    );
    let object = std::fs::read(&out_path).expect("published ELF object");
    assert!(object.starts_with(b"\x7fELF"));
    assert_eq!(std::fs::read(&tmbc_path).unwrap(), tmbc);
    let audits: Vec<serde_json::Value> = find_files_with_suffix(&proofs_dir, ".cert")
        .into_iter()
        .map(|path| serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap())
        .collect();
    assert!(!audits.is_empty());
    assert!(audits.iter().all(|row| row["verified"] == true));
    assert!(
        audits
            .iter()
            .any(|row| row["proof_name"] == FRAME_OBLIGATION_NAME
                && row["function"] == "_identity"
                && row["strength"] == "Formal")
    );
    assert!(
        audits
            .iter()
            .any(|row| row["category"] == "relocation_inventory")
    );
    assert_eq!(find_files_with_suffix(&proofs_dir, ".smt2").len(), 1);

    let lowering_paths = find_files_with_suffix(&proofs_dir, ".lowering.json");
    let export_paths = find_files_with_suffix(&proofs_dir, ".trust-proof-cert.json");
    assert_eq!(lowering_paths.len(), 1);
    assert_eq!(export_paths.len(), 1);
    let lowering_text = std::fs::read_to_string(&lowering_paths[0]).unwrap();
    let lowering = LoweringCertificate::from_json(&lowering_text).unwrap();
    let value: serde_json::Value = serde_json::from_str(&lowering_text).unwrap();
    assert_eq!(value["schema"], "trust-cg.lowering_certificate.v1");
    assert_eq!(value["function"], "_identity");
    assert_eq!(value["target"], "aarch64-unknown-linux-gnu");
    assert_eq!(value["result"], "verified");
    assert_eq!(value["overall_strength"]["kind"], "smt_unsat");
    assert_eq!(lowering.trust_ir_hash, sha256_hex(&tmbc));
    assert_eq!(lowering.machine_code_hash, sha256_hex(&object));
    // The frame theorem, then the twelve memory-effect parts of the two frame
    // records: the records' credit needed both, so the sidecar carries both.
    let parts = trust_cg_verify::aarch64_memory_source_binding::frame_record_part_obligations();
    assert_eq!(lowering.rule_proofs.len(), 1 + parts.len());
    let rule = &value["rule_proofs"][0];
    assert_eq!(rule["rule_name"], FRAME_OBLIGATION_NAME);
    assert_eq!(rule["check_kind"], "regalloc");
    for (index, rule) in value["rule_proofs"].as_array().unwrap().iter().enumerate() {
        if index > 0 {
            assert_eq!(rule["rule_name"], parts[index - 1].name.as_str());
        }
        assert_eq!(rule["result"]["status"], "proved");
        assert_eq!(rule["result"]["strength"]["kind"], "smt_unsat");
        assert_eq!(rule["result"]["solver"], "ay_cli");
    }
    // The formal sidecar names the exact AY every obligation was bound to: the
    // one the identity rule admits (this test's build toolchain AY, by the
    // SHA-256 recorded when trust-cg-verify was built).
    let recorded = trust_cg_verify::ay_identity::recorded_toolchain_ay_identity()
        .expect("a formal sidecar implies an admitted AY");
    let ay = value["ay"]
        .as_str()
        .expect("a formal lowering certificate names the AY that produced it");
    assert!(
        ay.contains(recorded.sha256()) && ay.contains("route=toolchain-pinned-ay"),
        "{ay}"
    );
    let exported: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&export_paths[0]).unwrap()).unwrap();
    assert_eq!(exported, lowering.to_trust_proof_cert_value().unwrap());
    assert_eq!(exported["status"], "Trusted");
    assert_eq!(exported["signature"], serde_json::Value::Null);

    // `machine_code_hash` binds the whole object, so its `.text` is the
    // certified function. On aarch64 Linux that object must also link with the
    // host C compiler into an executable carrying the same words at the
    // symbol's link-time address, and returning each argument when run. This
    // is a test-side byte comparison of the linked image, not a certificate
    // over it; the .eh_frame PREL32's linked effect is not checked here
    // (scripts/check_aarch64_aot_arithmetic.py checks it for the arithmetic
    // leaves).
    let text = certified_function_text(&object, "_identity");
    if cfg!(all(target_os = "linux", target_arch = "aarch64")) {
        link_and_run_identity(&dir, &out_path, &text);
    }

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Pin the Mach-O object-authority control using only its exact reparse knob.
// The target is explicit, so this test exercises the same lane on every host.
// ---------------------------------------------------------------------------

#[test]
fn cli_emit_proofs_aarch64_macho_requires_reparse_binding() {
    let dir = scratch_dir("aarch64_macho_requires_reparse_binding");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");
    let proofs_dir = dir.join("proofs");

    let module = make_structural_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg("--target=aarch64-apple-darwin")
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .env("TCG_NO_MACHO_REPARSE", "1")
        .output()
        .expect("run trust-cg with Mach-O reparse disabled");

    assert_object_authority_rejection_for(
        &output,
        &out_path,
        &proofs_dir,
        "lacks an independent reparse binding",
    );

    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg("--target=aarch64-apple-darwin")
        .arg("--opt-level=0")
        .arg(format!("--emit-proofs={}", proofs_dir.display()))
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg with default-Enforce Mach-O reparse");

    assert_object_promotes(&output, &out_path, &proofs_dir);

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
        .arg("--permit-unlicensed")
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
        .arg("--permit-unlicensed")
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

#[path = "common/scratch.rs"]
mod scratch;
