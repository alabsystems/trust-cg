// guard_kernel_gate_riscv_compile_e2e.rs — ITEM 2: proof-driven bounds-check
// elimination through the PRODUCTION `Compiler::compile` path on RISC-V.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! ITEM 2 (RISC-V production wiring) — the integration proof that fail-closed
//! bounds-check handling flows all the way through `Compiler::compile` for
//! `Target::Riscv64`, exercising the minimal trust_ir → `RiscVISelFunction`
//! selector + `run_riscv_guard_kernel_gate` (with its fail-closed re-check) + the
//! existing S5 carrier/pass/expansion + RISC-V emission.
//!
//! Unlike `guard_kernel_gate_riscv_e2e` (which hand-builds the ISel function from
//! the adapter's producer opcode), this test drives the WHOLE compiler: it builds
//! a trust-ir module with a proven `array[index]` access and calls
//! `Compiler::compile`, asserting:
//!
//! * Default (gate ON): report-only `InBounds` metadata does not authorize elimination;
//!   the emitted RISC-V object retains its `EBREAK` trap.
//! * Gate OFF (`TRUST_CG_GUARD_KERNEL_GATE=0`): the carrier is KEPT and expands to
//!   a real `BGEU + EBREAK` runtime check in the emitted object.
//! * STRICT RESTRICTION: without independently replayed authority, gate ON and OFF
//!   both preserve runtime safety.
//! * FAIL-CLOSED: a function shape the minimal selector cannot lower soundly is
//!   rejected with a clear error, never miscompiled.
//!
//! `InBounds` is report/runtime-carrier metadata, not replayed proof authority. A
//! kept carrier compiles to a real BGEU+EBREAK check.

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const EBREAK_WORD: u32 = 0x0010_0073;
const ARRAY_LEN: u64 = 8;

/// Build a trust-ir module whose single function does `array[index]` on an
/// `Array(I64, ARRAY_LEN)` parameter carrying `InBounds`, returning the element.
/// This is exactly the guard-bearing shape the adapter lowers to a
/// `GuardBoundsCheck` producer without synthesizing proof authority.
fn build_proven_extract_module() -> Module {
    let mut module = Module::new("guard_kernel_gate_riscv_compile_e2e");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "proven_extract", ft, BlockId::new(0));
    let node = InstrNode::new(Inst::ExtractElement {
        ty: Ty::I64,
        array: ValueId::new(0),
        index: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::InBounds);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            node,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// PHASE 4: a trust-ir module where `caller(x)` makes a DIRECT cross-function
/// call to a DEFINED `callee(x)` in the SAME module. The RISC-V production path
/// now lays both functions into one `.text` and resolves the call PC-relatively
/// at module-emit time (AUIPC+JALR pcrel pair) — no relocation, no linker.
fn build_intra_module_call_module() -> Module {
    let mut module = Module::new("riscv_intra_module_call");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    // A defined callee.
    let callee_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut callee = TrustIrFunction::new(FuncId::new(1), "callee", callee_ft, BlockId::new(0));
    callee.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    module.add_function(callee);

    let mut func = TrustIrFunction::new(FuncId::new(0), "caller", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// PHASE 4: a trust-ir module where `caller(x)` calls an EXTERNAL function `ext`
/// that is DECLARED (no body) but not defined in this module. The RISC-V
/// production path must record an `R_RISCV_CALL` relocation in `.rela.text`
/// against an undefined `ext` symbol rather than failing — leaving the AUIPC+JALR
/// placeholder for a real linker to patch.
fn build_external_call_module() -> Module {
    let mut module = Module::new("riscv_external_call");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    // An EXTERNAL (declaration-only, no blocks) callee — not defined here.
    let ext_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let ext = TrustIrFunction::new(FuncId::new(1), "ext", ext_ft, BlockId::new(0));
    // No blocks: a declaration. The translator emits no body for it, so it is
    // not a defined module function; the call below becomes an external symbol.
    module.add_function(ext);

    let mut func = TrustIrFunction::new(FuncId::new(0), "caller", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

fn count_words(bytes: &[u8], target: u32) -> usize {
    bytes
        .chunks_exact(4)
        .filter(|w| *w == target.to_le_bytes())
        .count()
}

fn compile_riscv(module: &Module) -> trust_cg_codegen::compiler::CompilationResult {
    let cfg = CompilerConfig {
        target: Target::Riscv64,
        parallel: false,
        ..CompilerConfig::default()
    };
    Compiler::new(cfg).compile(module).expect("RISC-V compile")
}

/// Compile without the shared LIR inliner. Cross-call tests exercise the call
/// materialization itself, so their deliberately tiny callee must remain a call.
fn compile_riscv_o0(module: &Module) -> trust_cg_codegen::compiler::CompilationResult {
    let cfg = CompilerConfig {
        target: Target::Riscv64,
        opt_level: OptLevel::O0,
        parallel: false,
        ..CompilerConfig::default()
    };
    Compiler::new(cfg)
        .compile(module)
        .expect("RISC-V O0 compile")
}

#[test]
fn riscv_compile_default_gate_on_keeps_report_only_inbounds_check() {
    // The kernel gate is the production default. Report-only InBounds metadata must
    // not remove the runtime check.
    let module = build_proven_extract_module();
    let result = compile_riscv(&module);
    assert!(
        result.metrics.code_size_bytes > 0,
        "the function must actually compile to code"
    );
    assert!(
        count_words(&result.object_code, EBREAK_WORD) >= 1,
        "DEFAULT (gate ON): the bounds-check trap must survive without replayed authority"
    );
}

#[test]
fn riscv_compile_gate_off_keeps_bounds_check_with_real_trap() {
    // With the gate explicitly OFF, the carrier is KEPT and expands to a real
    // BGEU + EBREAK runtime check. Run in a child process so the env var cannot
    // race other tests in the same binary.
    let exe = std::env::current_exe().expect("test exe");
    let output = std::process::Command::new(exe)
        .arg("--exact")
        .arg("riscv_compile_gate_off_child")
        .arg("--nocapture")
        .env("TRUST_CG_GUARD_KERNEL_GATE", "0")
        .env("TRUST_CG_RISCV_GATE_OFF_CHILD", "1")
        .output()
        .expect("spawn child test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "child test failed:\nstdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("GATE_OFF_EBREAK_COUNT=1"),
        "child must report exactly one EBREAK with the gate off; stdout:\n{stdout}"
    );
}

#[test]
fn riscv_compile_gate_off_child() {
    if !matches!(
        std::env::var("TRUST_CG_RISCV_GATE_OFF_CHILD").as_deref(),
        Ok("1")
    ) {
        eprintln!(
            "child-process helper not requested; \
             riscv_compile_gate_off_keeps_bounds_check_with_real_trap runs it"
        );
        return;
    }

    let module = build_proven_extract_module();
    let result = compile_riscv(&module);
    let ebreaks = count_words(&result.object_code, EBREAK_WORD);
    println!("GATE_OFF_EBREAK_COUNT={ebreaks}");
    assert!(
        ebreaks >= 1,
        "gate OFF: a kept carrier must expand to an EBREAK bounds-check trap"
    );
}

// ---------------------------------------------------------------------------
// ELF section/relocation parsing helpers for the phase-4 cross-call tests.
// ---------------------------------------------------------------------------

fn read_u16(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}
fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}
fn read_u64(bytes: &[u8], offset: usize) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&bytes[offset..offset + 8]);
    u64::from_le_bytes(b)
}

const ELF64_SHDR_SIZE: usize = 64;
const ELF64_RELA_SIZE: usize = 24;
const ELF64_SYM_SIZE: usize = 24;

/// Return `(name -> (sh_type, sh_offset, sh_size, sh_link, sh_info, sh_entsize))`
/// for every section, parsed from the ELF section header table.
fn section_table(bytes: &[u8]) -> Vec<(String, u32, u64, u64, u32, u32, u64)> {
    let sh_offset = read_u64(bytes, 40) as usize;
    let e_shnum = read_u16(bytes, 60) as usize;
    let e_shstrndx = read_u16(bytes, 62) as usize;
    let shstr_shdr = sh_offset + e_shstrndx * ELF64_SHDR_SIZE;
    let shstr_off = read_u64(bytes, shstr_shdr + 24) as usize;
    let mut out = Vec::new();
    for i in 0..e_shnum {
        let sh = sh_offset + i * ELF64_SHDR_SIZE;
        let name_idx = read_u32(bytes, sh) as usize;
        let ns = shstr_off + name_idx;
        let ne = bytes[ns..]
            .iter()
            .position(|&b| b == 0)
            .map(|p| ns + p)
            .unwrap_or(ns);
        let name = std::str::from_utf8(&bytes[ns..ne])
            .unwrap_or("")
            .to_string();
        let sh_type = read_u32(bytes, sh + 4);
        let sh_link = read_u32(bytes, sh + 40);
        let sh_info = read_u32(bytes, sh + 44);
        let sh_entsize = read_u64(bytes, sh + 56);
        let off = read_u64(bytes, sh + 24);
        let size = read_u64(bytes, sh + 32);
        out.push((name, sh_type, off, size, sh_link, sh_info, sh_entsize));
    }
    out
}

/// Read the name of symbol `index` from `.symtab` (resolving through `.strtab`).
fn symbol_name(bytes: &[u8], sym_index: u32) -> String {
    let secs = section_table(bytes);
    let (_, _, symtab_off, _symtab_size, symtab_link, _, _) = secs
        .iter()
        .find(|s| s.0 == ".symtab")
        .cloned()
        .expect(".symtab present");
    // sh_link of .symtab -> .strtab section index.
    let strtab = &secs[symtab_link as usize];
    let strtab_off = strtab.2 as usize;
    let sym_off = symtab_off as usize + sym_index as usize * ELF64_SYM_SIZE;
    let name_idx = read_u32(bytes, sym_off) as usize;
    let ns = strtab_off + name_idx;
    let ne = bytes[ns..]
        .iter()
        .position(|&b| b == 0)
        .map(|p| ns + p)
        .unwrap_or(ns);
    std::str::from_utf8(&bytes[ns..ne])
        .unwrap_or("")
        .to_string()
}

/// Return all `.rela.text` entries as `(r_offset, sym_index, reloc_type, addend)`.
fn rela_text_entries(bytes: &[u8]) -> Vec<(u64, u32, u32, i64)> {
    let secs = section_table(bytes);
    let Some((_, _, off, size, _, _, _)) = secs.iter().find(|s| s.0 == ".rela.text").cloned()
    else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let n = (size as usize) / ELF64_RELA_SIZE;
    for i in 0..n {
        let base = off as usize + i * ELF64_RELA_SIZE;
        let r_offset = read_u64(bytes, base);
        let r_info = read_u64(bytes, base + 8);
        let addend = read_u64(bytes, base + 16) as i64;
        let sym = (r_info >> 32) as u32;
        let ty = (r_info & 0xFFFF_FFFF) as u32;
        out.push((r_offset, sym, ty, addend));
    }
    out
}

/// PHASE 4: a DIRECT cross-function call to a DEFINED callee in the same module
/// now COMPILES (it used to be fail-closed-rejected). This runs at O0 so the
/// shared LIR inliner cannot legitimately erase the tiny identity call before
/// the backend sees it. The two functions land in
/// one `.text`, the call resolves PC-relatively at module-emit time, and — being
/// intra-object — the object carries NO `.rela.text` (no relocation needed).
#[test]
fn riscv_compile_intra_module_cross_call_resolves_without_relocation() {
    let module = build_intra_module_call_module();
    let result = compile_riscv_o0(&module);
    assert_eq!(
        result.metrics.function_count, 2,
        "both caller and callee must be emitted into the module"
    );
    assert!(
        result.metrics.code_size_bytes > 0,
        "the module must actually compile to code"
    );
    // The object must contain BOTH symbols and the resolved AUIPC+JALR call.
    let bytes = &result.object_code;
    let secs = section_table(bytes);
    assert!(secs.iter().any(|s| s.0 == ".text"), ".text present");
    // Intra-object call => no relocation section is emitted.
    assert!(
        rela_text_entries(bytes).is_empty(),
        "an intra-object cross-function call needs NO relocation"
    );
    // The AUIPC (opcode 0x17) for the call must be present, with a NON-zero
    // resolved hi20 OR a non-zero JALR lo12 (a wrong/zero target is forbidden).
    // Find the AUIPC ra (rd=1) + following JALR ra (rd=1) pcrel pair and assert
    // its reconstructed target lands inside .text (i.e. it was actually resolved).
    let (text_off, text_size) = find_riscv_section(bytes, ".text");
    let text = &bytes[text_off as usize..(text_off + text_size) as usize];
    let mut resolved_call = false;
    let mut i = 0;
    while i + 8 <= text.len() {
        let w = u32::from_le_bytes([text[i], text[i + 1], text[i + 2], text[i + 3]]);
        if (w & 0x7F) == 0x17 && ((w >> 7) & 0x1F) == 1 {
            // AUIPC ra: scan forward for the matching JALR ra, ra.
            let mut j = i + 4;
            while j + 4 <= text.len() {
                let w2 = u32::from_le_bytes([text[j], text[j + 1], text[j + 2], text[j + 3]]);
                if (w2 & 0x7F) == 0x67 && ((w2 >> 7) & 0x1F) == 1 && ((w2 >> 15) & 0x1F) == 1 {
                    let hi20 = ((w as i32) >> 12) as i64;
                    let lo12 = ((w2 as i32) >> 20) as i64;
                    let target = i as i64 + (hi20 << 12) + lo12;
                    assert!(
                        target >= 0 && (target as usize) < text.len(),
                        "resolved call target {target} must land inside .text [0,{})",
                        text.len()
                    );
                    resolved_call = true;
                    break;
                }
                j += 4;
            }
            break;
        }
        i += 4;
    }
    assert!(resolved_call, "must find a resolved AUIPC+JALR call pair");
}

/// Helper mirroring `find_elf_section` but for this test (returns (off,size)).
fn find_riscv_section(bytes: &[u8], name: &str) -> (u64, u64) {
    let secs = section_table(bytes);
    let s = secs.iter().find(|s| s.0 == name).expect("section present");
    (s.2, s.3)
}

/// PHASE 4: a DIRECT call to an EXTERNAL (declaration-only) symbol must NOT fail
/// closed — it records a single `R_RISCV_CALL` relocation in `.rela.text` against
/// the undefined `ext` symbol, leaving the AUIPC+JALR placeholder for a real
/// linker to patch. This proves the external-relocation path (requirement 3).
#[test]
fn riscv_compile_external_cross_call_emits_r_riscv_call_relocation() {
    use trust_cg_codegen::elf::constants::R_RISCV_CALL;

    let module = build_external_call_module();
    let result = compile_riscv(&module);
    // Only `caller` is a DEFINED function; `ext` is a declaration.
    assert_eq!(
        result.metrics.function_count, 1,
        "only the defined caller is emitted; ext is an external declaration"
    );
    let bytes = &result.object_code;
    let relas = rela_text_entries(bytes);
    assert_eq!(
        relas.len(),
        1,
        "exactly one R_RISCV_CALL relocation for the external call, got {relas:?}"
    );
    let (r_offset, sym, ty, addend) = relas[0];
    assert_eq!(
        ty, R_RISCV_CALL,
        "relocation type must be R_RISCV_CALL (18)"
    );
    assert_eq!(addend, 0, "R_RISCV_CALL addend is 0 (RELA)");
    assert_eq!(
        symbol_name(bytes, sym),
        "ext",
        "relocation must target the external `ext` symbol"
    );
    // The relocation offset must point at an AUIPC (opcode 0x17) in .text.
    let (text_off, _text_size) = find_riscv_section(bytes, ".text");
    let i = text_off as usize + r_offset as usize;
    let w = read_u32(bytes, i);
    assert_eq!(
        w & 0x7F,
        0x17,
        "R_RISCV_CALL must apply at the AUIPC of the call pair"
    );
    // psABI REQUIREMENT: R_RISCV_CALL patches a CONTIGUOUS AUIPC+JALR pair — the
    // linker writes the hi20 at r_offset and the lo12 at r_offset+4. The
    // instruction at r_offset+4 MUST therefore be the JALR (opcode 0x67), not an
    // argument-setup move. (Regression guard: an earlier lowering placed the arg
    // ADDIs between the AUIPC and JALR, which a real linker would have corrupted.)
    let w_next = read_u32(bytes, i + 4);
    assert_eq!(
        w_next & 0x7F,
        0x67,
        "the instruction at r_offset+4 must be the JALR (contiguous AUIPC+JALR pair); \
         arg-setup moves must precede the AUIPC"
    );
}
