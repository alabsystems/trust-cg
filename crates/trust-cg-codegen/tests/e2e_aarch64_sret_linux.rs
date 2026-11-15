// Copyright 2026 Andrew Yates | Apache-2.0
//! ELF and Linux-native twin of `e2e_aarch64_sret.rs`: hidden-result (`sret`)
//! returns through X8 in both directions, through function pointers and
//! variadic callees, on aarch64-unknown-linux-gnu (ledger L01-P5).
//!
//! Host-neutral rows compile the shared corpus (`common/sret_corpus.rs`) to
//! ELF at O0-O3 and check, with an independent ELF64 reader and the
//! `trust-cg-lift` decoder, that every corpus function is a defined global
//! `STT_FUNC` of non-zero size in an executable section and every C callee it
//! imports an undefined global (what the Linux link of the C driver
//! resolves), and that the static-provenance edge (`CallIndirect` through a
//! `Const FnDef` of the pre-lowered declaration `c_big_attr`) stays an
//! indirect call: X8 written before a `BLR`, no `BL` in the caller and no
//! `R_AARCH64_CALL26`/`JUMP26` against the declaration. Byte mutations show
//! each check can fail, and the real compiler's refusals (non-leading hidden
//! parameter, hidden parameter beside a result, disagreeing indirect edge,
//! indirect call over a variadic signature, variadic definition) are asserted
//! by name. The Linux-only rows link the objects with `cc` against the shared
//! C driver and execute them at O0-O3 (the Linux floor runs them).
//!
//! Base AAPCS64 (Arm IHI 0055, rule numbers from the current Arm `abi-aa`
//! text; the lowering's `abi.rs` comments still use an older revision's
//! numbering) differs from the DarwinPCS the Darwin test runs under exactly
//! where this corpus puts arguments on the stack, so the Darwin expectations
//! are not copied:
//!
//! * §6.8.2 stage C rule C.16: a stack-passed argument smaller than 8 bytes
//!   has its size set to 8 bytes (C.14 first rounds the NSAA up to the larger
//!   of 8 and the natural alignment), so the two `int32_t` arguments sit at
//!   `[sp, #16]` and `[sp, #24]` after the stack `int64_t` and `double`
//!   (DarwinPCS packs them at `[sp, #16]` and `[sp, #20]`);
//! * the remaining bits of that 8-byte slot are unspecified (C.16), as are
//!   the unused high bits of a narrow register argument (C.9, "copied to the
//!   least significant bits"), so a conforming CALLEE may use only the
//!   argument's own width (DarwinPCS makes the caller extend instead). The
//!   Linux-only wide-slot row calls the CG callees through a prototype whose
//!   two narrow arguments are `int64_t` with poisoned high halves, which
//!   AAPCS64 lays out at exactly the same registers and slots. What that row
//!   shows is placement and low-bit independence: the CG callees' `I32`
//!   add/sub lanes are unaffected by the poisoned high halves. Because the
//!   corpus uses `n0`/`n1` only in 32-bit add/sub, whose low 32 bits do not
//!   depend on a slot's high 32 bits, the row does NOT distinguish a callee
//!   that reads the full 8-byte slot from one that reads its low 32 bits (a
//!   C callee declared with `int64_t` narrows and 64-bit arithmetic passes
//!   it too), so callee-side narrow handling is not evidenced here; the
//!   register-narrow case is evidenced by `e2e_aarch64_bool_abi_linux`;
//! * §6.8.2 applies unchanged to a variadic call: anonymous arguments take
//!   the remaining X and V registers before the stack (DarwinPCS puts every
//!   anonymous argument on the stack), so the variadic rows exercise a
//!   register-resident anonymous tail against glibc's `va_arg`.
//!
//! Execution and object-structure evidence, not proof of the hidden-result
//! convention.

#[path = "common/sret_corpus.rs"]
mod corpus;

#[path = "common/admission_expect.rs"]
mod admission_expect;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lift::disasm::aarch64::{Instruction, decode};
use trust_ir::{Module, Ty};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const ALL_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHF_EXECINSTR: u64 = 4;
const STB_GLOBAL: u8 = 1;
const STT_FUNC: u8 = 2;
const R_AARCH64_JUMP26: u32 = 282;
const R_AARCH64_CALL26: u32 = 283;
const X8: u8 = 8;
/// `BranchReg::opc` of `BLR` (0 is `BR`, 2 is `RET`).
const BLR_OPC: u8 = 1;
const AARCH64_NOP: u32 = 0xd503_201f;
/// `BL #0`: the shape a devirtualized, relocated call would take.
const AARCH64_BL_0: u32 = 0x9400_0000;

fn compile(module: &Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).expect("Linux triple parses"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error} ({error:?})"))
}

fn compile_ok(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    let object = compile(module, opt_level)
        .unwrap_or_else(|error| panic!("sret module must compile at {opt_level:?}: {error}"));
    assert_eq!(
        object.get(..4),
        Some(b"\x7fELF".as_slice()),
        "the Linux target must emit an ELF object"
    );
    object
}

fn compile_error(module: &Module, opt_level: OptLevel) -> String {
    compile(module, opt_level)
        .map(|_| ())
        .expect_err("the module must be refused")
}

/// `module` is refused at `opt_level`: by trust-ir's own first admission
/// finding when trust-ir refuses it (WS7.3: ingestion admission runs before
/// any backend arm), else by the backend's message naming every `needle`.
fn assert_refused(module: &Module, opt_level: OptLevel, needles: &[&str]) {
    let message = compile_error(module, opt_level);
    match admission_expect::names_first_finding(module, &message, &permit_unlicensed()) {
        Some(named) => assert!(
            named,
            "{opt_level:?}: trust-ir's finding {:?} is not named in {message}",
            admission_expect::first_finding(module, &permit_unlicensed())
        ),
        None => assert!(
            needles.iter().all(|needle| message.contains(needle)),
            "{opt_level:?}: {message}"
        ),
    }
}

fn bytes<const N: usize>(object: &[u8], offset: usize) -> Result<[u8; N], String> {
    object
        .get(offset..offset + N)
        .and_then(|slice| slice.try_into().ok())
        .ok_or_else(|| format!("read of {N} bytes at {offset:#x} is out of bounds"))
}

fn u16_at(object: &[u8], offset: usize) -> Result<u16, String> {
    bytes(object, offset).map(u16::from_le_bytes)
}

fn u32_at(object: &[u8], offset: usize) -> Result<u32, String> {
    bytes(object, offset).map(u32::from_le_bytes)
}

fn u64_at(object: &[u8], offset: usize) -> Result<u64, String> {
    bytes(object, offset).map(u64::from_le_bytes)
}

fn c_string(object: &[u8], offset: usize) -> Result<String, String> {
    let tail = object
        .get(offset..)
        .ok_or_else(|| format!("string at {offset:#x} is out of bounds"))?;
    let end = tail
        .iter()
        .position(|byte| *byte == 0)
        .ok_or_else(|| format!("string at {offset:#x} is unterminated"))?;
    String::from_utf8(tail[..end].to_vec()).map_err(|error| error.to_string())
}

struct Section {
    kind: u32,
    flags: u64,
    offset: usize,
    size: usize,
    link: usize,
    info: usize,
}

struct Symbol {
    name: String,
    binding: u8,
    kind: u8,
    section_index: usize,
    /// Offset inside its section (a relocatable object).
    value: usize,
    size: u64,
    /// File offset of the 24-byte symbol record.
    record: usize,
}

/// A relocation applied to an executable section.
struct TextRelocation {
    symbol: String,
    kind: u32,
    /// File offsets of the relocation record and the relocated instruction.
    record: usize,
    instruction: usize,
}

struct Elf {
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
    relocations: Vec<TextRelocation>,
}

/// Independent System V ELF64 little-endian relocatable-object reader.
fn parse_elf(object: &[u8]) -> Result<Elf, String> {
    if object.get(..6) != Some(b"\x7fELF\x02\x01".as_slice()) {
        return Err("not an ELF64 little-endian object".into());
    }
    if u16_at(object, 16)? != 1 || u16_at(object, 18)? != 183 {
        return Err("not an AArch64 relocatable object".into());
    }
    let (shoff, shentsize, shnum) = (
        u64_at(object, 0x28)? as usize,
        u16_at(object, 0x3a)? as usize,
        u16_at(object, 0x3c)? as usize,
    );
    if shentsize != 64 {
        return Err(format!("section header size {shentsize}"));
    }
    let sections = (0..shnum)
        .map(|index| {
            let header = shoff + index * shentsize;
            Ok(Section {
                kind: u32_at(object, header + 4)?,
                flags: u64_at(object, header + 8)?,
                offset: u64_at(object, header + 24)? as usize,
                size: u64_at(object, header + 32)? as usize,
                link: u32_at(object, header + 40)? as usize,
                info: u32_at(object, header + 44)? as usize,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let symtab = sections
        .iter()
        .find(|section| section.kind == SHT_SYMTAB)
        .ok_or("no symbol table")?;
    let strtab = sections.get(symtab.link).ok_or("strtab out of range")?;
    let symbols = (0..symtab.size / 24)
        .map(|entry| {
            let record = symtab.offset + entry * 24;
            let info = bytes::<1>(object, record + 4)?[0];
            Ok(Symbol {
                name: c_string(object, strtab.offset + u32_at(object, record)? as usize)?,
                binding: info >> 4,
                kind: info & 0xf,
                section_index: u16_at(object, record + 6)? as usize,
                value: u64_at(object, record + 8)? as usize,
                size: u64_at(object, record + 16)?,
                record,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut relocations = Vec::new();
    for rela in sections.iter().filter(|section| section.kind == SHT_RELA) {
        let target = sections.get(rela.info).ok_or("rela target out of range")?;
        if target.flags & SHF_EXECINSTR == 0 {
            continue;
        }
        let linked = sections.get(rela.link).ok_or("rela symtab out of range")?;
        if linked.kind != SHT_SYMTAB {
            return Err("rela link is not a symbol table".into());
        }
        let linked_strtab = sections.get(linked.link).ok_or("strtab out of range")?;
        for entry in 0..rela.size / 24 {
            let record = rela.offset + entry * 24;
            let offset = u64_at(object, record)? as usize;
            let info = u64_at(object, record + 8)?;
            let symbol = linked.offset + (info >> 32) as usize * 24;
            if offset + 4 > target.size {
                return Err(format!("relocation offset {offset:#x} outside its section"));
            }
            relocations.push(TextRelocation {
                symbol: c_string(
                    object,
                    linked_strtab.offset + u32_at(object, symbol)? as usize,
                )?,
                kind: info as u32,
                record,
                instruction: target.offset + offset,
            });
        }
    }
    Ok(Elf {
        sections,
        symbols,
        relocations,
    })
}

impl Elf {
    fn symbol(&self, name: &str) -> Result<&Symbol, String> {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .ok_or_else(|| format!("{name} has no symbol"))
    }

    /// The instruction words of the defined function `name`, each with its
    /// file offset.
    fn function_words(&self, object: &[u8], name: &str) -> Result<Vec<(usize, u32)>, String> {
        let symbol = self.symbol(name)?;
        if symbol.section_index == 0 {
            return Err(format!("{name} is undefined"));
        }
        let section = self
            .sections
            .get(symbol.section_index)
            .ok_or("symbol section out of range")?;
        if symbol.size == 0 || symbol.size % 4 != 0 {
            return Err(format!("{name} has size {}", symbol.size));
        }
        let start = section.offset + symbol.value;
        (0..symbol.size as usize / 4)
            .map(|index| {
                let offset = start + index * 4;
                Ok((offset, u32_at(object, offset)?))
            })
            .collect()
    }
}

/// Every function in `defined` is a defined global `STT_FUNC` of non-zero
/// size in an executable section, and every C callee in `imports` is an
/// undefined global, so the link of the C driver resolves both directions.
fn corpus_symbols_resolve(object: &[u8], defined: &[&str], imports: &[&str]) -> Result<(), String> {
    let elf = parse_elf(object)?;
    for name in defined {
        let symbol = elf.symbol(name)?;
        if symbol.binding != STB_GLOBAL || symbol.kind != STT_FUNC || symbol.section_index == 0 {
            return Err(format!("{name} is not a defined global function"));
        }
        if symbol.size == 0 {
            return Err(format!("{name} has size 0"));
        }
        let section = elf
            .sections
            .get(symbol.section_index)
            .ok_or("symbol section out of range")?;
        if section.flags & SHF_EXECINSTR == 0 {
            return Err(format!("{name} is not in an executable section"));
        }
    }
    for name in imports {
        let symbol = elf.symbol(name)?;
        if symbol.binding != STB_GLOBAL || symbol.section_index != 0 {
            return Err(format!("{name} is not an undefined global"));
        }
    }
    Ok(())
}

/// True when `inst` writes the general register X8 (or W8): the indirect
/// result location register (AAPCS64 §6.9) being staged for the call.
fn writes_x8(inst: &Instruction) -> bool {
    match inst {
        Instruction::AddSubShiftedReg(i) => i.rd == X8,
        Instruction::LogicalShiftedReg(i) => i.rd == X8,
        Instruction::LogicalImm(i) => i.rd == X8,
        Instruction::AddSubImm(i) => i.rd == X8,
        Instruction::AddSubCarry(i) => i.rd == X8,
        Instruction::MoveWide(i) => i.rd == X8,
        Instruction::BitfieldMove(i) => i.rd == X8,
        Instruction::PcRelAddress(i) => i.rd == X8,
        Instruction::DataProcessing2Source(i) => i.rd == X8,
        Instruction::DataProcessing3Source(i) => i.rd == X8,
        Instruction::ConditionalSelect(i) => i.rd == X8,
        Instruction::FpIntConversion(i) => i.rd == X8,
        Instruction::LoadStoreUnsignedImm(i) => !i.vector && i.opc != 0 && i.rt == X8,
        Instruction::LoadStoreUnscaled(i) => !i.vector && i.opc != 0 && i.rt == X8,
        Instruction::LoadStoreIndexed(i) => !i.vector && i.opc != 0 && i.rt == X8,
        Instruction::LoadStoreRegister(i) => !i.vector && i.opc != 0 && i.rt == X8,
        Instruction::LoadLiteral(i) => !i.vector && i.rt == X8,
        Instruction::LoadStorePair(i) => !i.vector && i.load && (i.rt == X8 || i.rt2 == X8),
        _ => false,
    }
}

/// The hidden-result edge from `caller` to the external declaration `callee`
/// is an indirect call: X8 is written before a `BLR`, the caller contains no
/// `BL` (an external declaration is not an exact-module target, so the edge
/// must not be devirtualized), and no `CALL26`/`JUMP26` relocation names the
/// declaration. Every word of the caller must decode, so an instruction the
/// decoder does not model fails closed rather than hiding an X8 write.
fn sret_edge_is_indirect(object: &[u8], caller: &str, callee: &str) -> Result<(), String> {
    let elf = parse_elf(object)?;
    let mut x8_written = false;
    let mut blr = 0usize;
    for (offset, word) in elf.function_words(object, caller)? {
        match decode(word) {
            Ok(Instruction::BranchReg(branch)) if branch.opc == BLR_OPC => {
                if !x8_written {
                    return Err(format!("{caller}: blr at {offset:#x} before x8 is written"));
                }
                blr += 1;
            }
            Ok(Instruction::UncondBranch(branch)) if branch.link => {
                return Err(format!(
                    "{caller}: bl at {offset:#x}: the sret edge was devirtualized"
                ));
            }
            Ok(inst) => x8_written |= writes_x8(&inst),
            Err(error) => return Err(format!("{caller}: word at {offset:#x}: {error}")),
        }
    }
    if blr == 0 {
        return Err(format!("{caller}: no blr"));
    }
    if let Some(relocation) = elf.relocations.iter().find(|relocation| {
        relocation.symbol == callee
            && (relocation.kind == R_AARCH64_CALL26 || relocation.kind == R_AARCH64_JUMP26)
    }) {
        return Err(format!(
            "relocation type {} against {callee} at {:#x}: the sret edge was devirtualized",
            relocation.kind, relocation.instruction
        ));
    }
    Ok(())
}

#[test]
fn elf_object_defines_every_sret_function_and_imports_every_c_callee_o0_through_o3() {
    let callees = corpus::build_callee_module(TRIPLE);
    let callers = corpus::build_caller_module(TRIPLE);
    for opt_level in ALL_LEVELS {
        let object = compile_ok(&callees, opt_level);
        assert_eq!(
            corpus_symbols_resolve(&object, corpus::CALLEE_SYMBOLS, corpus::CALLEE_IMPORTS),
            Ok(()),
            "callees at {opt_level:?}"
        );
        let object = compile_ok(&callers, opt_level);
        assert_eq!(
            corpus_symbols_resolve(&object, corpus::CALLER_SYMBOLS, corpus::CALLER_IMPORTS),
            Ok(()),
            "callers at {opt_level:?}"
        );
    }

    // Mutation controls: a local binding, a zero size and a C callee that the
    // object defines itself (the driver's definition would then be shadowed
    // or duplicated) must each fail.
    let object = compile_ok(&callers, OptLevel::O0);
    let elf = parse_elf(&object).unwrap();
    let defined = elf.symbol(corpus::STATIC_PROVENANCE_CALLER).unwrap();
    let import = elf.symbol(corpus::STATIC_PROVENANCE_CALLEE).unwrap();
    let check = |mutated: &[u8]| {
        corpus_symbols_resolve(mutated, corpus::CALLER_SYMBOLS, corpus::CALLER_IMPORTS)
    };
    let mut local = object.clone();
    local[defined.record + 4] &= 0x0f; // STB_GLOBAL -> STB_LOCAL
    assert_eq!(
        check(&local),
        Err(format!(
            "{} is not a defined global function",
            corpus::STATIC_PROVENANCE_CALLER
        ))
    );
    let mut empty = object.clone();
    empty[defined.record + 16..defined.record + 24].copy_from_slice(&0u64.to_le_bytes());
    assert_eq!(
        check(&empty),
        Err(format!("{} has size 0", corpus::STATIC_PROVENANCE_CALLER))
    );
    let mut resolved = object;
    resolved[import.record + 6..import.record + 8]
        .copy_from_slice(&(defined.section_index as u16).to_le_bytes());
    assert_eq!(
        check(&resolved),
        Err(format!(
            "{} is not an undefined global",
            corpus::STATIC_PROVENANCE_CALLEE
        ))
    );
}

#[test]
fn elf_static_provenance_sret_edge_stays_an_indirect_call_o0_through_o3() {
    let module = corpus::build_caller_module(TRIPLE);
    for opt_level in ALL_LEVELS {
        let object = compile_ok(&module, opt_level);
        assert_eq!(
            sret_edge_is_indirect(
                &object,
                corpus::STATIC_PROVENANCE_CALLER,
                corpus::STATIC_PROVENANCE_CALLEE
            ),
            Ok(()),
            "{opt_level:?}"
        );
    }

    // Mutation controls, one per arm of the check: the BLR replaced by a NOP,
    // the BLR replaced by a BL, every X8 write redirected to X9, and the
    // declaration's address relocation retyped as a call relocation.
    let object = compile_ok(&module, OptLevel::O0);
    let elf = parse_elf(&object).unwrap();
    let words = elf
        .function_words(&object, corpus::STATIC_PROVENANCE_CALLER)
        .unwrap();
    let check = |mutated: &[u8]| {
        sret_edge_is_indirect(
            mutated,
            corpus::STATIC_PROVENANCE_CALLER,
            corpus::STATIC_PROVENANCE_CALLEE,
        )
        .unwrap_err()
    };
    let blr = words
        .iter()
        .find(|(_, word)| {
            matches!(decode(*word), Ok(Instruction::BranchReg(branch)) if branch.opc == BLR_OPC)
        })
        .map(|(offset, _)| *offset)
        .expect("the static-provenance caller has a blr");
    let mut nop = object.clone();
    nop[blr..blr + 4].copy_from_slice(&AARCH64_NOP.to_le_bytes());
    assert!(check(&nop).contains("no blr"), "{}", check(&nop));
    let mut bl = object.clone();
    bl[blr..blr + 4].copy_from_slice(&AARCH64_BL_0.to_le_bytes());
    assert!(check(&bl).contains("devirtualized"), "{}", check(&bl));
    let mut x9 = object.clone();
    let mut redirected = 0;
    for (offset, word) in &words {
        if decode(*word).is_ok_and(|inst| writes_x8(&inst)) {
            // Rd/Rt are bits 0..5; Rt2 of a pair is bits 10..15.
            let patched = if word & 0x1f == u32::from(X8) {
                (word & !0x1f) | 9
            } else {
                (word & !(0x1f << 10)) | (9 << 10)
            };
            x9[*offset..offset + 4].copy_from_slice(&patched.to_le_bytes());
            redirected += 1;
        }
    }
    assert!(redirected > 0, "the caller writes x8 at least once");
    assert!(
        check(&x9).contains("before x8 is written"),
        "{}",
        check(&x9)
    );
    let address = elf
        .relocations
        .iter()
        .find(|relocation| relocation.symbol == corpus::STATIC_PROVENANCE_CALLEE)
        .expect("the declaration's address is relocated");
    let mut call = object;
    call[address.record + 8..address.record + 12].copy_from_slice(&R_AARCH64_CALL26.to_le_bytes());
    assert!(check(&call).contains("devirtualized"), "{}", check(&call));
}

#[test]
fn elf_indirect_edge_disagreeing_with_a_resolved_sret_declaration_is_refused() {
    // The declaration passes a hidden buffer and returns nothing; the edge
    // claims the same parameters but an I64 result.
    let module = corpus::indirect_edge_module(
        TRIPLE,
        (vec![Ty::Ptr, Ty::I64], vec![], false),
        |attrs| attrs[0].sret = true,
        (vec![Ty::Ptr, Ty::I64], vec![Ty::I64], false),
        1,
    );
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        assert_refused(
            &module,
            opt_level,
            &["[TCG-SRET-ABI]", "indirect call resolves to `callee`"],
        );
    }
}

#[test]
fn elf_indirect_edge_agreeing_with_a_resolved_sret_declaration_compiles() {
    let module = corpus::indirect_edge_module(
        TRIPLE,
        (vec![Ty::Ptr, Ty::I64], vec![], false),
        |attrs| attrs[0].sret = true,
        (vec![Ty::Ptr, Ty::I64], vec![], false),
        0,
    );
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_ok(&module, opt_level);
        assert_eq!(
            sret_edge_is_indirect(&object, "caller", "callee"),
            Ok(()),
            "{opt_level:?}"
        );
    }
}

#[test]
fn elf_indirect_call_over_a_variadic_sret_signature_stays_refused() {
    let module = corpus::indirect_edge_module(
        TRIPLE,
        (vec![Ty::Ptr, Ty::I32], vec![], true),
        |attrs| attrs[0].sret = true,
        (vec![Ty::Ptr, Ty::I32], vec![], true),
        0,
    );
    assert_refused(
        &module,
        OptLevel::O0,
        &["CallIndirect over variadic FuncTyId"],
    );
}

#[test]
fn elf_hidden_parameter_declarations_the_selector_cannot_place_are_refused() {
    assert_refused(
        &corpus::sret_at_index_1_module(TRIPLE),
        OptLevel::O0,
        &[
            "[TCG-SRET-ABI]",
            "only a leading hidden return-buffer parameter is supported",
        ],
    );
    assert_refused(
        &corpus::sret_with_return_module(TRIPLE),
        OptLevel::O0,
        &["[TCG-SRET-ABI]", "requires an empty return list"],
    );
    assert_refused(
        &corpus::sret_variadic_definition_module(TRIPLE),
        OptLevel::O0,
        &["[TCG-VARIADIC-DEFINITION]"],
    );
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::{ALL_LEVELS, TRIPLE, compile_ok, corpus, process};
    use std::fs;
    use std::path::Path;
    use std::process::Command;

    /// How the drivers name their oracle: the host's `cc` (GCC on the Linux
    /// floor host), not the clang the Darwin test links against.
    const ORACLE: &str = "the host cc";

    /// AAPCS64 §6.8.2 rule C.16 slot probe, Linux-only: the CG callees are
    /// called through a prototype whose two `int32_t` arguments are `int64_t`
    /// with poisoned high halves. Under base AAPCS64 both prototypes place
    /// every argument identically (`a8` at `[sp]`, `d8` at `[sp, #8]`, the
    /// narrow pair in the 8-byte slots at `[sp, #16]` and `[sp, #24]`), so
    /// the row shows that the `int64_t` prototype lands the narrow pair in
    /// the same 8-byte slots and that the CG callees' `I32` add/sub results
    /// are unaffected by the poisoned high halves. It shows no more than
    /// that: the corpus uses `n0`/`n1` only in 32-bit add/sub, whose low 32
    /// bits are independent of the slot's high 32 bits, so this row does NOT
    /// distinguish a callee that reads the full 8-byte slot from one that
    /// reads its low 32 bits (a C callee declared with `int64_t` narrows and
    /// 64-bit arithmetic passes it as well), and it does not evidence the
    /// callee-side narrow handling the C.16 "unspecified bits" clause
    /// permits; only `e2e_aarch64_bool_abi_linux` evidences that, for
    /// register narrows. Under DarwinPCS packing the narrow pair would share
    /// one slot and this probe would not be well-formed, which is why the
    /// Darwin test has no such row. The call through a differently-typed
    /// pointer is an ABI-level probe outside the C abstract machine, kept
    /// behind a `volatile` pointer so the oracle cannot fold it.
    const WIDE_SLOT_DRIVER: &str = r#"
typedef struct Big (*wide_fn)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t,
                              int64_t, int64_t, double, double, double, double, double, double,
                              double, double, double, int64_t, int64_t);
extern struct Big cg_sret_attr(ORDINARY_PARAMS);
extern struct Big cg_sret_struct(ORDINARY_PARAMS);

int main(void) {
    const int64_t n0w = (int64_t)(((uint64_t)0xdeadbeefu << 32) | (uint32_t)N0);
    const int64_t n1w = (int64_t)(((uint64_t)0x5a5a5a5au << 32) | (uint32_t)N1);
    wide_fn volatile fns[2] = { (wide_fn)cg_sret_attr, (wide_fn)cg_sret_struct };
    const char *names[2] = {
        "wide-slot C caller -> cg_sret_attr", "wide-slot C caller -> cg_sret_struct"
    };
    for (int k = 0; k < 2; k++) {
        struct Big got;
        memset(&got, 0x5a, sizeof got);
        got = fns[k](A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8],
                     D[0], D[1], D[2], D[3], D[4], D[5], D[6], D[7], D[8], n0w, n1w);
        if (!same(names[k], &got)) return k + 1;
    }
    printf("C caller with poisoned 8-byte narrow slots -> CG sret callees agree with " ORACLE "\n");
    return 0;
}
"#;

    fn wide_slot_pass_line() -> String {
        format!("C caller with poisoned 8-byte narrow slots -> CG sret callees agree with {ORACLE}")
    }

    fn scratch_dir(tag: &str) -> crate::fresh_dir::ScratchDir {
        crate::fresh_dir::create(&format!("trust-cg-sret-linux-{tag}-"))
    }

    fn oracle_version() -> String {
        Command::new("cc")
            .arg("--version")
            .output()
            .ok()
            .and_then(|out| {
                String::from_utf8_lossy(&out.stdout)
                    .lines()
                    .next()
                    .map(str::to_owned)
            })
            .unwrap_or_else(|| "cc --version unavailable".into())
    }

    /// Link `object` with the shared oracle prelude and `driver` at `-O2` (an
    /// O0 C side could spill and re-read in ways that mask a placement defect
    /// on the CG side), run it, and require exit 0 with exactly `pass_line`.
    fn link_and_run(tag: &str, object: &[u8], driver: &str, pass_line: &str) {
        let dir = scratch_dir(tag);
        let object_path = dir.join("module.o");
        let driver_path = dir.join("driver.c");
        let binary = dir.join("driver");
        fs::write(&object_path, object).expect("write object");
        fs::write(
            &driver_path,
            format!("{}\n{driver}", corpus::ORACLE_PRELUDE),
        )
        .expect("write driver");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg("-O2")
                .arg(format!("-DORACLE=\"{ORACLE}\""))
                .arg(&driver_path)
                .arg(&object_path)
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .expect("cc is required on the Linux aarch64 host");
        assert!(
            !link.timed_out && link.output.status.success(),
            "{tag}: link failed; files={dir:?}\n{}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run = process::run_executable_with_timeout(
            Path::new(&binary),
            process::codegen_run_timeout(),
        )
        .expect("run the linked driver");
        let stdout = String::from_utf8_lossy(&run.output.stdout);
        assert!(
            !run.timed_out && run.output.status.success(),
            "{tag}: CG diverged from the oracle; files={dir:?}\n{stdout}{}",
            String::from_utf8_lossy(&run.output.stderr)
        );
        assert_eq!(
            stdout.trim(),
            pass_line,
            "{tag}: incomplete native execution; files={dir:?}"
        );
        eprintln!("{tag}: {}", stdout.trim());
        fs::remove_dir_all(&dir).expect("remove scratch dir");
    }

    #[test]
    fn native_c_caller_reaches_cg_sret_callees_through_pointers_o0_through_o3() {
        eprintln!("oracle: {}", oracle_version());
        let module = corpus::build_callee_module(TRIPLE);
        for opt_level in ALL_LEVELS {
            let object = compile_ok(&module, opt_level);
            link_and_run(
                &format!("callee-{opt_level:?}"),
                &object,
                corpus::CALLEE_DRIVER,
                &corpus::callee_pass_line(ORACLE),
            );
            link_and_run(
                &format!("wide-slot-{opt_level:?}"),
                &object,
                WIDE_SLOT_DRIVER,
                &wide_slot_pass_line(),
            );
        }
    }

    #[test]
    fn native_cg_caller_reaches_c_sret_callees_through_pointers_and_variadics_o0_through_o3() {
        eprintln!("oracle: {}", oracle_version());
        let module = corpus::build_caller_module(TRIPLE);
        for opt_level in ALL_LEVELS {
            let object = compile_ok(&module, opt_level);
            link_and_run(
                &format!("caller-{opt_level:?}"),
                &object,
                corpus::CALLER_DRIVER,
                &corpus::caller_pass_line(ORACLE),
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
