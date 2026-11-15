// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Native Linux ELF linking: GOT imports, absolute pointer slots, function
//! calls, symbol binding and shared-library relocation. This is execution
//! evidence, not a claim of whole-compiler or dynamic-linker proof authority.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, CallingConv, Constant, Endianness, FuncId, FuncTy, Function, Global,
    Inst, InstrNode, Linkage, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

fn global_address(index: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::GlobalAddr {
        global: GlobalId::new(index),
    })
    .with_result(ValueId::new(result))
}

fn load(ty: Ty, pointer: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty,
        ptr: ValueId::new(pointer),
        volatile: false,
        align: Some(8),
    })
    .with_result(ValueId::new(result))
}

fn fixture() -> Module {
    let mut module = Module::new("linux_elf_link");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    // The import contributes no local storage. Pointer slots are deliberately
    // mutable .data, as a writable function/data dispatch table; immutable
    // pointer-table placement is a separate qualification requirement.
    let word_type = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    module.globals = vec![
        Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "elf_words".into(),
            ty: Ty::Array(word_type, 3),
            mutable: true,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: Some(8),
        },
        Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "elf_data_slot".into(),
            ty: Ty::Ptr,
            mutable: true,
            initializer: Some(Constant::SymbolAddr {
                symbol: "elf_words".into(),
                addend: 8,
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(8),
        },
        Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "elf_fn_slot".into(),
            ty: Ty::Ptr,
            mutable: true,
            initializer: Some(Constant::SymbolAddr {
                symbol: "elf_provider".into(),
                addend: 0,
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: Some(8),
        },
        Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "elf_public_seed".into(),
            ty: Ty::U64,
            mutable: true,
            // WS7.3: typed at the global's `u64` (trust-ir refuses a byte
            // aggregate there as `ConstTypeMismatch`).
            initializer: Some(Constant::Int(0x12345678)),
            linkage: Linkage::External,
            tls: None,
            align: Some(8),
        },
    ];
    let provider_signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64, Ty::Ptr],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let provider_id = FuncId::new(0);
    let mut provider = Function::new(
        provider_id,
        "elf_provider",
        provider_signature,
        BlockId::new(0),
    );
    provider.linkage = Linkage::External;
    provider.blocks.clear();
    module
        .try_add_function(provider)
        .expect("Module::try_add_function: test fixture");

    let touch_signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut touch = Function::new(
        FuncId::new(1),
        "elf_touch",
        touch_signature,
        BlockId::new(0),
    );
    touch.linkage = Linkage::External;
    touch.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::U64)],
        body: vec![
            global_address(0, 1),
            load(Ty::U64, 1, 2),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::U64,
                ptr: ValueId::new(1),
                value: ValueId::new(3),
                volatile: false,
                align: Some(8),
            }),
            global_address(1, 4),
            load(Ty::Ptr, 4, 5),
            InstrNode::new(Inst::Call {
                callee: provider_id,
                args: vec![ValueId::new(0), ValueId::new(5)],
            })
            .with_result(ValueId::new(6)),
            global_address(2, 7),
            load(Ty::Ptr, 7, 8),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(8),
                sig: provider_signature,
                args: vec![ValueId::new(6), ValueId::new(5)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(9)],
            }),
        ],
    }];
    module
        .try_add_function(touch)
        .expect("Module::try_add_function: test fixture");
    let address_signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (global, name) in [(1, "elf_data_address"), (2, "elf_function_address")] {
        let mut getter = Function::new(
            FuncId::new(module.functions.len() as u32),
            name,
            address_signature,
            BlockId::new(0),
        );
        getter.linkage = Linkage::External;
        getter.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                global_address(global, 0),
                load(Ty::Ptr, 0, 1),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        }];
        module
            .try_add_function(getter)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

const PROVIDER: &str = r#"
#include <stdint.h>
uint64_t elf_words[3] = { 17, 29, 0xfeedface };
__attribute__((noinline)) uint64_t elf_provider(uint64_t x, uint64_t *p) {
    *p += x * UINT64_C(0x100000001b3) + UINT64_C(0x27d4eb2d);
    return *p ^ (x >> 7);
}
uint64_t *elf_words_address(void) { return elf_words; }
"#;

const DRIVER: &str = r#"
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
typedef uint64_t (*provider_fn)(uint64_t, uint64_t *);
extern uint64_t elf_words[3], elf_public_seed;
extern uint64_t elf_touch(uint64_t);
extern uint64_t elf_provider(uint64_t, uint64_t *);
extern uint64_t *elf_words_address(void), *elf_data_address(void);
extern provider_fn elf_function_address(void);
static uint64_t reference_provider(uint64_t x, uint64_t *p) {
    *p += x * UINT64_C(0x100000001b3) + UINT64_C(0x27d4eb2d);
    return *p ^ (x >> 7);
}
static uint64_t reference_touch(uint64_t x, uint64_t *words) {
    words[0] += x;
    uint64_t first = reference_provider(x, &words[1]);
    return reference_provider(first, &words[1]);
}
int main(void) {
    if (elf_words_address() != elf_words || elf_data_address() != &elf_words[1]
        || elf_function_address() != elf_provider) return 2;
    if (elf_public_seed != UINT64_C(0x12345678)) return 3;
    uint64_t reference[3] = { 17, 29, 0xfeedface };
    uint64_t random = UINT64_C(0x3141592653589793);
    const uint64_t edges[] = { 0, 1, UINT64_MAX, UINT64_C(0x8000000000000000),
        UINT64_C(0x7fffffffffffffff), UINT64_C(0x100000000), 255, 256 };
    for (unsigned i = 0; i < 128; ++i) {
        random = random * UINT64_C(6364136223846793005) + 1;
        uint64_t x = i < 8 ? edges[i] : random;
        // Alternate C-side mutation with CG-side writes: neither side may
        // observe a duplicate import definition or a stale/copy-relocated view.
        elf_words[0] ^= random;
        reference[0] ^= random;
        elf_words[1] += i;
        reference[1] += i;
        uint64_t expected = reference_touch(x, reference);
        uint64_t actual = elf_touch(x);
        if (actual != expected || elf_words[0] != reference[0]
            || elf_words[1] != reference[1] || elf_words[2] != reference[2]) {
            fprintf(stderr, "case %u result=%" PRIx64 " expected=%" PRIx64
                " memory=%" PRIx64 ",%" PRIx64 ",%" PRIx64 "\n",
                i, actual, expected, elf_words[0], elf_words[1], elf_words[2]);
            return 4;
        }
        elf_public_seed ^= x;
    }
    puts("128 exact ELF call/memory cases passed");
    return 0;
}
"#;

// Both translation units use the same exception definition and exact external
// C symbol ABI as the ordinary fixture. CG has no handler or cleanup: only its
// emitted frame descriptions can let the unwinder reach the C++ caller.
const UNWIND_PROVIDER: &str = r#"
#include <cstdint>
struct ElfException { uint64_t payload; unsigned stage; };
extern "C" {
uint64_t elf_words[3] = { 17, 29, 0xfeedface };
volatile unsigned elf_calls = 0, elf_provider_dtors = 0, elf_throw_on_call = 0;
}
struct ProviderGuard {
    __attribute__((noinline)) ~ProviderGuard() noexcept {
        elf_provider_dtors = elf_provider_dtors + 1;
    }
};
extern "C" __attribute__((noinline)) uint64_t elf_provider(uint64_t x, uint64_t *p) {
    ProviderGuard guard;
    unsigned stage = elf_calls + 1;
    elf_calls = stage;
    *p += x * UINT64_C(0x100000001b3) + UINT64_C(0x27d4eb2d);
    if (elf_throw_on_call == stage)
        throw ElfException { x ^ *p ^ UINT64_C(0xdecafbad12345678), stage };
    return *p ^ (x >> 7);
}
extern "C" uint64_t *elf_words_address(void) { return elf_words; }
"#;

const UNWIND_DRIVER: &str = r#"
#include <cinttypes>
#include <cstdint>
#include <cstdio>
struct ElfException { uint64_t payload; unsigned stage; };
typedef uint64_t (*provider_fn)(uint64_t, uint64_t *);
extern "C" {
extern uint64_t elf_words[3], elf_public_seed;
extern volatile unsigned elf_calls, elf_provider_dtors, elf_throw_on_call;
uint64_t elf_touch(uint64_t), elf_provider(uint64_t, uint64_t *);
uint64_t *elf_words_address(void), *elf_data_address(void);
provider_fn elf_function_address(void);
}
static unsigned caller_dtors = 0;
struct CallerGuard {
    __attribute__((noinline)) ~CallerGuard() noexcept { ++caller_dtors; }
};
static uint64_t reference_provider(uint64_t x, uint64_t *p) {
    *p += x * UINT64_C(0x100000001b3) + UINT64_C(0x27d4eb2d);
    return *p ^ (x >> 7);
}
int main() {
    if (elf_words_address() != elf_words || elf_data_address() != &elf_words[1]
        || elf_function_address() != elf_provider) return 2;
    if (elf_public_seed != UINT64_C(0x12345678)) return 3;
    uint64_t random = UINT64_C(0x3141592653589793);
    const uint64_t edges[] = { 0, 1, UINT64_MAX, UINT64_C(0x8000000000000000),
        UINT64_C(0x7fffffffffffffff), UINT64_C(0x100000000), 255, 256 };
    for (unsigned i = 0; i < 64; ++i) {
        random = random * UINT64_C(6364136223846793005) + 1;
        uint64_t x = i < 8 ? edges[i] : random;
        for (unsigned throw_stage = 0; throw_stage < 3; ++throw_stage) {
            uint64_t reference[3] = { random, ~random, UINT64_C(0xfeedfacecafebeef) };
            for (unsigned j = 0; j < 3; ++j) elf_words[j] = reference[j];
            elf_throw_on_call = throw_stage;
            elf_calls = 0;
            elf_provider_dtors = 0;
            caller_dtors = 0;
            reference[0] += x;
            uint64_t first = reference_provider(x, &reference[1]);
            uint64_t payload = x ^ reference[1] ^ UINT64_C(0xdecafbad12345678);
            uint64_t expected = 0;
            if (throw_stage != 1) {
                expected = reference_provider(first, &reference[1]);
                payload = first ^ reference[1] ^ UINT64_C(0xdecafbad12345678);
            }
            bool caught = false;
            uint64_t actual = 0;
            try {
                CallerGuard guard;
                actual = elf_touch(x);
            } catch (const ElfException &exception) {
                caught = true;
                if (exception.stage != throw_stage || exception.payload != payload) {
                    std::fprintf(stderr, "wrong exception case=%u stage=%u payload=%" PRIx64 "\n",
                        i, exception.stage, exception.payload);
                    return 4;
                }
            } catch (...) {
                std::fprintf(stderr, "wrong exception type case=%u stage=%u\n", i, throw_stage);
                return 5;
            }
            unsigned calls = throw_stage == 1 ? 1 : 2;
            if (caught != (throw_stage != 0) || (!caught && actual != expected)
                || elf_calls != calls || elf_provider_dtors != calls || caller_dtors != 1
                || elf_words[0] != reference[0] || elf_words[1] != reference[1]
                || elf_words[2] != reference[2]) {
                std::fprintf(stderr, "unwind mismatch case=%u stage=%u caught=%d calls=%u provider_dtors=%u caller_dtors=%u\n",
                    i, throw_stage, caught, unsigned(elf_calls), unsigned(elf_provider_dtors), caller_dtors);
                return 6;
            }
        }
    }
    std::puts("192 exact ELF exception/RAII/memory cases passed");
    return 0;
}
"#;

fn command(command: &mut Command, directory: &Path) -> String {
    let output = process::command_output_with_timeout(command, process::codegen_link_timeout())
        .expect("required native ELF tool must launch");
    assert!(
        !output.timed_out && output.output.status.success(),
        "ELF command {command:?} failed; preserved files={directory:?}\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.output.stdout),
        String::from_utf8_lossy(&output.output.stderr),
    );
    String::from_utf8(output.output.stdout).expect("native ELF tool output is UTF-8")
}

fn inspect(path: &Path, directory: &Path, relocatable: bool) -> String {
    let bytes = fs::read(path).unwrap();
    assert_eq!(
        &bytes[..6],
        b"\x7fELF\x02\x01",
        "ELF64 little-endian required"
    );
    assert_eq!(
        u16::from_le_bytes([bytes[18], bytes[19]]),
        183,
        "EM_AARCH64 required"
    );
    assert_eq!(
        u16::from_le_bytes([bytes[16], bytes[17]]),
        if relocatable { 1 } else { 3 }
    );
    // binutils independently reads actual serialized ELF; do not use the
    // compiler's own emitter/reparser to supply expected symbol/reloc facts.
    let text = command(
        Command::new("readelf")
            .env("LC_ALL", "C")
            .args([
                "--wide",
                "--file-header",
                "--symbols",
                "--relocs",
                "--dynamic",
            ])
            .arg(path),
        directory,
    );
    fs::write(path.with_extension("readelf.txt"), &text).unwrap();
    assert!(text.contains("AArch64"));
    assert!(
        !text.contains("TEXTREL"),
        "shared objects must not require writable text"
    );
    text
}

fn assert_symbol(text: &str, name: &str, binding: &str, undefined: bool) {
    let rows: Vec<_> = text
        .lines()
        .filter(|line| {
            let columns: Vec<_> = line.split_whitespace().collect();
            columns.len() == 8 && columns[7] == name && columns[0].ends_with(':')
        })
        .collect();
    assert!(
        !rows.is_empty(),
        "symbol {name} absent from real ELF symbol table"
    );
    for row in rows {
        let columns: Vec<_> = row.split_whitespace().collect();
        assert_eq!(columns[4], binding, "wrong ELF symbol binding: {row}");
        assert_eq!(
            columns[6] == "UND",
            undefined,
            "wrong ELF definition/import: {row}"
        );
    }
}

fn assert_relocation(text: &str, kind: &str, symbol: &str, addend: &str) {
    assert!(
        text.lines().any(|line| {
            let columns: Vec<_> = line.split_whitespace().collect();
            columns.len() == 7
                && columns[2] == kind
                && columns[4] == symbol
                && columns[5] == "+"
                && columns[6] == addend
        }),
        "missing {kind} against {symbol} + {addend}\n{text}"
    );
}

/// The ELF FDE describes this object's function body, not whichever definition
/// of its exported name a dynamic linker selects. GNU cc -fPIC emits a local
/// STT_SECTION .text reference plus the body offset. Parse the independent
/// readelf view, including binding and exact target offsets, not just PREL32's
/// arithmetic kind or the compiler's intended relocation inventory.
fn validate_fde_bindings(text: &str) -> Result<(), String> {
    let symbol = |name: &str| -> Result<Vec<&str>, String> {
        let rows: Vec<Vec<&str>> = text
            .lines()
            .map(|line| line.split_whitespace().collect())
            .filter(|columns: &Vec<&str>| {
                columns.len() == 8 && columns[0].ends_with(':') && columns[7] == name
            })
            .collect();
        if rows.len() != 1 {
            return Err(format!(
                "expected one ELF symbol row for {name}, got {}",
                rows.len()
            ));
        }
        Ok(rows.into_iter().next().unwrap())
    };
    let anchor = symbol(".text")?;
    if anchor[1] != "0000000000000000"
        || anchor[3] != "SECTION"
        || anchor[4] != "LOCAL"
        || anchor[5] != "DEFAULT"
        || anchor[6] == "UND"
    {
        return Err(format!(
            "FDE anchor must be local .text section at offset zero: {anchor:?}"
        ));
    }
    let mut expected = BTreeSet::new();
    for name in ["elf_touch", "elf_data_address", "elf_function_address"] {
        let function = symbol(name)?;
        if function[3] != "FUNC"
            || function[4] != "GLOBAL"
            || function[5] != "DEFAULT"
            || function[6] != anchor[6]
        {
            return Err(format!(
                "exported function must remain defined in .text: {function:?}"
            ));
        }
        let offset = u64::from_str_radix(function[1], 16)
            .map_err(|_| format!("invalid function offset: {function:?}"))?;
        if !expected.insert(offset) {
            return Err("fixture functions unexpectedly share an offset".into());
        }
    }
    let mut in_fde_relocations = false;
    let mut sections = 0;
    let mut observed = BTreeSet::new();
    for line in text.lines() {
        if line.starts_with("Relocation section '") {
            in_fde_relocations = line.starts_with("Relocation section '.rela.eh_frame'");
            sections += usize::from(in_fde_relocations);
            continue;
        }
        let columns: Vec<_> = line.split_whitespace().collect();
        if !in_fde_relocations || columns.len() != 7 || !columns[2].starts_with("R_") {
            continue;
        }
        if columns[2] != "R_AARCH64_PREL32"
            || columns[4] != ".text"
            || columns[3] != "0000000000000000"
            || columns[5] != "+"
        {
            return Err(format!("FDE must name the local .text anchor: {line}"));
        }
        let addend = u64::from_str_radix(columns[6], 16)
            .map_err(|_| format!("invalid FDE relocation addend: {line}"))?;
        if !observed.insert(addend) {
            return Err(format!(
                "duplicate FDE relocation at function offset {addend:#x}"
            ));
        }
    }
    if sections != 1 || observed != expected {
        return Err(format!(
            "FDE body offsets must match each defined function once: sections={sections}, expected={expected:?}, observed={observed:?}"
        ));
    }
    Ok(())
}

#[test]
fn elf_fde_binding_validator_rejects_interposable_and_offset_mutations() {
    // Independently captured GNU readelf row layout, with three fixture body
    // offsets. The real emitted objects pass through this same validator below.
    const VALID: &str = "Symbol table '.symtab' contains 5 entries:\n\
 1: 0000000000000000 0 SECTION LOCAL DEFAULT 1 .text\n\
 2: 0000000000000000 84 FUNC GLOBAL DEFAULT 1 elf_touch\n\
 3: 0000000000000054 28 FUNC GLOBAL DEFAULT 1 elf_data_address\n\
 4: 0000000000000070 28 FUNC GLOBAL DEFAULT 1 elf_function_address\n\
Relocation section '.rela.eh_frame' at offset 0x100 contains 3 entries:\n\
0000000000000020 0000000100000105 R_AARCH64_PREL32 0000000000000000 .text + 0\n\
0000000000000048 0000000100000105 R_AARCH64_PREL32 0000000000000000 .text + 54\n\
0000000000000068 0000000100000105 R_AARCH64_PREL32 0000000000000000 .text + 70\n";
    assert_eq!(validate_fde_bindings(VALID), Ok(()));
    let mutants = [
        VALID.replacen(".text + 0", "elf_touch + 0", 1),
        VALID.replacen(".text + 54", ".text + 58", 1),
        VALID
            .lines()
            .filter(|line| !line.contains(".text + 70"))
            .collect::<Vec<_>>()
            .join("\n"),
        format!(
            "{VALID}0000000000000088 0000000100000105 R_AARCH64_PREL32 0000000000000000 .text + 70\n"
        ),
        VALID.replacen("SECTION LOCAL", "SECTION GLOBAL", 1),
    ];
    for (index, mutant) in mutants.iter().enumerate() {
        assert!(
            validate_fde_bindings(mutant).is_err(),
            "FDE binding mutant {index} accepted"
        );
    }
}

#[derive(Clone, Copy, Debug)]
enum Boundary {
    ExecutableObjects,
    SharedProvider,
    SharedGenerated,
    SharedGeneratedUnwind,
}

fn new_directory(boundary: Boundary, level: OptLevel) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust-cg-elf-link-{boundary:?}-{level:?}-"))
}

fn exercise(boundary: Boundary) {
    exercise_pointer_slots(boundary, false);
}

// Public Pipeline callers may supply machine functions without frame layouts.
// Exercise both the data-only relocation path and mixed text/data relocations.
fn exercise_layoutless_pointer_slots(text_fixups: bool) {
    use trust_cg_codegen::pipeline::{GlobalSymbolRef, ObjectGlobal, Pipeline, PipelineConfig};
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::X0;

    let mut function = MachFunction::new("slot_target".into(), Signature::new(vec![], vec![]));
    let ret = function.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    function.append_inst(function.entry, ret);
    let mut functions = vec![function];
    if text_fixups {
        let mut getter = MachFunction::new(
            "local_address".into(),
            Signature::new(vec![], vec![Type::Ptr]),
        );
        for inst in [
            MachInst::new(
                AArch64Opcode::Adrp,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Symbol("local_words".into()),
                ],
            ),
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::Symbol("local_words".into()),
                ],
            ),
            MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]),
        ] {
            let id = getter.push_inst(inst);
            getter.append_inst(getter.entry, id);
        }
        functions.push(getter);
    }
    let local = ObjectGlobal {
        name: "local_words".into(),
        data: [17_u64, 29]
            .into_iter()
            .flat_map(u64::to_le_bytes)
            .collect(),
        mutable: false,
        is_external: false,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        align: 8,
        section: None,
        comdat: false,
    };
    let table = ObjectGlobal {
        name: "pointer_table".into(),
        data: vec![0; 32],
        align: 64,
        is_external: true,
        symbol_refs: [
            ("local_words", 8),
            ("imported_words", 8),
            ("slot_target", 0),
            ("slot_provider", 0),
        ]
        .into_iter()
        .enumerate()
        .map(|(i, (symbol, addend))| GlobalSymbolRef {
            offset: i as u64 * 8,
            symbol: symbol.into(),
            addend,
        })
        .collect(),
        ..local.clone()
    };
    let globals = vec![
        table.clone(),
        local.clone(),
        ObjectGlobal {
            name: "weak_words".into(),
            mutable: true,
            is_external: true,
            is_weak: true,
            ..local
        },
        ObjectGlobal {
            name: "weak_slot".into(),
            data: vec![0; 8],
            align: 128,
            symbol_refs: vec![GlobalSymbolRef {
                offset: 0,
                symbol: "weak_words".into(),
                addend: 8,
            }],
            ..table
        },
    ];
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: "aarch64-unknown-linux-gnu".into(),
        ..PipelineConfig::default()
    });
    let directory = new_directory(Boundary::SharedGenerated, OptLevel::O0);
    let generated = directory.join("layoutless.o");
    let object = pipeline
        .compile_module_with_globals(&functions, &globals)
        .expect("layoutless ELF must relocate non-TLS pointer slots");
    fs::write(&generated, object).unwrap();
    let symbols = inspect(&generated, &directory, true);
    assert_symbol(&symbols, "local_words", "LOCAL", false);
    assert_symbol(&symbols, "weak_words", "WEAK", false);
    for (name, addend) in [
        ("local_words", "8"),
        ("imported_words", "8"),
        ("slot_target", "0"),
        ("slot_provider", "0"),
        ("weak_words", "8"),
    ] {
        assert_relocation(&symbols, "R_AARCH64_ABS64", name, addend);
    }
    assert!(
        !symbols.contains(".rela.eh_frame"),
        "no frame layouts were supplied"
    );
    #[cfg(feature = "verify")]
    {
        use trust_cg_verify::ObjectRelocationKind;
        let report = pipeline
            .module_relocation_inventory_report_with_object_state(
                &functions,
                &globals,
                &[],
                "layoutless.o",
            )
            .unwrap()
            .unwrap();
        let actual_rows = symbols
            .lines()
            .filter(|line| line.contains("R_AARCH64_"))
            .count();
        assert_eq!(report.entries.len(), actual_rows);
        assert_eq!(
            report
                .entries
                .iter()
                .filter(|row| row.kind == ObjectRelocationKind::AArch64ElfAbs64)
                .count(),
            5
        );
    }
    let library = directory.join("libslots.so");
    command(
        Command::new("cc")
            .args(["-shared", "-Wl,-z,text,-z,relro,-z,now"])
            .arg(&generated)
            .arg("-o")
            .arg(&library),
        &directory,
    );
    inspect(&library, &directory, false);
    let driver = directory.join("slots.c");
    fs::write(&driver, r#"
#include <stdint.h>
#include <stdio.h>
uint64_t imported_words[3] = {31, 47, 53};
uint64_t weak_words[2] = {61, 73};
static int calls;
void slot_provider(void) { ++calls; }
extern void slot_target(void);
extern const void *const pointer_table[4];
extern const uint64_t *const weak_slot;
#ifdef TEXT_FIXUPS
extern const uint64_t *local_address(void);
#endif
int main(void) {
    if ((uintptr_t)pointer_table % 64 || (uintptr_t)&weak_slot % 128) return 1;
    if (*(const uint64_t *)pointer_table[0] != 29) return 2;
    if (pointer_table[1] != &imported_words[1]) return 3;
    if (pointer_table[2] != (void *)slot_target || pointer_table[3] != (void *)slot_provider) return 4;
    if (weak_slot != &weak_words[1] || *weak_slot != 73) return 5;
#ifdef TEXT_FIXUPS
    if (local_address() + 1 != pointer_table[0] || *local_address() != 17) return 6;
#endif
    ((void (*)(void))pointer_table[2])();
    ((void (*)(void))pointer_table[3])();
    if (calls != 1) return 7;
    puts("layoutless ELF pointer identities and weak override passed");
    return 0;
}
"#).unwrap();
    let binary = directory.join("slots");
    let mut link = Command::new("cc");
    link.args([
        "-std=c11",
        "-O2",
        "-fPIC",
        "-pie",
        "-Wl,-z,text,-z,relro,-z,now",
    ]);
    if text_fixups {
        link.arg("-DTEXT_FIXUPS");
    }
    command(
        link.arg(&driver).arg(&library).arg("-o").arg(&binary),
        &directory,
    );
    assert!(command(&mut Command::new(&binary), &directory).contains("weak override passed"));

    // The same slots inside a thread-local's initial-value template are
    // relocated in `.rela.tdata` (the layout-less emitter included), exactly
    // as gcc relocates `__thread void *p[] = {&x, ...};`.
    let mut thread_local = globals.clone();
    thread_local[0].is_thread_local = true;
    let tls_object = directory.join("layoutless-tls.o");
    fs::write(
        &tls_object,
        pipeline
            .compile_module_with_globals(&functions, &thread_local)
            .expect("layoutless ELF must relocate a TLS initial-value template"),
    )
    .unwrap();
    let tls_symbols = inspect(&tls_object, &directory, true);
    assert!(
        tls_symbols.contains("Relocation section '.rela.tdata'"),
        "the template slots relocate through .rela.tdata\n{tls_symbols}"
    );
    assert!(
        tls_symbols.lines().any(|line| {
            let columns: Vec<_> = line.split_whitespace().collect();
            columns.len() == 8 && columns[3] == "TLS" && columns[7] == "pointer_table"
        }),
        "the template symbol is STT_TLS\n{tls_symbols}"
    );
    let tdata_rows: Vec<&str> = tls_symbols
        .lines()
        .skip_while(|line| !line.starts_with("Relocation section '.rela.tdata'"))
        .skip(2)
        .take_while(|line| !line.trim().is_empty())
        .collect();
    assert_eq!(tdata_rows.len(), 4, "{tls_symbols}");
    for (name, addend) in [
        ("local_words", "8"),
        ("imported_words", "8"),
        ("slot_target", "0"),
        ("slot_provider", "0"),
    ] {
        assert_relocation(&tdata_rows.join("\n"), "R_AARCH64_ABS64", name, addend);
    }
    // A slot whose TARGET is a thread-local has no link-time address.
    let mut invalid = globals.clone();
    invalid[1].is_thread_local = true;
    let error = pipeline
        .compile_module_with_globals(&functions, &invalid)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("[TCG-TLS-SLOT-TARGET]") && error.contains("thread-local `local_words`"),
        "unexpected diagnostic: {error}"
    );
    invalid = globals.clone();
    invalid[0].symbol_refs[0].offset = 31;
    assert!(
        pipeline
            .compile_module_with_globals(&functions, &invalid)
            .is_err()
    );
}

#[test]
fn elf_layoutless_pointer_slots_without_text_fixups() {
    exercise_layoutless_pointer_slots(false);
}

#[test]
fn elf_layoutless_pointer_slots_with_text_fixups() {
    exercise_layoutless_pointer_slots(true);
}

fn exercise_pointer_slots(boundary: Boundary, immutable_slots: bool) {
    let unwind = matches!(boundary, Boundary::SharedGeneratedUnwind);
    let cc = if unwind { "c++" } else { "cc" };
    let language = if unwind { "-std=c++17" } else { "-std=c11" };
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let directory = new_directory(boundary, level);
        let generated = directory.join("generated.o");
        let mut module = fixture();
        if immutable_slots {
            for (index, alignment) in [(1, 64), (2, 128)] {
                module.globals[index].mutable = false;
                module.globals[index].align = Some(alignment);
            }
        }
        let compiled = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                ..CompilerConfig::default()
            },
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .expect("native ELF relocation fixture must compile");
        fs::write(&generated, compiled.object_code).unwrap();
        let object = inspect(&generated, &directory, true);
        validate_fde_bindings(&object).unwrap_or_else(|error| {
            panic!("invalid emitted FDE binding; files={directory:?}: {error}")
        });
        for symbol in ["elf_data_slot", "elf_fn_slot"] {
            assert_symbol(&object, symbol, "LOCAL", false);
        }
        for symbol in [
            "elf_touch",
            "elf_data_address",
            "elf_function_address",
            "elf_public_seed",
        ] {
            assert_symbol(&object, symbol, "GLOBAL", false);
        }
        for symbol in ["elf_words", "elf_provider"] {
            assert_symbol(&object, symbol, "GLOBAL", true);
        }
        assert_relocation(&object, "R_AARCH64_ABS64", "elf_words", "8");
        assert_relocation(&object, "R_AARCH64_ABS64", "elf_provider", "0");
        assert_relocation(&object, "R_AARCH64_CALL26", "elf_provider", "0");
        assert_relocation(&object, "R_AARCH64_ADR_GOT_PAGE", "elf_words", "0");
        assert_relocation(&object, "R_AARCH64_LD64_GOT_LO12_NC", "elf_words", "0");
        let provider = directory.join(if unwind { "provider.cpp" } else { "provider.c" });
        let driver = directory.join(if unwind { "driver.cpp" } else { "driver.c" });
        fs::write(&provider, if unwind { UNWIND_PROVIDER } else { PROVIDER }).unwrap();
        fs::write(&driver, if unwind { UNWIND_DRIVER } else { DRIVER }).unwrap();
        let provider_object = directory.join("provider.o");
        command(
            Command::new(cc)
                .args([language, "-O2", "-fPIC", "-fexceptions", "-c"])
                .arg(&provider)
                .arg("-o")
                .arg(&provider_object),
            &directory,
        );
        let binary = directory.join("driver");
        let mut link = Command::new(cc);
        link.args([language, "-O2", "-fPIC", "-fexceptions", "-pie"])
            .arg(&driver)
            .arg("-Wl,-z,defs,-z,text,-z,relro,-z,now,-rpath,$ORIGIN")
            .arg("-L")
            .arg(&directory)
            .arg("-o")
            .arg(&binary);
        match boundary {
            Boundary::ExecutableObjects => {
                link.arg(&generated).arg(&provider_object);
            }
            Boundary::SharedProvider
            | Boundary::SharedGenerated
            | Boundary::SharedGeneratedUnwind => {
                let library = directory.join("libprovider.so");
                command(
                    Command::new(cc)
                        .args(["-shared", "-Wl,-z,defs,-z,text,-soname,libprovider.so"])
                        .arg(&provider_object)
                        .arg("-o")
                        .arg(&library),
                    &directory,
                );
                inspect(&library, &directory, false);
                if matches!(
                    boundary,
                    Boundary::SharedGenerated | Boundary::SharedGeneratedUnwind
                ) {
                    let library = directory.join("libgenerated.so");
                    command(
                        Command::new(cc)
                            .arg("-shared")
                            .arg(&generated)
                            .arg("-L")
                            .arg(&directory)
                            .arg("-lprovider")
                            .arg("-Wl,-z,defs,-z,text,-z,relro,-z,now,-soname,libgenerated.so,-rpath,$ORIGIN")
                            .arg("-o")
                            .arg(&library),
                        &directory,
                    );
                    let linked = inspect(&library, &directory, false);
                    if immutable_slots {
                        assert_pointer_slots_in_relro(&library, &directory, &linked);
                    }
                    assert_symbol(&linked, "elf_touch", "GLOBAL", false);
                    assert_symbol(&linked, "elf_words", "GLOBAL", true);
                    assert_relocation(&linked, "R_AARCH64_ABS64", "elf_words", "8");
                    assert_relocation(&linked, "R_AARCH64_ABS64", "elf_provider", "0");
                    assert_relocation(&linked, "R_AARCH64_GLOB_DAT", "elf_words", "0");
                    assert_relocation(&linked, "R_AARCH64_JUMP_SLOT", "elf_provider", "0");
                    link.arg("-lgenerated");
                } else {
                    link.arg(&generated);
                }
                link.arg("-lprovider");
            }
        }
        command(&mut link, &directory);
        let linked = inspect(&binary, &directory, false);
        if immutable_slots
            && matches!(
                boundary,
                Boundary::ExecutableObjects | Boundary::SharedProvider
            )
        {
            assert_pointer_slots_in_relro(&binary, &directory, &linked);
        }
        let run = process::run_executable_with_timeout(&binary, process::codegen_run_timeout())
            .expect("linked native ELF driver must execute");
        assert!(
            !run.timed_out && run.output.status.success(),
            "{boundary:?}/{level:?} native mismatch; files={directory:?}\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.output.stdout).trim(),
            if unwind {
                "192 exact ELF exception/RAII/memory cases passed"
            } else {
                "128 exact ELF call/memory cases passed"
            }
        );
        fs::remove_dir_all(&directory).unwrap();
    }
}

// The linker must place each complete pointer slot in PT_GNU_RELRO. Merely
// making .rodata writable would link but lose the immutable storage contract.
// Read the linked image with binutils, independently of the compiler's parser.
fn assert_pointer_slots_in_relro(path: &Path, directory: &Path, symbols: &str) {
    let headers = command(
        Command::new("readelf")
            .env("LC_ALL", "C")
            .args(["--wide", "--program-headers"])
            .arg(path),
        directory,
    );
    fs::write(path.with_extension("segments.txt"), &headers).unwrap();
    let hex = |value: &str| u64::from_str_radix(value.trim_start_matches("0x"), 16).unwrap();
    let ranges: Vec<_> = headers
        .lines()
        .map(|line| line.split_whitespace().collect::<Vec<_>>())
        .filter(|columns| columns.first() == Some(&"GNU_RELRO"))
        .map(|columns| {
            let start = hex(columns[2]);
            (start, start.checked_add(hex(columns[5])).unwrap())
        })
        .collect();
    assert!(!ranges.is_empty(), "missing GNU_RELRO: {headers}");
    assert!(
        headers.contains(".data.rel.ro"),
        "missing relocation storage: {headers}"
    );
    for (name, alignment) in [("elf_data_slot", 64), ("elf_fn_slot", 128)] {
        let rows: Vec<_> = symbols
            .lines()
            .map(|line| line.split_whitespace().collect::<Vec<_>>())
            .filter(|columns| columns.len() == 8 && columns[7] == name)
            .collect();
        assert_eq!(rows.len(), 1, "expected exactly one local {name}");
        let row = &rows[0];
        assert_eq!(row[2], "8");
        assert_eq!(row[3], "OBJECT");
        assert_eq!(row[4], "LOCAL");
        let start = hex(row[1]);
        assert_eq!(start % alignment, 0, "lost alignment for {name}");
        let end = start.checked_add(8).unwrap();
        assert!(
            ranges
                .iter()
                .any(|&(low, high)| low <= start && end <= high),
            "{name} at {start:#x}..{end:#x} lies outside GNU_RELRO {ranges:?}"
        );
    }
}

#[test]
fn elf_executable_resolves_separate_object_calls_and_pointer_slots() {
    exercise(Boundary::ExecutableObjects);
}

#[test]
fn elf_executable_resolves_shared_provider_calls_and_pointer_slots() {
    exercise(Boundary::SharedProvider);
}

#[test]
fn elf_generated_shared_library_preserves_import_identity_and_memory() {
    exercise(Boundary::SharedGenerated);
}

#[test]
fn elf_cpp_exceptions_unwind_through_generated_frames_with_exact_raii() {
    exercise(Boundary::SharedGeneratedUnwind);
}

#[test]
fn elf_immutable_pointer_slots_link_in_pie_with_separate_objects() {
    exercise_pointer_slots(Boundary::ExecutableObjects, true);
}

#[test]
fn elf_immutable_pointer_slots_link_in_pie_with_shared_provider() {
    exercise_pointer_slots(Boundary::SharedProvider, true);
}

#[test]
fn elf_immutable_pointer_slots_link_in_shared_library() {
    exercise_pointer_slots(Boundary::SharedGenerated, true);
}

#[test]
fn elf_immutable_pointer_slots_preserve_shared_library_unwinding() {
    exercise_pointer_slots(Boundary::SharedGeneratedUnwind, true);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
