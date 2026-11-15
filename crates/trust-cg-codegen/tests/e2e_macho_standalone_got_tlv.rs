// trust-cg-codegen/tests/e2e_macho_standalone_got_tlv.rs - standalone Mach-O
// linking of GOT loads, Darwin TLV and libSystem data imports.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-cg-emitted AArch64 Mach-O objects that use `ARM64_RELOC_GOT_LOAD_*`
//! (a stack guard and a libSystem data import) and `ARM64_RELOC_TLVP_LOAD_*`
//! (a Darwin thread-local) are linked by the in-repo linker, without ld64.
//!
//! On every host the objects are linked standalone and the image is read back
//! with an independent reader: section types, `MH_HAS_TLV_DESCRIPTORS`, the
//! chained fixups behind each GOT/TLV slot, the resolved TLV descriptor, and
//! the patched ADRP/LDR pairs that reach those slots. Malformed relocations in
//! real CG objects are refused by name.
//!
//! On macOS AArch64 every standalone executable also runs next to an
//! ld64-linked twin of the same objects: both must agree on exit status and
//! stdout, `dyld_info -validate_only` must accept both images, and both must
//! bind the same imports. A CG object is also linked into an `MH_DYLIB` and
//! served to an ld64-linked program next to an ld64-built twin dylib. This is
//! execution evidence for these programs, not a linker proof.

mod common;

use trust_cg_codegen::frame;
use trust_cg_codegen::macho::linker::{
    DylibConfig, LinkerError, MachOParser, ParsedObject, lay_out_sections, link, link_dylib,
    link_with_dylibs,
};
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_codegen::macho::writer::MachOWriter;
use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::regs::{X0, XZR};
use trust_cg_ir::{
    AArch64Opcode as Op, MachFunction, MachInst, MachOperand as Operand, Signature as IrSignature,
    StackProtectorMode, TlsModel, Type as IrType,
};
use trust_cg_lower::function::{BasicBlock, Function as LowerFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LowerType;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const TLS_INITIAL: i64 = 7;

// ---------------------------------------------------------------------------
// CG objects
// ---------------------------------------------------------------------------

fn darwin_pipeline(opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        target_triple: "aarch64-apple-darwin".into(),
        opt_level,
        verify: true,
        ..PipelineConfig::default()
    })
}

fn inst(opcode: Opcode, args: Vec<Value>, results: Vec<Value>) -> Instruction {
    Instruction {
        opcode,
        args,
        results,
    }
}

fn lower_function(
    name: &str,
    params: Vec<LowerType>,
    returns: Vec<LowerType>,
    instructions: Vec<Instruction>,
) -> LowerFunction {
    let mut func = LowerFunction::new(name, Signature { params, returns });
    func.entry_block = Block(0);
    func.block_order = vec![Block(0)];
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

fn global(name: &str, data: Vec<u8>, thread_local: bool, import: bool, align: u32) -> ObjectGlobal {
    ObjectGlobal {
        name: name.into(),
        data,
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: thread_local,
        is_import: import,
        is_weak: false,
        align,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }
}

fn compile(pipeline: &Pipeline, functions: &[LowerFunction], globals: &[ObjectGlobal]) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        // Normalize only optional allocation-quality search; mandatory
        // verification, allocation and encoding checks stay enabled.
        env.remove("TCG_AY_REGALLOC");
        let prepared: Vec<_> = functions
            .iter()
            .map(|func| {
                pipeline
                    .prepare_function(func)
                    .expect("prepare CG function")
            })
            .collect();
        pipeline
            .compile_module_with_globals(&prepared, globals)
            .expect("compile CG Mach-O object")
    })
}

/// `cg_optind_{addr,read,write}` reach libSystem's `optind` through the GOT.
fn data_import_object(opt_level: OptLevel) -> Vec<u8> {
    let extern_ref = || Opcode::ExternRef {
        name: "optind".into(),
    };
    let functions = [
        lower_function(
            "cg_optind_addr",
            vec![],
            vec![LowerType::I64],
            vec![
                inst(extern_ref(), vec![], vec![Value(0)]),
                inst(Opcode::Return, vec![Value(0)], vec![]),
            ],
        ),
        lower_function(
            "cg_optind_read",
            vec![],
            vec![LowerType::I32],
            vec![
                inst(extern_ref(), vec![], vec![Value(0)]),
                inst(
                    Opcode::Load {
                        ty: LowerType::I32,
                        align: Some(4),
                    },
                    vec![Value(0)],
                    vec![Value(1)],
                ),
                inst(Opcode::Return, vec![Value(1)], vec![]),
            ],
        ),
        lower_function(
            "cg_optind_write",
            vec![LowerType::I32],
            vec![],
            vec![
                inst(extern_ref(), vec![], vec![Value(1)]),
                inst(
                    Opcode::Store {
                        ty: LowerType::I32,
                        align: Some(4),
                    },
                    vec![Value(0), Value(1)],
                    vec![],
                ),
                inst(Opcode::Return, vec![], vec![]),
            ],
        ),
    ];
    compile(
        &darwin_pipeline(opt_level),
        &functions,
        &[global("optind", vec![], false, true, 4)],
    )
}

/// `cg_tls_addr` returns this thread's `cg_tls_counter` (initially 7) through
/// the Darwin TLV descriptor.
fn tls_object(opt_level: OptLevel) -> Vec<u8> {
    let function = lower_function(
        "cg_tls_addr",
        vec![],
        vec![LowerType::I64],
        vec![
            inst(
                Opcode::TlsRef {
                    name: "cg_tls_counter".into(),
                    model: TlsModel::Tlv,
                    local_exec_offset: None,
                },
                vec![],
                vec![Value(0)],
            ),
            inst(Opcode::Return, vec![Value(0)], vec![]),
        ],
    );
    compile(
        &darwin_pipeline(opt_level),
        &[function],
        &[global(
            "cg_tls_counter",
            TLS_INITIAL.to_le_bytes().to_vec(),
            true,
            false,
            8,
        )],
    )
}

/// `guard_target` returns 42 under a stack guard loaded through the GOT; the
/// corrupt variant overwrites its canary so the epilogue must fail.
fn stack_guard_object(corrupt: bool, define_guard: bool) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        let mut func = MachFunction::new(
            "guard_target".into(),
            IrSignature::new(vec![], vec![IrType::I64]),
        );
        func.stack_protector = StackProtectorMode::StackGuard;
        frame::ensure_stack_protector_slot(&mut func).unwrap();
        if corrupt {
            let store = func.push_inst(MachInst::new(
                Op::StrRI,
                vec![
                    Operand::PReg(XZR),
                    Operand::StackSlot(func.stack_protector_slot.unwrap()),
                ],
            ));
            func.append_inst(func.entry, store);
        }
        let mov = func.push_inst(MachInst::new(
            Op::Movz,
            vec![Operand::PReg(X0), Operand::Imm(42)],
        ));
        func.append_inst(func.entry, mov);
        let ret = func.push_inst(MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]));
        func.append_inst(func.entry, ret);
        let pipeline = darwin_pipeline(OptLevel::O0);
        pipeline.prepare_ir_function(&mut func).unwrap();
        let globals = if define_guard {
            vec![global(
                "__stack_chk_guard",
                0x1234_5678_9abc_def0_u64.to_le_bytes().to_vec(),
                false,
                false,
                8,
            )]
        } else {
            vec![]
        };
        pipeline
            .compile_module_with_globals(&[func], &globals)
            .unwrap()
    })
}

/// A dylib body: `cg_add`, exported data `cg_counter` (5) and its address,
/// an exported thread-local `cg_tls_counter` (7) and its address, and a
/// libSystem `optind` read through the GOT.
fn dylib_object(opt_level: OptLevel) -> Vec<u8> {
    let functions = [
        lower_function(
            "cg_add",
            vec![LowerType::I64, LowerType::I64],
            vec![LowerType::I64],
            vec![
                inst(Opcode::Iadd, vec![Value(0), Value(1)], vec![Value(2)]),
                inst(Opcode::Return, vec![Value(2)], vec![]),
            ],
        ),
        lower_function(
            "cg_counter_addr",
            vec![],
            vec![LowerType::I64],
            vec![
                inst(
                    Opcode::GlobalRef {
                        name: "cg_counter".into(),
                    },
                    vec![],
                    vec![Value(0)],
                ),
                inst(Opcode::Return, vec![Value(0)], vec![]),
            ],
        ),
        lower_function(
            "cg_tls_addr",
            vec![],
            vec![LowerType::I64],
            vec![
                inst(
                    Opcode::TlsRef {
                        name: "cg_tls_counter".into(),
                        model: TlsModel::Tlv,
                        local_exec_offset: None,
                    },
                    vec![],
                    vec![Value(0)],
                ),
                inst(Opcode::Return, vec![Value(0)], vec![]),
            ],
        ),
        lower_function(
            "cg_optind_read",
            vec![],
            vec![LowerType::I32],
            vec![
                inst(
                    Opcode::ExternRef {
                        name: "optind".into(),
                    },
                    vec![],
                    vec![Value(0)],
                ),
                inst(
                    Opcode::Load {
                        ty: LowerType::I32,
                        align: Some(4),
                    },
                    vec![Value(0)],
                    vec![Value(1)],
                ),
                inst(Opcode::Return, vec![Value(1)], vec![]),
            ],
        ),
    ];
    compile(
        &darwin_pipeline(opt_level),
        &functions,
        &[
            global("cg_counter", 5i64.to_le_bytes().to_vec(), false, false, 8),
            global(
                "cg_tls_counter",
                TLS_INITIAL.to_le_bytes().to_vec(),
                true,
                false,
                8,
            ),
            global("optind", vec![], false, true, 4),
        ],
    )
}

/// A dylib-only `_main` so object-level links need no C compiler.
fn main_object() -> ParsedObject {
    let mut writer = MachOWriter::new();
    writer.add_text_section(&0xD65F_03C0u32.to_le_bytes());
    writer.add_symbol("_main", 1, 0, true).unwrap();
    MachOParser::parse(&writer.write().unwrap()).unwrap()
}

fn libsystem(extra: &[&str]) -> DylibConfig {
    let mut config = DylibConfig::with_libsystem();
    config.dylibs[0]
        .symbols
        .extend(extra.iter().map(|symbol| symbol.to_string()));
    config
}

// ---------------------------------------------------------------------------
// Independent image reader
// ---------------------------------------------------------------------------

const MH_EXECUTE: u32 = 0x2;
const MH_DYLIB: u32 = 0x6;
const MH_HAS_TLV_DESCRIPTORS: u32 = 0x0080_0000;
const SG_READ_ONLY: u32 = 0x10;
const S_NON_LAZY_SYMBOL_POINTERS: u32 = 0x6;
const S_THREAD_LOCAL_REGULAR: u32 = 0x11;
const S_THREAD_LOCAL_VARIABLES: u32 = 0x13;
const S_THREAD_LOCAL_VARIABLE_POINTERS: u32 = 0x14;
const LC_SEGMENT_64: u32 = 0x19;
const LC_DYLD_CHAINED_FIXUPS: u32 = 0x8000_0034;
const PAGE_SIZE: u64 = 0x4000;

fn u16_at(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes(bytes[offset..offset + 2].try_into().unwrap())
}

fn u32_at(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

fn name16(bytes: &[u8], offset: usize) -> String {
    let raw = &bytes[offset..offset + 16];
    let end = raw.iter().position(|&byte| byte == 0).unwrap_or(16);
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

fn cstring(bytes: &[u8], offset: usize) -> String {
    let end = bytes[offset..].iter().position(|&byte| byte == 0).unwrap() + offset;
    String::from_utf8_lossy(&bytes[offset..end]).into_owned()
}

#[derive(Debug, Clone)]
struct Segment {
    name: String,
    vmaddr: u64,
    fileoff: u64,
    filesize: u64,
    flags: u32,
}

#[derive(Debug, Clone)]
struct Section {
    name: String,
    segment: String,
    addr: u64,
    size: u64,
    flags: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Fixup {
    Rebase(u64),
    Bind(String),
}

struct Image {
    bytes: Vec<u8>,
    filetype: u32,
    flags: u32,
    segments: Vec<Segment>,
    sections: Vec<Section>,
    fixups: Vec<(u64, Fixup)>,
}

impl Image {
    fn read(bytes: Vec<u8>) -> Self {
        assert_eq!(u32_at(&bytes, 0), 0xFEED_FACF);
        let filetype = u32_at(&bytes, 12);
        let flags = u32_at(&bytes, 24);
        let mut segments = Vec::new();
        let mut sections = Vec::new();
        let mut fixups_offset = None;
        let mut offset = 32;
        for _ in 0..u32_at(&bytes, 16) {
            let cmd = u32_at(&bytes, offset);
            if cmd == LC_SEGMENT_64 {
                segments.push(Segment {
                    name: name16(&bytes, offset + 8),
                    vmaddr: u64_at(&bytes, offset + 24),
                    fileoff: u64_at(&bytes, offset + 40),
                    filesize: u64_at(&bytes, offset + 48),
                    flags: u32_at(&bytes, offset + 68),
                });
                for index in 0..u32_at(&bytes, offset + 64) as usize {
                    let header = offset + 72 + index * 80;
                    sections.push(Section {
                        name: name16(&bytes, header),
                        segment: name16(&bytes, header + 16),
                        addr: u64_at(&bytes, header + 32),
                        size: u64_at(&bytes, header + 40),
                        flags: u32_at(&bytes, header + 64),
                    });
                }
            } else if cmd == LC_DYLD_CHAINED_FIXUPS {
                fixups_offset = Some(u32_at(&bytes, offset + 8) as usize);
            }
            offset += u32_at(&bytes, offset + 4) as usize;
        }
        let fixups = decode_fixups(&bytes, &segments, fixups_offset.expect("chained fixups"));
        Self {
            bytes,
            filetype,
            flags,
            segments,
            sections,
            fixups,
        }
    }

    fn section(&self, segment: &str, name: &str) -> &Section {
        let mut matches = self
            .sections
            .iter()
            .filter(|section| section.segment == segment && section.name == name);
        let section = matches
            .next()
            .unwrap_or_else(|| panic!("missing section {segment},{name}"));
        assert!(matches.next().is_none(), "duplicate {segment},{name}");
        section
    }

    fn segment(&self, name: &str) -> &Segment {
        self.segments
            .iter()
            .find(|segment| segment.name == name)
            .unwrap_or_else(|| panic!("missing segment {name}"))
    }

    fn fixup_at(&self, address: u64) -> &Fixup {
        let mut matches = self.fixups.iter().filter(|(at, _)| *at == address);
        let (_, fixup) = matches
            .next()
            .unwrap_or_else(|| panic!("no chained fixup at {address:#x}"));
        assert!(matches.next().is_none());
        fixup
    }

    fn read_at(&self, address: u64, len: usize) -> &[u8] {
        let segment = self
            .segments
            .iter()
            .find(|segment| (segment.vmaddr..segment.vmaddr + segment.filesize).contains(&address))
            .expect("address in file-backed segment");
        let offset = (segment.fileoff + address - segment.vmaddr) as usize;
        &self.bytes[offset..offset + len]
    }

    fn instruction(&self, address: u64) -> u32 {
        u32::from_le_bytes(self.read_at(address, 4).try_into().unwrap())
    }
}

/// DYLD_CHAINED_PTR_64 chains, decoded per `<mach-o/fixup-chains.h>`.
fn decode_fixups(bytes: &[u8], segments: &[Segment], start: usize) -> Vec<(u64, Fixup)> {
    let starts = start + u32_at(bytes, start + 4) as usize;
    let imports = start + u32_at(bytes, start + 8) as usize;
    let symbols = start + u32_at(bytes, start + 12) as usize;
    let import_count = u32_at(bytes, start + 16) as usize;
    assert_eq!(u32_at(bytes, starts) as usize, segments.len());
    let mut decoded = Vec::new();
    for (index, segment) in segments.iter().enumerate() {
        let info = u32_at(bytes, starts + 4 + index * 4) as usize;
        if info == 0 {
            continue;
        }
        let seg = starts + info;
        assert_eq!(u16_at(bytes, seg + 4), PAGE_SIZE as u16);
        assert_eq!(u16_at(bytes, seg + 6), 2, "DYLD_CHAINED_PTR_64");
        let text = segments
            .iter()
            .find(|segment| segment.name == "__TEXT")
            .expect("__TEXT");
        assert_eq!(u64_at(bytes, seg + 8), segment.vmaddr - text.vmaddr);
        for page in 0..u16_at(bytes, seg + 20) as u64 {
            let first = u16_at(bytes, seg + 22 + page as usize * 2);
            if first == 0xFFFF {
                continue;
            }
            let mut offset = page * PAGE_SIZE + u64::from(first);
            loop {
                assert!(offset + 8 <= segment.filesize);
                let raw = u64_at(bytes, (segment.fileoff + offset) as usize);
                let fixup = if raw >> 63 == 1 {
                    let ordinal = (raw & 0xFF_FFFF) as usize;
                    assert!(ordinal < import_count);
                    assert_eq!((raw >> 24) & 0xFF, 0, "no bind addends here");
                    let entry = u32_at(bytes, imports + ordinal * 4);
                    assert_eq!(entry & 0xFF, 1, "libSystem is dylib ordinal 1");
                    Fixup::Bind(cstring(bytes, symbols + (entry >> 9) as usize))
                } else {
                    Fixup::Rebase(raw & ((1 << 36) - 1))
                };
                decoded.push((segment.vmaddr + offset, fixup));
                let next = (raw >> 51) & 0xFFF;
                if next == 0 {
                    break;
                }
                offset += next * 4;
                assert_eq!(offset / PAGE_SIZE, page);
            }
        }
    }
    decoded
}

/// Decode `ADRP Xd, page` + `LDR Xt, [Xd, #imm]` and return the loaded slot.
fn adrp_ldr_target(image: &Image, adrp_address: u64, ldr_address: u64) -> u64 {
    let adrp = image.instruction(adrp_address);
    let ldr = image.instruction(ldr_address);
    assert_eq!(
        adrp & 0x9F00_0000,
        0x9000_0000,
        "ADRP expected: {adrp:#010x}"
    );
    assert_eq!(
        ldr & 0xFFC0_0000,
        0xF940_0000,
        "64-bit LDR expected: {ldr:#010x}"
    );
    assert_eq!(
        (ldr >> 5) & 0x1F,
        adrp & 0x1F,
        "LDR base must be the ADRP result"
    );
    let immediate = (((adrp >> 5) & 0x7FFFF) << 2) | ((adrp >> 29) & 3);
    let pages = (i64::from(immediate) << 43) >> 43;
    let page = ((adrp_address & !0xFFF) as i64 + pages * 4096) as u64;
    page + u64::from((ldr >> 10) & 0xFFF) * 8
}

/// Address of `objects[0]`'s `__text` inside `image`. Stubs follow all input
/// text, so the slot-free layout places input sections exactly as the link.
fn cg_text_address(image: &Image, objects: &[ParsedObject]) -> u64 {
    let text_index = objects[0]
        .sections
        .iter()
        .position(|section| section.name == "__text")
        .expect("CG __text");
    let layout = lay_out_sections(objects, image.section("__TEXT", "__text").addr).unwrap();
    layout.section_addrs[0][text_index]
}

/// Every `(ADRP, LDR)` site of `kind` in the CG object's `__text`.
fn relocation_pairs(
    object: &ParsedObject,
    page: AArch64RelocKind,
    pageoff: AArch64RelocKind,
) -> Vec<(u64, u64, String)> {
    let text = object
        .sections
        .iter()
        .find(|section| section.name == "__text")
        .expect("CG __text");
    let name = |index: u32| object.symbols[index as usize].name.to_string();
    let pages: Vec<_> = text
        .relocations
        .iter()
        .filter(|reloc| reloc.kind == page)
        .collect();
    let offs: Vec<_> = text
        .relocations
        .iter()
        .filter(|reloc| reloc.kind == pageoff)
        .collect();
    assert_eq!(pages.len(), offs.len(), "{page:?}/{pageoff:?} must pair");
    let mut pairs: Vec<_> = pages
        .iter()
        .map(|adrp| {
            let ldr = offs
                .iter()
                .filter(|ldr| ldr.symbol_index == adrp.symbol_index && ldr.offset > adrp.offset)
                .min_by_key(|ldr| ldr.offset)
                .expect("LDR partner");
            (
                u64::from(adrp.offset),
                u64::from(ldr.offset),
                name(adrp.symbol_index),
            )
        })
        .collect();
    pairs.sort();
    pairs
}

// ---------------------------------------------------------------------------
// Object-level evidence (every host)
// ---------------------------------------------------------------------------

#[test]
fn data_import_got_loads_bind_libsystem_optind_on_every_opt_level() {
    for opt_level in OPT_LEVELS {
        let object = MachOParser::parse(&data_import_object(opt_level)).unwrap();
        let pairs = relocation_pairs(
            &object,
            AArch64RelocKind::GotLoadPage21,
            AArch64RelocKind::GotLoadPageoff12,
        );
        assert!(
            pairs.len() >= 3,
            "{opt_level:?}: every function loads the GOT"
        );
        let objects = [object, main_object()];
        let image = Image::read(link_with_dylibs(&objects, &libsystem(&["_optind"])).unwrap());
        let got = image.section("__DATA_CONST", "__got");
        assert_eq!(got.flags, S_NON_LAZY_SYMBOL_POINTERS);
        assert_eq!(image.segment("__DATA_CONST").flags, SG_READ_ONLY);
        assert_eq!(got.size, 8, "{opt_level:?}: one deduplicated slot");
        assert_eq!(image.fixup_at(got.addr), &Fixup::Bind("_optind".into()));
        let text = cg_text_address(&image, &objects);
        for (adrp, ldr, symbol) in pairs {
            assert_eq!(symbol, "_optind");
            assert_eq!(adrp_ldr_target(&image, text + adrp, text + ldr), got.addr);
        }
    }
}

#[test]
fn defined_stack_guard_got_slot_is_rebased_to_the_guard() {
    let object = MachOParser::parse(&stack_guard_object(false, true)).unwrap();
    let pairs = relocation_pairs(
        &object,
        AArch64RelocKind::GotLoadPage21,
        AArch64RelocKind::GotLoadPageoff12,
    );
    assert!(!pairs.is_empty());
    let guard_value = 0x1234_5678_9abc_def0_u64.to_le_bytes();
    // `___stack_chk_fail` comes from libSystem through a stub.
    let objects = [object, main_object()];
    let image = Image::read(link_with_dylibs(&objects, &DylibConfig::with_libsystem()).unwrap());
    let got = image.section("__DATA_CONST", "__got");
    let text = cg_text_address(&image, &objects);
    let data = image.section("__DATA", "__data");
    let guard_slot = adrp_ldr_target(&image, text + pairs[0].0, text + pairs[0].1);
    for (adrp, ldr, symbol) in &pairs {
        assert_eq!(symbol, "___stack_chk_guard");
        assert_eq!(adrp_ldr_target(&image, text + adrp, text + ldr), guard_slot);
    }
    assert!((got.addr..got.addr + got.size).contains(&guard_slot));
    let Fixup::Rebase(guard) = image.fixup_at(guard_slot).clone() else {
        panic!("a defined guard must be rebased, not bound");
    };
    assert!((data.addr..data.addr + data.size).contains(&guard));
    assert_eq!(image.read_at(guard, 8), guard_value);
    // The other GOT slot backs the ___stack_chk_fail stub.
    assert!(
        image
            .fixups
            .iter()
            .any(|(_, fixup)| fixup == &Fixup::Bind("___stack_chk_fail".into()))
    );
}

#[test]
fn tlv_descriptor_template_and_pointer_slot_resolve_on_every_opt_level() {
    for opt_level in OPT_LEVELS {
        let object = MachOParser::parse(&tls_object(opt_level)).unwrap();
        let pairs = relocation_pairs(
            &object,
            AArch64RelocKind::TlvpLoadPage21,
            AArch64RelocKind::TlvpLoadPageoff12,
        );
        assert_eq!(pairs.len(), 1, "{opt_level:?}");
        let objects = [object, main_object()];
        let image =
            Image::read(link_with_dylibs(&objects, &DylibConfig::with_libsystem()).unwrap());
        assert_eq!(image.filetype, MH_EXECUTE);
        assert_ne!(image.flags & MH_HAS_TLV_DESCRIPTORS, 0);
        let pointers = image.section("__DATA_CONST", "__thread_ptrs");
        let descriptors = image.section("__DATA", "__thread_vars");
        let template = image.section("__DATA", "__thread_data");
        assert_eq!(pointers.flags, S_THREAD_LOCAL_VARIABLE_POINTERS);
        assert_eq!(descriptors.flags, S_THREAD_LOCAL_VARIABLES);
        assert_eq!(template.flags, S_THREAD_LOCAL_REGULAR);
        assert_eq!(descriptors.size, 24);
        // The TLVP pair loads the pointer slot; dyld rebases it to the
        // descriptor. No instruction is relaxed.
        let text = cg_text_address(&image, &objects);
        let (adrp, ldr, symbol) = &pairs[0];
        assert_eq!(symbol, "_cg_tls_counter");
        assert_eq!(
            adrp_ldr_target(&image, text + adrp, text + ldr),
            pointers.addr
        );
        assert_eq!(
            image.fixup_at(pointers.addr),
            &Fixup::Rebase(descriptors.addr)
        );
        // Descriptor: thunk bound to __tlv_bootstrap, key 0, template offset 0.
        assert_eq!(
            image.fixup_at(descriptors.addr),
            &Fixup::Bind("__tlv_bootstrap".into())
        );
        assert_eq!(image.read_at(descriptors.addr + 8, 16), [0u8; 16]);
        assert_eq!(image.read_at(template.addr, 8), TLS_INITIAL.to_le_bytes());
    }
}

#[test]
fn cg_dylib_binds_its_imports_and_rebases_its_own_slots() {
    for opt_level in OPT_LEVELS {
        let object = MachOParser::parse(&dylib_object(opt_level)).unwrap();
        let image = Image::read(
            link_dylib(
                std::slice::from_ref(&object),
                &libsystem(&["_optind"]),
                "@executable_path/libcg.dylib",
            )
            .unwrap(),
        );
        assert_eq!(image.filetype, MH_DYLIB, "{opt_level:?}");
        assert_ne!(image.flags & MH_HAS_TLV_DESCRIPTORS, 0);
        assert_eq!(image.segment("__TEXT").vmaddr, 0);
        let got = image.section("__DATA_CONST", "__got");
        let pointers = image.section("__DATA_CONST", "__thread_ptrs");
        let vars = image.section("__DATA", "__thread_vars");
        assert_eq!(image.fixup_at(got.addr), &Fixup::Bind("_optind".into()));
        assert_eq!(image.fixup_at(pointers.addr), &Fixup::Rebase(vars.addr));
        assert_eq!(
            image.fixup_at(vars.addr),
            &Fixup::Bind("__tlv_bootstrap".into())
        );
        let text = cg_text_address_dylib(&image, &object);
        let (adrp, ldr, _) = &relocation_pairs(
            &object,
            AArch64RelocKind::TlvpLoadPage21,
            AArch64RelocKind::TlvpLoadPageoff12,
        )[0];
        assert_eq!(
            adrp_ldr_target(&image, text + adrp, text + ldr),
            pointers.addr
        );
    }
}

/// `object`'s `__text` address inside a dylib image linked from it alone.
fn cg_text_address_dylib(image: &Image, object: &ParsedObject) -> u64 {
    cg_text_address(image, std::slice::from_ref(object))
}

#[test]
fn cg_objects_refuse_malformed_got_and_tlv_relocations_by_name() {
    let base = MachOParser::parse(&data_import_object(OptLevel::O0)).unwrap();
    let config = libsystem(&["_optind"]);
    let text_index = base
        .sections
        .iter()
        .position(|section| section.name == "__text")
        .unwrap();
    let find = |object: &ParsedObject, kind| {
        object.sections[text_index]
            .relocations
            .iter()
            .position(|reloc| reloc.kind == kind)
            .unwrap()
    };
    let mutate = |edit: &dyn Fn(&mut ParsedObject)| {
        let mut object = base.clone();
        edit(&mut object);
        link_with_dylibs(&[object, main_object()], &config).unwrap_err()
    };

    // GOT_LOAD_PAGEOFF12 must patch a 64-bit LDR, never an ADD it would relax.
    let error = mutate(&|object| {
        let index = find(object, AArch64RelocKind::GotLoadPageoff12);
        let offset = object.sections[text_index].relocations[index].offset as usize;
        let data = &mut object.sections[text_index].data;
        data[offset..offset + 4].copy_from_slice(&0x9100_0000u32.to_le_bytes());
    });
    assert!(
        matches!(
            error,
            LinkerError::RelocationInstructionMismatch {
                kind: AArch64RelocKind::GotLoadPageoff12,
                ..
            }
        ),
        "{error:?}"
    );
    // GOT loads must name a symbol and keep their pc-relative shape.
    let error = mutate(&|object| {
        let index = find(object, AArch64RelocKind::GotLoadPage21);
        object.sections[text_index].relocations[index].is_extern = false;
        object.sections[text_index].relocations[index].symbol_index = 1;
    });
    assert!(
        matches!(error, LinkerError::MalformedRelocation(_)),
        "{error:?}"
    );
    let error = mutate(&|object| {
        let index = find(object, AArch64RelocKind::GotLoadPage21);
        object.sections[text_index].relocations[index].pc_relative = false;
    });
    assert!(
        matches!(error, LinkerError::MalformedRelocation(_)),
        "{error:?}"
    );
    // A direct PAGE21 to a dylib import cannot be satisfied without text
    // relocations; it is refused rather than pointed at a stub.
    let error = mutate(&|object| {
        let index = find(object, AArch64RelocKind::GotLoadPage21);
        object.sections[text_index].relocations[index].kind = AArch64RelocKind::Page21;
    });
    assert!(
        matches!(error, LinkerError::DirectImportReference { ref symbol, .. } if symbol == "_optind"),
        "{error:?}"
    );
    // pc-relative UNSIGNED is not an arm64 Mach-O relocation.
    let error = mutate(&|object| {
        let index = find(object, AArch64RelocKind::GotLoadPage21);
        let reloc = &mut object.sections[text_index].relocations[index];
        reloc.kind = AArch64RelocKind::Unsigned;
        reloc.length = 2;
    });
    assert!(
        matches!(error, LinkerError::PcRelativeUnsigned { .. }),
        "{error:?}"
    );

    // TLVP loads must name a TLV descriptor, and nothing else may.
    let tls = MachOParser::parse(&tls_object(OptLevel::O0)).unwrap();
    let tls_text = tls
        .sections
        .iter()
        .position(|section| section.name == "__text")
        .unwrap();
    let tlvp = tls.sections[tls_text]
        .relocations
        .iter()
        .position(|reloc| reloc.kind == AArch64RelocKind::TlvpLoadPage21)
        .unwrap();
    let mut direct = tls.clone();
    direct.sections[tls_text].relocations[tlvp].kind = AArch64RelocKind::Page21;
    let error =
        link_with_dylibs(&[direct, main_object()], &DylibConfig::with_libsystem()).unwrap_err();
    assert!(matches!(error, LinkerError::ThreadLocal(_)), "{error:?}");
    let mut wrong_target = tls.clone();
    let main_symbol = wrong_target
        .symbols
        .iter()
        .position(|symbol| symbol.name == "_cg_tls_addr")
        .unwrap();
    for reloc in &mut wrong_target.sections[tls_text].relocations {
        if matches!(
            reloc.kind,
            AArch64RelocKind::TlvpLoadPage21 | AArch64RelocKind::TlvpLoadPageoff12
        ) {
            reloc.symbol_index = main_symbol as u32;
        }
    }
    let error = link_with_dylibs(
        &[wrong_target, main_object()],
        &DylibConfig::with_libsystem(),
    )
    .unwrap_err();
    assert!(matches!(error, LinkerError::ThreadLocal(_)), "{error:?}");
    // A descriptor whose thunk is not bound to __tlv_bootstrap is malformed.
    let mut no_thunk = tls.clone();
    let vars = no_thunk
        .sections
        .iter()
        .position(|section| section.name == "__thread_vars")
        .unwrap();
    no_thunk.sections[vars]
        .relocations
        .retain(|reloc| reloc.offset % 24 != 0);
    let error =
        link_with_dylibs(&[no_thunk, main_object()], &DylibConfig::with_libsystem()).unwrap_err();
    assert!(matches!(error, LinkerError::ThreadLocal(_)), "{error:?}");
    // Without libSystem there is no __tlv_bootstrap to bind.
    let error = link(&[tls, main_object()]).unwrap_err();
    assert!(
        matches!(error, LinkerError::UndefinedSymbol(ref name) if name == "__tlv_bootstrap"),
        "{error:?}"
    );
}

// ---------------------------------------------------------------------------
// Native twins (macOS AArch64)
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native {
    use super::*;
    use common::rosetta::{
        TimedCommandOutput, codegen_run_timeout, command_output_with_timeout,
        run_executable_with_timeout,
    };
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Duration;

    const TLS_DRIVER: &str = r#"
#include <pthread.h>
#include <stdio.h>

extern long *cg_tls_addr(void);
__thread long drv_tls_zero;
__thread long drv_tls_init = 99;

struct probe { long *addr; long initial; long after; long zero; long init; };

static void run(struct probe *p, long value) {
    p->addr = cg_tls_addr();
    p->initial = *p->addr;
    *p->addr = value;
    drv_tls_zero += value;
    drv_tls_init += value;
    p->after = *cg_tls_addr();
    p->zero = drv_tls_zero;
    p->init = drv_tls_init;
}

static void *worker(void *arg) {
    run((struct probe *)arg, 2000);
    return 0;
}

int main(void) {
    struct probe main_probe, worker_probe;
    pthread_t thread;
    run(&main_probe, 1000);
    if (pthread_create(&thread, 0, worker, &worker_probe) != 0) return 90;
    if (pthread_join(thread, 0) != 0) return 91;
    long main_again = *cg_tls_addr();
    printf("main initial=%ld after=%ld zero=%ld init=%ld again=%ld\n",
           main_probe.initial, main_probe.after, main_probe.zero, main_probe.init,
           main_again);
    printf("worker initial=%ld after=%ld zero=%ld init=%ld\n",
           worker_probe.initial, worker_probe.after, worker_probe.zero,
           worker_probe.init);
    printf("distinct=%d\n", main_probe.addr != worker_probe.addr);
    return main_probe.initial == 7 && worker_probe.initial == 7 && main_again == 1000
        && worker_probe.after == 2000 && main_probe.addr != worker_probe.addr ? 0 : 3;
}
"#;

    const DATA_IMPORT_DRIVER: &str = r#"
#include <stdio.h>
#include <unistd.h>

extern int *cg_optind_addr(void);
extern int cg_optind_read(void);
extern void cg_optind_write(int);

int main(void) {
    int same = cg_optind_addr() == &optind;
    int initial = cg_optind_read();
    cg_optind_write(37);
    int seen = optind;
    int reread = cg_optind_read();
    printf("same=%d initial=%d seen=%d reread=%d\n", same, initial, seen, reread);
    return same && initial == 1 && seen == 37 && reread == 37 ? 0 : 3;
}
"#;

    const GUARD_DRIVER_LIBSYSTEM: &str = r#"
extern long guard_target(void);
int main(void) { return guard_target() == 42 ? 0 : 1; }
"#;

    const GUARD_DRIVER_LOCAL_FAIL: &str = r#"
#include <stdlib.h>
extern long guard_target(void);
__attribute__((noreturn)) void __stack_chk_fail(void) { _Exit(87); }
int main(void) { return guard_target() == 42 ? 0 : 1; }
"#;

    const DRIVER_IMPORTS: &[&str] = &["_optind", "_pthread_create", "_pthread_join", "__Exit"];

    fn checked(command: &mut Command, what: &str) -> TimedCommandOutput {
        let output = command_output_with_timeout(command, Duration::from_secs(60))
            .unwrap_or_else(|error| panic!("{what}: {error}"));
        assert!(!output.timed_out, "{what} timed out");
        assert!(
            output.output.status.success(),
            "{what} failed: {}",
            String::from_utf8_lossy(&output.output.stderr)
        );
        output
    }

    fn make_executable(path: &Path) {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    /// Imports each image binds, as reported by the platform's `dyld_info`.
    fn dyld_binds(path: &Path) -> BTreeSet<String> {
        let output = checked(
            Command::new("/usr/bin/dyld_info").arg("-fixups").arg(path),
            "dyld_info -fixups",
        );
        String::from_utf8_lossy(&output.output.stdout)
            .lines()
            .filter_map(|line| {
                let fields: Vec<_> = line.split_whitespace().collect();
                let bind = fields.iter().position(|field| *field == "bind")?;
                let target = fields.get(bind + 1)?;
                Some(target.rsplit('/').next()?.to_string())
            })
            .collect()
    }

    fn validate(path: &Path) {
        let output = checked(
            Command::new("/usr/bin/dyld_info")
                .arg("-validate_only")
                .arg(path),
            "dyld_info -validate_only",
        );
        let report = String::from_utf8_lossy(&output.output.stdout).to_string()
            + &String::from_utf8_lossy(&output.output.stderr);
        assert!(
            !report.to_ascii_lowercase().contains("malformed")
                && !report.to_ascii_lowercase().contains("error"),
            "dyld_info rejected {}: {report}",
            path.display()
        );
    }

    struct Twins {
        standalone: TimedCommandOutput,
        ld64: TimedCommandOutput,
        standalone_path: PathBuf,
        ld64_path: PathBuf,
        _directory: tempfile::TempDir,
    }

    /// Compile `driver`, link it with `cg_objects` standalone and with ld64,
    /// run both, and validate both images with `dyld_info`.
    fn link_twins(label: &str, driver: &str, cg_objects: &[Vec<u8>]) -> Twins {
        link_twins_after(label, &[], driver, cg_objects)
    }

    /// [`link_twins`] with `leading` objects placed before the driver in
    /// both links, so they come first in every merged output section.
    fn link_twins_after(
        label: &str,
        leading: &[Vec<u8>],
        driver: &str,
        cg_objects: &[Vec<u8>],
    ) -> Twins {
        let directory = tempfile::Builder::new()
            .prefix(&format!("trust-cg-macho-standalone-{label}-"))
            .tempdir()
            .unwrap();
        let source = directory.path().join("driver.c");
        let driver_object = directory.path().join("driver.o");
        std::fs::write(&source, driver).unwrap();
        checked(
            Command::new("/usr/bin/clang")
                .args(["-O1", "-fno-stack-protector", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&driver_object),
            "clang -c driver",
        );
        let mut paths = Vec::new();
        let mut parsed = Vec::new();
        for (index, bytes) in leading.iter().enumerate() {
            let path = directory.path().join(format!("leading{index}.o"));
            std::fs::write(&path, bytes).unwrap();
            parsed.push(MachOParser::parse(bytes).unwrap());
            paths.push(path);
        }
        paths.push(driver_object.clone());
        parsed.push(MachOParser::parse(&std::fs::read(&driver_object).unwrap()).unwrap());
        for (index, bytes) in cg_objects.iter().enumerate() {
            let path = directory.path().join(format!("cg{index}.o"));
            std::fs::write(&path, bytes).unwrap();
            parsed.push(MachOParser::parse(bytes).unwrap());
            paths.push(path);
        }
        let standalone_path = directory.path().join("standalone");
        let image = link_with_dylibs(&parsed, &libsystem(DRIVER_IMPORTS))
            .unwrap_or_else(|error| panic!("{label}: standalone link failed: {error}"));
        std::fs::write(&standalone_path, image).unwrap();
        make_executable(&standalone_path);
        let ld64_path = directory.path().join("ld64");
        checked(
            Command::new("/usr/bin/clang")
                .args(&paths)
                .arg("-o")
                .arg(&ld64_path),
            "ld64 twin link",
        );
        validate(&standalone_path);
        validate(&ld64_path);
        let run = |path: &Path| {
            let output = run_executable_with_timeout(path, codegen_run_timeout()).unwrap();
            assert!(!output.timed_out, "{label}: {} timed out", path.display());
            output
        };
        Twins {
            standalone: run(&standalone_path),
            ld64: run(&ld64_path),
            standalone_path,
            ld64_path,
            _directory: directory,
        }
    }

    fn assert_twins_agree(label: &str, twins: &Twins, expected_status: i32) {
        for (name, output) in [("standalone", &twins.standalone), ("ld64", &twins.ld64)] {
            assert_eq!(
                output.output.status.code(),
                Some(expected_status),
                "{label} {name}: stdout={} stderr={}",
                String::from_utf8_lossy(&output.output.stdout),
                String::from_utf8_lossy(&output.output.stderr)
            );
        }
        assert_eq!(
            twins.standalone.output.stdout, twins.ld64.output.stdout,
            "{label}: standalone and ld64 twins must print the same result"
        );
        assert_eq!(
            dyld_binds(&twins.standalone_path),
            dyld_binds(&twins.ld64_path),
            "{label}: both images must bind the same imports"
        );
    }

    #[test]
    fn stack_guard_via_got_executes_like_its_ld64_twin() {
        // Guard and failure handler from libSystem: GOT bind + stub. A
        // corrupted canary aborts (SIGABRT, reported as 128 + 6).
        for (corrupt, status) in [(false, 0), (true, 134)] {
            let label = format!("guard-libsystem-corrupt-{corrupt}");
            let twins = link_twins(
                &label,
                GUARD_DRIVER_LIBSYSTEM,
                &[stack_guard_object(corrupt, false)],
            );
            assert_twins_agree(&label, &twins, status);
            let binds = dyld_binds(&twins.standalone_path);
            assert!(binds.contains("___stack_chk_guard"), "{binds:?}");
        }
        // Guard defined in the CG object: its GOT slot is rebased; the driver's
        // own __stack_chk_fail exits 87 on corruption.
        for (corrupt, status) in [(false, 0), (true, 87)] {
            let label = format!("guard-local-corrupt-{corrupt}");
            let twins = link_twins(
                &label,
                GUARD_DRIVER_LOCAL_FAIL,
                &[stack_guard_object(corrupt, true)],
            );
            assert_twins_agree(&label, &twins, status);
            assert!(!dyld_binds(&twins.standalone_path).contains("___stack_chk_guard"));
        }
    }

    #[test]
    fn tls_global_is_per_thread_like_its_ld64_twin_at_o0_through_o3() {
        for opt_level in OPT_LEVELS {
            let label = format!("tls-{opt_level:?}");
            let twins = link_twins(&label, TLS_DRIVER, &[tls_object(opt_level)]);
            assert_twins_agree(&label, &twins, 0);
            assert_eq!(
                String::from_utf8_lossy(&twins.standalone.output.stdout),
                "main initial=7 after=1000 zero=1000 init=1099 again=1000\n\
                 worker initial=7 after=2000 zero=2000 init=2099\n\
                 distinct=1\n",
                "{label}"
            );
            assert!(dyld_binds(&twins.standalone_path).contains("__tlv_bootstrap"));
        }
    }

    /// An empty `__thread_data` input aligned to 32 bytes, stricter than
    /// every non-empty TLV template it precedes.
    const EMPTY_OVERALIGNED_TLS_ASM: &str = "\
.section __DATA,__thread_data,thread_local_regular
.p2align 5
.section __TEXT,__text,regular,pure_instructions
.globl _empty_tls_marker
_empty_tls_marker:
  ret
";

    fn assemble(what: &str, source: &str) -> Vec<u8> {
        let directory = tempfile::tempdir().unwrap();
        let assembly = directory.path().join("input.s");
        let object = directory.path().join("input.o");
        std::fs::write(&assembly, source).unwrap();
        checked(
            Command::new("/usr/bin/clang")
                .arg("-c")
                .arg(&assembly)
                .arg("-o")
                .arg(&object),
            what,
        );
        std::fs::read(&object).unwrap()
    }

    #[test]
    fn empty_overaligned_leading_tls_template_keeps_descriptor_offsets_like_ld64() {
        // dyld copies each thread's template from the first emitted TLV
        // template section. An empty input section that is placed first and
        // aligned beyond every non-empty template must not move descriptor
        // offsets away from that section's start.
        let empty = assemble("clang -c empty TLV template", EMPTY_OVERALIGNED_TLS_ASM);
        let parsed = MachOParser::parse(&empty).unwrap();
        assert!(
            parsed
                .sections
                .iter()
                .any(|section| section.name == "__thread_data"
                    && section.data.is_empty()
                    && section.align == 5),
            "control: the leading object carries an empty 32-byte-aligned __thread_data"
        );
        let label = "tls-empty-overaligned-leading";
        let twins = link_twins_after(label, &[empty], TLS_DRIVER, &[tls_object(OptLevel::O0)]);
        assert_twins_agree(label, &twins, 0);
        assert_eq!(
            String::from_utf8_lossy(&twins.standalone.output.stdout),
            "main initial=7 after=1000 zero=1000 init=1099 again=1000\n\
             worker initial=7 after=2000 zero=2000 init=2099\n\
             distinct=1\n",
            "{label}"
        );
    }

    #[test]
    fn libsystem_data_import_through_got_matches_its_ld64_twin_at_o0_through_o3() {
        for opt_level in OPT_LEVELS {
            let label = format!("optind-{opt_level:?}");
            let twins = link_twins(&label, DATA_IMPORT_DRIVER, &[data_import_object(opt_level)]);
            assert_twins_agree(&label, &twins, 0);
            assert_eq!(
                String::from_utf8_lossy(&twins.standalone.output.stdout),
                "same=1 initial=1 seen=37 reread=37\n",
                "{label}"
            );
            assert!(dyld_binds(&twins.standalone_path).contains("_optind"));
        }
    }

    #[test]
    fn absolute_data_pointer_is_rebased_under_aslr_like_its_ld64_twin() {
        // `pointer` holds `&local`. Without a rebase the slid image would load
        // a stale link-time address; both twins must return 5.
        let twins = link_twins(
            "rebase",
            "static long local = 5;\nlong *pointer = &local;\n\
             int main(void) { return (int)*pointer; }\n",
            &[],
        );
        assert_twins_agree("rebase", &twins, 5);
    }

    #[test]
    fn dyld_info_validation_rejects_a_corrupted_standalone_image() {
        // Control for `validate`: the platform validator must notice a broken
        // chained-fixup pointer format in an image this linker produced.
        let mut image = link_with_dylibs(
            &[
                MachOParser::parse(&data_import_object(OptLevel::O0)).unwrap(),
                main_object(),
            ],
            &libsystem(&["_optind"]),
        )
        .unwrap();
        let mut offset = 32;
        let mut payload = None;
        for _ in 0..u32_at(&image, 16) {
            if u32_at(&image, offset) == LC_DYLD_CHAINED_FIXUPS {
                payload = Some(u32_at(&image, offset + 8) as usize);
            }
            offset += u32_at(&image, offset + 4) as usize;
        }
        let payload = payload.unwrap();
        let starts = payload + u32_at(&image, payload + 4) as usize;
        let segment = (0..u32_at(&image, starts) as usize)
            .map(|index| u32_at(&image, starts + 4 + index * 4) as usize)
            .find(|&info| info != 0)
            .expect("the GOT segment has chains");
        image[starts + segment + 6..starts + segment + 8].copy_from_slice(&99u16.to_le_bytes());
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("corrupted");
        std::fs::write(&path, &image).unwrap();
        let output = command_output_with_timeout(
            Command::new("/usr/bin/dyld_info")
                .arg("-validate_only")
                .arg(&path),
            Duration::from_secs(60),
        )
        .unwrap();
        assert!(!output.timed_out);
        assert!(!output.output.status.success(), "corruption went unnoticed");
        assert!(
            String::from_utf8_lossy(&output.output.stdout).contains("pointer_format"),
            "{}",
            String::from_utf8_lossy(&output.output.stdout)
        );
    }

    #[test]
    fn platform_linker_also_rejects_pc_relative_unsigned() {
        // The standalone refusal of pc-relative ARM64_RELOC_UNSIGNED matches
        // the platform linker: the same mutated object fails under ld64 too.
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("pointer.c");
        let object_path = directory.path().join("pointer.o");
        std::fs::write(
            &source,
            "static long local = 5;\nlong *pointer = &local;\nint main(void) { return (int)*pointer; }\n",
        )
        .unwrap();
        checked(
            Command::new("/usr/bin/clang")
                .args(["-O1", "-c"])
                .arg(&source)
                .arg("-o")
                .arg(&object_path),
            "clang -c pointer",
        );
        let mut bytes = std::fs::read(&object_path).unwrap();
        let parsed = MachOParser::parse(&bytes).unwrap();
        let data = parsed
            .sections
            .iter()
            .position(|section| section.name == "__data")
            .unwrap();
        assert!(
            link_with_dylibs(
                std::slice::from_ref(&parsed),
                &DylibConfig::with_libsystem()
            )
            .is_ok(),
            "control: the unmutated pointer links standalone"
        );
        // Set r_pcrel on the __data UNSIGNED record in the raw object.
        let mut offset = 32;
        let mut patched = 0;
        for _ in 0..u32_at(&bytes, 16) {
            if u32_at(&bytes, offset) == LC_SEGMENT_64 {
                for index in 0..u32_at(&bytes, offset + 64) as usize {
                    let header = offset + 72 + index * 80;
                    if name16(&bytes, header) == "__data" {
                        let reloff = u32_at(&bytes, header + 56) as usize;
                        for record in 0..u32_at(&bytes, header + 60) as usize {
                            let word = reloff + record * 8 + 4;
                            let raw = u32_at(&bytes, word);
                            if raw >> 28 == 0 {
                                bytes[word..word + 4]
                                    .copy_from_slice(&(raw | 1 << 24).to_le_bytes());
                                patched += 1;
                            }
                        }
                    }
                }
            }
            offset += u32_at(&bytes, offset + 4) as usize;
        }
        assert_eq!(patched, 1);
        let mutated = MachOParser::parse(&bytes).unwrap();
        assert!(mutated.sections[data].relocations[0].pc_relative);
        let error = link_with_dylibs(&[mutated], &DylibConfig::with_libsystem()).unwrap_err();
        assert!(
            matches!(error, LinkerError::PcRelativeUnsigned { .. }),
            "{error:?}"
        );
        std::fs::write(&object_path, &bytes).unwrap();
        let linked = command_output_with_timeout(
            Command::new("/usr/bin/clang")
                .arg(&object_path)
                .arg("-o")
                .arg(directory.path().join("pcrel")),
            Duration::from_secs(60),
        )
        .unwrap();
        assert!(!linked.timed_out);
        assert!(
            !linked.output.status.success(),
            "ld64 unexpectedly accepted pc-relative UNSIGNED"
        );
        assert!(
            String::from_utf8_lossy(&linked.output.stderr).contains("not supported"),
            "{}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
    }

    const DYLIB_DRIVER: &str = r#"
#include <dlfcn.h>
#include <pthread.h>
#include <stdio.h>

extern long cg_add(long, long);
extern long cg_counter;
extern long *cg_counter_addr(void);
extern long *cg_tls_addr(void);
extern __thread long cg_tls_counter;
extern int cg_optind_read(void);

static void *worker(void *arg) {
    long *slot = cg_tls_addr();
    long *out = arg;
    out[0] = *slot;
    *slot = 2000;
    out[1] = cg_tls_counter;
    out[2] = slot != &cg_tls_counter ? 1 : 0;
    out[3] = (long)slot;
    return 0;
}

int main(void) {
    long *mine = cg_tls_addr();
    long initial = *mine;
    *mine = 1000;
    long seen = cg_tls_counter;
    long worker_result[4];
    pthread_t thread;
    if (pthread_create(&thread, 0, worker, worker_result) != 0) return 90;
    if (pthread_join(thread, 0) != 0) return 91;
    void *by_name = dlsym(RTLD_DEFAULT, "cg_add");
    printf("add=%ld counter=%ld same_counter=%d optind=%d dlsym=%d\n", cg_add(40, 2),
           cg_counter, cg_counter_addr() == &cg_counter, cg_optind_read(),
           by_name == (void *)cg_add);
    printf("tls initial=%ld seen=%ld again=%ld worker=%ld/%ld/%ld distinct=%d\n", initial,
           seen, *cg_tls_addr(), worker_result[0], worker_result[1], worker_result[2],
           (long *)worker_result[3] != mine);
    return 0;
}
"#;

    /// Exported `(symbol, per-thread)` pairs as reported by `dyld_info`.
    fn dyld_exports(path: &Path) -> BTreeSet<(String, bool)> {
        let output = checked(
            Command::new("/usr/bin/dyld_info").arg("-exports").arg(path),
            "dyld_info -exports",
        );
        String::from_utf8_lossy(&output.output.stdout)
            .lines()
            .filter_map(|line| {
                let fields: Vec<_> = line.split_whitespace().collect();
                (fields.len() >= 2 && fields[0].starts_with("0x"))
                    .then(|| (fields[1].to_string(), fields.contains(&"[per-thread]")))
            })
            .collect()
    }

    #[test]
    fn cg_dylib_serves_an_ld64_linked_program_like_its_ld64_twin() {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let label = format!("dylib-{opt_level:?}");
            let root = tempfile::Builder::new()
                .prefix("trust-cg-macho-dylib-")
                .tempdir()
                .unwrap();
            let object_path = root.path().join("cg.o");
            let bytes = dylib_object(opt_level);
            std::fs::write(&object_path, &bytes).unwrap();
            let source = root.path().join("driver.c");
            let driver = root.path().join("driver.o");
            std::fs::write(&source, DYLIB_DRIVER).unwrap();
            checked(
                Command::new("/usr/bin/clang")
                    .args(["-O1", "-fno-stack-protector", "-c"])
                    .arg(&source)
                    .arg("-o")
                    .arg(&driver),
                "clang -c dylib driver",
            );
            let install_name = "@executable_path/libcg.dylib";
            let mut outputs = Vec::new();
            let mut exports = Vec::new();
            for twin in ["standalone", "ld64"] {
                let directory = root.path().join(twin);
                std::fs::create_dir(&directory).unwrap();
                let dylib = directory.join("libcg.dylib");
                if twin == "standalone" {
                    let image = link_dylib(
                        &[MachOParser::parse(&bytes).unwrap()],
                        &libsystem(&["_optind"]),
                        install_name,
                    )
                    .unwrap_or_else(|error| panic!("{label}: standalone dylib: {error}"));
                    std::fs::write(&dylib, image).unwrap();
                } else {
                    checked(
                        Command::new("/usr/bin/clang")
                            .arg("-dynamiclib")
                            .arg(&object_path)
                            .arg("-install_name")
                            .arg(install_name)
                            .arg("-o")
                            .arg(&dylib),
                        "ld64 twin dylib",
                    );
                }
                validate(&dylib);
                exports.push(dyld_exports(&dylib));
                let program = directory.join("driver");
                checked(
                    Command::new("/usr/bin/clang")
                        .arg(&driver)
                        .arg(&dylib)
                        .arg("-o")
                        .arg(&program),
                    "ld64 link of the driver against the dylib",
                );
                let output = run_executable_with_timeout(&program, codegen_run_timeout()).unwrap();
                assert!(!output.timed_out, "{label} {twin} timed out");
                assert_eq!(
                    output.output.status.code(),
                    Some(0),
                    "{label} {twin}: {}",
                    String::from_utf8_lossy(&output.output.stderr)
                );
                outputs.push(output.output.stdout);
            }
            assert_eq!(
                String::from_utf8_lossy(&outputs[0]),
                "add=42 counter=5 same_counter=1 optind=1 dlsym=1\n\
                 tls initial=7 seen=1000 again=1000 worker=7/2000/0 distinct=1\n",
                "{label}"
            );
            assert_eq!(outputs[0], outputs[1], "{label}: twins must agree");
            assert_eq!(
                exports[0], exports[1],
                "{label}: twins must export the same symbols"
            );
            assert!(exports[0].contains(&("_cg_tls_counter".to_string(), true)));
        }
    }

    #[test]
    fn standalone_program_consumes_a_standalone_cg_dylib_without_ld64() {
        // Neither image is linked by ld64. The standalone executable calls the
        // standalone CG dylib through stubs and imports its data through the
        // GOT and its thread-local through a bound `__thread_ptrs` slot.
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let label = format!("standalone-pair-{opt_level:?}");
            let directory = tempfile::Builder::new()
                .prefix("trust-cg-macho-standalone-pair-")
                .tempdir()
                .unwrap();
            let install_name = "@executable_path/libcg.dylib";
            let dylib = directory.path().join("libcg.dylib");
            let image = link_dylib(
                &[MachOParser::parse(&dylib_object(opt_level)).unwrap()],
                &libsystem(&["_optind"]),
                install_name,
            )
            .unwrap_or_else(|error| panic!("{label}: standalone dylib: {error}"));
            std::fs::write(&dylib, image).unwrap();
            let source = directory.path().join("driver.c");
            let driver = directory.path().join("driver.o");
            std::fs::write(&source, DYLIB_DRIVER).unwrap();
            checked(
                Command::new("/usr/bin/clang")
                    .args(["-O1", "-fno-stack-protector", "-c"])
                    .arg(&source)
                    .arg("-o")
                    .arg(&driver),
                "clang -c dylib driver",
            );
            let mut config = libsystem(&["_dlsym", "_pthread_create", "_pthread_join"]);
            config.add_dylib(
                install_name,
                [
                    "_cg_add",
                    "_cg_counter",
                    "_cg_counter_addr",
                    "_cg_optind_read",
                    "_cg_tls_addr",
                    "_cg_tls_counter",
                ]
                .iter()
                .map(|symbol| symbol.to_string())
                .collect(),
            );
            let program = directory.path().join("driver");
            let image = link_with_dylibs(
                &[MachOParser::parse(&std::fs::read(&driver).unwrap()).unwrap()],
                &config,
            )
            .unwrap_or_else(|error| panic!("{label}: standalone driver: {error}"));
            std::fs::write(&program, image).unwrap();
            make_executable(&program);
            validate(&dylib);
            validate(&program);
            let binds = dyld_binds(&program);
            for import in ["_cg_add", "_cg_counter", "_cg_tls_counter", "_dlsym"] {
                assert!(
                    binds.contains(import),
                    "{label}: {import} not bound: {binds:?}"
                );
            }
            let output = run_executable_with_timeout(&program, codegen_run_timeout()).unwrap();
            assert!(!output.timed_out, "{label} timed out");
            assert_eq!(
                output.output.status.code(),
                Some(0),
                "{label}: {}",
                String::from_utf8_lossy(&output.output.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&output.output.stdout),
                "add=42 counter=5 same_counter=1 optind=1 dlsym=1\n\
                 tls initial=7 seen=1000 again=1000 worker=7/2000/0 distinct=1\n",
                "{label}"
            );
        }
    }
}
