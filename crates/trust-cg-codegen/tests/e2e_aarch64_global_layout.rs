// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Typed global initialization must preserve declared layout, not merely
//! concatenate field widths. Native C executes the host's object (ELF on Linux
//! GNU, Mach-O on macOS); an independent ELF reader checks the generic Linux
//! object's definitions on every host, including padding and relocated pointer
//! slots.

#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/native_host.rs"]
mod native_host;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fs;
use std::path::Path;
use std::process::Command;
use trust_cg_codegen::compiler::module_object_globals;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, Constant, Endianness, FieldDef, FuncId, FuncTy, Function, Global, Inst,
    InstrNode, Linkage, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    Ty, ValueId,
};

fn aggregate(values: impl IntoIterator<Item = Constant>) -> Constant {
    Constant::Aggregate(values.into_iter().collect())
}

fn padded(tag: i128, value: i128) -> Constant {
    aggregate([Constant::Int(tag), Constant::Int(value)])
}

fn global(name: &str, ty: Ty, initializer: Option<Constant>) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: true,
        initializer,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    }
}

fn add_struct(
    module: &mut Module,
    name: &str,
    size: u64,
    align: u64,
    repr: StructRepr,
    fields: Vec<(&str, Ty, u64)>,
) -> Ty {
    let id = StructId::new(module.structs.len() as u32);
    module.structs.push(StructDef {
        id,
        name: name.into(),
        origin: None,
        size: Some(size),
        align: Some(align),
        repr,
        fields: fields
            .into_iter()
            .map(|(name, ty, offset)| FieldDef {
                name: name.into(),
                ty,
                offset: Some(offset),
            })
            .collect(),
    });
    Ty::Struct(id)
}

fn module_base() -> Module {
    let mut module = Module::new("linux_global_layout");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let padded_type = add_struct(
        &mut module,
        "Padded",
        16,
        8,
        StructRepr::C,
        vec![("tag", Ty::U8, 0), ("value", Ty::U64, 8)],
    );
    module.globals.push(global(
        "gl_padded",
        padded_type,
        Some(padded(7, 0x0123456789abcdef)),
    ));
    module
}

fn add_address_functions(module: &mut Module) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for index in 0..module.globals.len() {
        let name = format!("cg_addr_{}", module.globals[index].name);
        let mut function =
            Function::new(FuncId::new(index as u32), name, signature, BlockId::new(0));
        function.linkage = Linkage::External;
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::GlobalAddr {
                    global: GlobalId::new(index as u32),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }
}

fn matrix() -> Module {
    let mut module = module_base();
    let packed_type = add_struct(
        &mut module,
        "Packed",
        9,
        1,
        StructRepr::Packed(1),
        vec![("tag", Ty::U8, 0), ("value", Ty::U64, 1)],
    );
    let nested_type = add_struct(
        &mut module,
        "Nested",
        32,
        8,
        StructRepr::C,
        vec![
            ("head", Ty::U16, 0),
            ("inner", Ty::Struct(StructId::new(0)), 8),
            ("tail", Ty::U32, 24),
        ],
    );
    let pointers_type = add_struct(
        &mut module,
        "Pointers",
        32,
        8,
        StructRepr::C,
        vec![
            ("tag", Ty::U8, 0),
            ("local", Ty::Ptr, 8),
            ("external", Ty::Ptr, 16),
            ("tail", Ty::U16, 24),
        ],
    );
    let word = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let record = module
        .add_type(Ty::Struct(StructId::new(0)))
        .expect("Module::add_type: test fixture");
    module.globals.extend([
        global(
            "gl_packed",
            packed_type,
            Some(padded(9, 0x1122334455667788)),
        ),
        global(
            "gl_nested",
            nested_type,
            Some(aggregate([
                Constant::Int(0xabcd),
                padded(11, 0x2233445566778899),
                Constant::Int(0x76543210),
            ])),
        ),
        global(
            "gl_words",
            Ty::Array(word, 3),
            Some(aggregate([
                Constant::Int(0x33445566778899aa),
                Constant::Int(0x445566778899aabb),
                Constant::Int(0x5566778899aabbcc),
            ])),
        ),
        global(
            "gl_records",
            Ty::Array(record, 2),
            Some(aggregate([
                padded(13, 0x66778899aabbccdd),
                padded(15, 0x778899aabbccddee),
            ])),
        ),
        global("external_words", Ty::Array(word, 3), None),
        global(
            "gl_pointers",
            pointers_type,
            Some(aggregate([
                Constant::Int(17),
                Constant::SymbolAddr {
                    symbol: "gl_words".into(),
                    addend: 8,
                },
                Constant::SymbolAddr {
                    symbol: "external_words".into(),
                    addend: 16,
                },
                Constant::Int(0xcafe),
            ])),
        ),
        global(
            "gl_top_pointer",
            Ty::Ptr,
            Some(Constant::SymbolAddr {
                symbol: "gl_words".into(),
                addend: 16,
            }),
        ),
        global(
            "gl_u128",
            Ty::U128,
            Some(Constant::U128(0xfedcba98765432100123456789abcdef)),
        ),
    ]);
    add_address_functions(&mut module);
    module
}

fn u16le(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes(bytes[offset..offset + 2].try_into().unwrap())
}
fn u32le(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap())
}
fn u64le(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}
fn cstring(bytes: &[u8], offset: usize) -> &str {
    let length = bytes[offset..].iter().position(|&byte| byte == 0).unwrap();
    std::str::from_utf8(&bytes[offset..offset + length]).unwrap()
}

struct Section {
    name: String,
    kind: u32,
    offset: usize,
    size: usize,
    link: usize,
}
struct Symbol {
    name: String,
    info: u8,
    section: usize,
    value: usize,
    size: usize,
}
struct Elf<'a> {
    bytes: &'a [u8],
    sections: Vec<Section>,
    symbols: Vec<Symbol>,
}

impl<'a> Elf<'a> {
    fn parse(bytes: &'a [u8]) -> Self {
        assert_eq!(&bytes[..6], b"\x7fELF\x02\x01");
        assert_eq!(u16le(bytes, 16), 1, "ELF relocatable required");
        assert_eq!(u16le(bytes, 18), 183, "AArch64 required");
        let table = u64le(bytes, 40) as usize;
        let stride = u16le(bytes, 58) as usize;
        assert_eq!(stride, 64);
        let names_header = table + u16le(bytes, 62) as usize * stride;
        let names_offset = u64le(bytes, names_header + 24) as usize;
        let sections: Vec<_> = (0..u16le(bytes, 60) as usize)
            .map(|index| {
                let header = table + index * stride;
                Section {
                    name: cstring(bytes, names_offset + u32le(bytes, header) as usize).into(),
                    kind: u32le(bytes, header + 4),
                    offset: u64le(bytes, header + 24) as usize,
                    size: u64le(bytes, header + 32) as usize,
                    link: u32le(bytes, header + 40) as usize,
                }
            })
            .collect();
        let table = sections
            .iter()
            .find(|section| section.name == ".symtab")
            .unwrap();
        assert_eq!(table.kind, 2);
        assert_eq!(table.size % 24, 0);
        let names = &sections[table.link];
        let symbols = (table.offset..table.offset + table.size)
            .step_by(24)
            .map(|offset| Symbol {
                name: cstring(bytes, names.offset + u32le(bytes, offset) as usize).into(),
                info: bytes[offset + 4],
                section: u16le(bytes, offset + 6) as usize,
                value: u64le(bytes, offset + 8) as usize,
                size: u64le(bytes, offset + 16) as usize,
            })
            .collect();
        Self {
            bytes,
            sections,
            symbols,
        }
    }

    fn symbol(&self, name: &str) -> &Symbol {
        let rows: Vec<_> = self
            .symbols
            .iter()
            .filter(|symbol| symbol.name == name)
            .collect();
        assert_eq!(rows.len(), 1, "expected one symbol {name}");
        rows[0]
    }

    fn assert_data(&self, name: &str, expected: &[u8]) {
        let symbol = self.symbol(name);
        assert_eq!(symbol.info, 0x11, "{name}: GLOBAL OBJECT binding");
        assert_eq!(
            symbol.size,
            expected.len(),
            "{name}: exact declared object size"
        );
        let section = &self.sections[symbol.section];
        assert_eq!(section.name, ".data");
        assert!(symbol.value + symbol.size <= section.size);
        assert_eq!(
            &self.bytes[section.offset + symbol.value..section.offset + symbol.value + symbol.size],
            expected,
            "{name}: values, padding and pointer placeholders"
        );
    }

    fn assert_pointer_relocations(&self) {
        let global = self.symbol("gl_pointers");
        let rela = self
            .sections
            .iter()
            .find(|section| section.name == ".rela.data")
            .unwrap();
        assert_eq!(rela.kind, 4);
        assert_eq!(rela.size % 24, 0);
        let mut observed = Vec::new();
        for offset in (rela.offset..rela.offset + rela.size).step_by(24) {
            let place = u64le(self.bytes, offset) as usize;
            let info = u64le(self.bytes, offset + 8);
            let addend = u64le(self.bytes, offset + 16) as i64;
            if (global.value..global.value + global.size).contains(&place) {
                let target = &self.symbols[(info >> 32) as usize];
                assert_eq!(info as u32, 257, "R_AARCH64_ABS64 required");
                observed.push((place - global.value, target.name.as_str(), addend));
            }
        }
        observed.sort();
        assert_eq!(
            observed,
            vec![(8, "gl_words", 8), (16, "external_words", 16)]
        );
        let external = self.symbol("external_words");
        assert_eq!(external.section, 0, "import must not define storage");
        assert_eq!(external.info >> 4, 1, "import must remain GLOBAL");
        let top = self.symbol("gl_top_pointer");
        let mut top_relocations = Vec::new();
        for offset in (rela.offset..rela.offset + rela.size).step_by(24) {
            let place = u64le(self.bytes, offset) as usize;
            if (top.value..top.value + top.size).contains(&place) {
                let info = u64le(self.bytes, offset + 8);
                let target = &self.symbols[(info >> 32) as usize];
                top_relocations.push((
                    place - top.value,
                    info as u32,
                    target.name.as_str(),
                    u64le(self.bytes, offset + 16) as i64,
                ));
            }
        }
        assert_eq!(top_relocations, vec![(0, 257, "gl_words", 16)]);
    }
}

fn image(size: usize, values: &[(usize, &[u8])]) -> Vec<u8> {
    let mut bytes = vec![0; size];
    for (offset, value) in values {
        bytes[*offset..*offset + value.len()].copy_from_slice(value);
    }
    bytes
}

fn check_images(elf: &Elf<'_>, complete: bool) {
    elf.assert_data(
        "gl_padded",
        &image(16, &[(0, &[7]), (8, &0x0123456789abcdef_u64.to_le_bytes())]),
    );
    if !complete {
        return;
    }
    elf.assert_data(
        "gl_packed",
        &image(9, &[(0, &[9]), (1, &0x1122334455667788_u64.to_le_bytes())]),
    );
    elf.assert_data(
        "gl_nested",
        &image(
            32,
            &[
                (0, &0xabcd_u16.to_le_bytes()),
                (8, &[11]),
                (16, &0x2233445566778899_u64.to_le_bytes()),
                (24, &0x76543210_u32.to_le_bytes()),
            ],
        ),
    );
    elf.assert_data(
        "gl_words",
        &image(
            24,
            &[
                (0, &0x33445566778899aa_u64.to_le_bytes()),
                (8, &0x445566778899aabb_u64.to_le_bytes()),
                (16, &0x5566778899aabbcc_u64.to_le_bytes()),
            ],
        ),
    );
    elf.assert_data(
        "gl_records",
        &image(
            32,
            &[
                (0, &[13]),
                (8, &0x66778899aabbccdd_u64.to_le_bytes()),
                (16, &[15]),
                (24, &0x778899aabbccddee_u64.to_le_bytes()),
            ],
        ),
    );
    elf.assert_data(
        "gl_pointers",
        &image(32, &[(0, &[17]), (24, &0xcafe_u16.to_le_bytes())]),
    );
    elf.assert_pointer_relocations();
    elf.assert_data("gl_top_pointer", &[0; 8]);
    elf.assert_data(
        "gl_u128",
        &0xfedcba98765432100123456789abcdef_u128.to_le_bytes(),
    );
}

const DECLARATIONS: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stddef.h>
struct Padded { uint8_t tag; uint64_t value; };
_Static_assert(sizeof(struct Padded)==16 && offsetof(struct Padded,value)==8,"padded layout");
extern struct Padded gl_padded;
extern struct Padded *cg_addr_gl_padded(void);
"#;

const BASELINE: &str = r#"
int main(void) {
    if (cg_addr_gl_padded() != &gl_padded) return 1;
    if (gl_padded.tag != 7 || gl_padded.value != UINT64_C(0x0123456789abcdef)) {
        fprintf(stderr, "padded tag=%u value=%016lx\n", gl_padded.tag, gl_padded.value);
        return 2;
    }
    gl_padded.value ^= UINT64_C(0x123456789);
    if (cg_addr_gl_padded()->value != (UINT64_C(0x0123456789abcdef)^UINT64_C(0x123456789))) return 3;
    puts("padded initializer fields and identity agree");
    return 0;
}
"#;

const MATRIX_DRIVER: &str = r#"
struct __attribute__((packed)) Packed { uint8_t tag; uint64_t value; };
struct Nested { uint16_t head; struct Padded inner; uint32_t tail; };
struct Pointers { uint8_t tag; uint64_t *local, *external; uint16_t tail; };
_Static_assert(sizeof(struct Packed)==9 && offsetof(struct Packed,value)==1,"packed layout");
_Static_assert(sizeof(struct Nested)==32 && offsetof(struct Nested,inner)==8 && offsetof(struct Nested,tail)==24,"nested layout");
_Static_assert(sizeof(struct Pointers)==32 && offsetof(struct Pointers,local)==8 && offsetof(struct Pointers,external)==16 && offsetof(struct Pointers,tail)==24,"pointer layout");
extern struct Packed gl_packed;
extern struct Nested gl_nested;
extern struct Padded gl_records[2];
extern struct Pointers gl_pointers;
extern uint64_t gl_words[3];
extern uint64_t *gl_top_pointer;
extern unsigned __int128 gl_u128;
_Static_assert(sizeof(unsigned __int128)==16 && _Alignof(unsigned __int128)==16,"u128 layout");
uint64_t external_words[3] = { 101, 202, 303 };
extern struct Packed *cg_addr_gl_packed(void);
extern struct Nested *cg_addr_gl_nested(void);
extern struct Padded *cg_addr_gl_records(void);
extern struct Pointers *cg_addr_gl_pointers(void);
extern uint64_t *cg_addr_gl_words(void), *cg_addr_external_words(void);
extern uint64_t **cg_addr_gl_top_pointer(void);
extern unsigned __int128 *cg_addr_gl_u128(void);
#define CHECK(condition) do { if (!(condition)) { fprintf(stderr,"layout check failed at line %d: %s\n",__LINE__,#condition); return 1; } } while(0)
int main(void) {
    CHECK(cg_addr_gl_padded()==&gl_padded && cg_addr_gl_packed()==&gl_packed);
    CHECK(cg_addr_gl_nested()==&gl_nested && cg_addr_gl_records()==gl_records);
    CHECK(cg_addr_gl_pointers()==&gl_pointers && cg_addr_gl_words()==gl_words);
    CHECK(cg_addr_external_words()==external_words);
    CHECK(cg_addr_gl_top_pointer()==&gl_top_pointer && cg_addr_gl_u128()==&gl_u128);
    CHECK(gl_padded.tag==7 && gl_padded.value==UINT64_C(0x0123456789abcdef));
    CHECK(gl_packed.tag==9 && gl_packed.value==UINT64_C(0x1122334455667788));
    CHECK(gl_nested.head==0xabcd && gl_nested.inner.tag==11 && gl_nested.inner.value==UINT64_C(0x2233445566778899) && gl_nested.tail==0x76543210);
    CHECK(gl_words[0]==UINT64_C(0x33445566778899aa) && gl_words[1]==UINT64_C(0x445566778899aabb) && gl_words[2]==UINT64_C(0x5566778899aabbcc));
    CHECK(gl_records[0].tag==13 && gl_records[0].value==UINT64_C(0x66778899aabbccdd));
    CHECK(gl_records[1].tag==15 && gl_records[1].value==UINT64_C(0x778899aabbccddee));
    CHECK(gl_pointers.tag==17 && gl_pointers.tail==0xcafe);
    CHECK(gl_pointers.local==&gl_words[1] && gl_pointers.external==&external_words[2]);
    CHECK(*gl_pointers.local==UINT64_C(0x445566778899aabb) && *gl_pointers.external==303);
    CHECK(gl_top_pointer==&gl_words[2] && *gl_top_pointer==UINT64_C(0x5566778899aabbcc));
    const unsigned __int128 wide = ((unsigned __int128)UINT64_C(0xfedcba9876543210)<<64) | UINT64_C(0x0123456789abcdef);
    CHECK(gl_u128==wide);
    gl_padded.value ^= 0x1234; gl_packed.value += 9; gl_nested.inner.value -= 13;
    gl_records[1].value ^= 0x6789;
    *gl_pointers.local = UINT64_C(0x123456789abcdef0);
    *gl_pointers.external = UINT64_C(0x23456789abcdef01);
    *gl_top_pointer = UINT64_C(0x456789abcdef0123);
    gl_u128 ^= ((unsigned __int128)UINT64_C(0x12345678)<<64);
    CHECK(cg_addr_gl_padded()->value==(UINT64_C(0x0123456789abcdef)^0x1234));
    CHECK(cg_addr_gl_packed()->value==UINT64_C(0x1122334455667791));
    CHECK(cg_addr_gl_nested()->inner.value==UINT64_C(0x223344556677888c));
    CHECK(cg_addr_gl_records()[1].value==(UINT64_C(0x778899aabbccddee)^0x6789));
    CHECK(gl_words[1]==UINT64_C(0x123456789abcdef0) && external_words[2]==UINT64_C(0x23456789abcdef01));
    CHECK(gl_words[0]==UINT64_C(0x33445566778899aa) && gl_words[2]==UINT64_C(0x456789abcdef0123));
    CHECK(*cg_addr_gl_u128()==(wide ^ ((unsigned __int128)UINT64_C(0x12345678)<<64)));
    CHECK(external_words[0]==101 && external_words[1]==202);
    puts("typed initializer fields, arrays, padding and relocated pointers agree");
    return 0;
}
"#;

fn command(command: &mut Command, directory: &Path) -> String {
    let output = process::command_output_with_timeout(command, process::codegen_link_timeout())
        .expect("required C/ELF tool must launch");
    assert!(
        !output.timed_out && output.output.status.success(),
        "{command:?} failed; files={directory:?}\n{}",
        String::from_utf8_lossy(&output.output.stderr)
    );
    String::from_utf8(output.output.stdout).unwrap()
}

/// The fresh directory one optimization level of [`exercise`] builds in. The
/// two `exercise` tests run in parallel and start at the same level together.
fn level_directory(level: OptLevel) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust-cg-global-layout-{level:?}-"))
}

fn exercise(module: Module, driver: &str, complete: bool) {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let directory = level_directory(level);
        let compile = |module: &Module, triple: &str| {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: level,
                    ..Default::default()
                },
                TargetSpec::parse(triple).unwrap(),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(module)
            .expect("typed global layout fixture must compile")
            .object_code
        };
        // The independent ELF image/relocation checks below are object-level
        // and run on every host; the executed object is the host's own.
        let object = compile(&module, "aarch64-unknown-linux-gnu");
        let native_object = if native_host::DARWIN {
            let mut native = module.clone();
            native.target_info = Some(native_host::target_info());
            let native_object = compile(&native, native_host::TRIPLE);
            native_host::assert_native_object(&native_object);
            native_object
        } else {
            object.clone()
        };
        let object_path = directory.join("globals.o");
        let driver_path = directory.join("driver.c");
        let binary = directory.join("driver");
        fs::write(&object_path, &native_object).unwrap();
        fs::write(&driver_path, format!("{DECLARATIONS}{driver}")).unwrap();
        // Retained diagnostic listing of the executed object's symbols,
        // relocations and data; the assertions are the checks below.
        let inspection = if native_host::DARWIN {
            command(
                Command::new("otool")
                    .env("LC_ALL", "C")
                    .args(["-r", "-v", "-s", "__DATA", "__data"])
                    .arg(&object_path),
                &directory,
            )
        } else {
            command(
                Command::new("readelf")
                    .env("LC_ALL", "C")
                    .args(["--wide", "--symbols", "--relocs", "--hex-dump=.data"])
                    .arg(&object_path),
                &directory,
            )
        };
        fs::write(
            directory.join(if native_host::DARWIN {
                "otool.txt"
            } else {
                "readelf.txt"
            }),
            inspection,
        )
        .unwrap();
        command(
            Command::new("cc")
                .args(["-std=c11", "-O2"])
                .arg(&driver_path)
                .arg(&object_path)
                .arg("-o")
                .arg(&binary),
            &directory,
        );
        // Execute before the independent size/byte assertions so the original
        // padded-struct defect remains a native wrong-value regression too.
        let run = process::run_executable_with_timeout(&binary, process::codegen_run_timeout())
            .expect("native C reader must execute");
        assert!(
            !run.timed_out && run.output.status.success(),
            "{level:?} native global layout mismatch; files={directory:?}\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
        check_images(&Elf::parse(&object), complete);
        fs::remove_dir_all(&directory).unwrap();
    }
}

/// Parallel tests of this binary share one pid, and the realtime clock is
/// coarse (whole microseconds on macOS), so the former `pid-level-nanos` name
/// repeated whenever two `exercise` calls reached a level in the same tick and
/// `create_dir` failed with `AlreadyExists`. Callers that start together must
/// each own a directory.
#[test]
fn level_directories_are_unique_when_parallel_callers_start_together() {
    const CALLERS: usize = 32;
    for _ in 0..20 {
        let start = std::sync::Barrier::new(CALLERS);
        let directories: Vec<_> = std::thread::scope(|scope| {
            let callers: Vec<_> = (0..CALLERS)
                .map(|_| {
                    scope.spawn(|| {
                        start.wait();
                        level_directory(OptLevel::O0)
                    })
                })
                .collect();
            callers
                .into_iter()
                .map(|caller| caller.join().expect("every caller gets a directory"))
                .collect()
        });
        let distinct: std::collections::BTreeSet<_> = directories
            .iter()
            .map(|directory| directory.path())
            .collect();
        assert_eq!(distinct.len(), CALLERS, "{directories:?}");
        for directory in &directories {
            assert!(directory.is_dir(), "{directory:?}");
            fs::remove_dir(directory).unwrap();
        }
    }
}

#[test]
fn padded_global_initializer_matches_native_c_o0_through_o3() {
    let mut module = module_base();
    add_address_functions(&mut module);
    exercise(module, BASELINE, false);
}

#[test]
fn nested_packed_array_pointer_initializers_match_native_c_o0_through_o3() {
    exercise(matrix(), MATRIX_DRIVER, true);
}

#[test]
fn typed_global_initializer_rejects_count_type_and_layout_mismatches() {
    let mut cases = Vec::new();
    for count in [1, 3] {
        let mut module = module_base();
        let word = module
            .add_type(Ty::U64)
            .expect("Module::add_type: test fixture");
        module.globals[0].ty = Ty::Array(word, count);
        module.globals[0].initializer = Some(aggregate([Constant::Int(1), Constant::Int(2)]));
        cases.push((format!("array count {count} with two elements"), module));
    }
    for values in [
        vec![Constant::Int(7)],
        vec![Constant::Int(7), Constant::Int(8), Constant::Int(9)],
    ] {
        let mut module = module_base();
        module.globals[0].initializer = Some(aggregate(values));
        cases.push(("struct field count".into(), module));
    }
    for value in [
        Constant::Float(2.0),
        Constant::Bool(true),
        Constant::SymbolAddr {
            symbol: "external_words".into(),
            addend: 0,
        },
    ] {
        let mut module = module_base();
        module.globals[0].initializer = Some(aggregate([Constant::Int(7), value]));
        cases.push(("wrong initializer type for U64 field".into(), module));
    }
    let mut outside_range = module_base();
    outside_range.globals[0].initializer = Some(padded(256, 1));
    cases.push(("U8 field out of range".into(), outside_range));
    for (label, offset) in [
        ("overlapping fields", 0),
        ("misaligned C field", 1),
        ("field past object end", 16),
    ] {
        let mut module = module_base();
        module.structs[0].fields[1].offset = Some(offset);
        cases.push((label.into(), module));
    }
    let mut undersized = module_base();
    undersized.structs[0].size = Some(9);
    cases.push(("declared size excludes field tail".into(), undersized));
    let mut invalid_alignment = module_base();
    invalid_alignment.structs[0].align = Some(3);
    cases.push(("non-power-of-two alignment".into(), invalid_alignment));
    let mut failures = Vec::new();
    for (label, module) in cases {
        if module_object_globals(&module).is_ok() {
            failures.push(label);
        }
    }
    assert!(
        failures.is_empty(),
        "invalid typed initializers accepted: {failures:?}"
    );
}

fn declared_tuple_module() -> Module {
    let mut module = Module::new("declared_tuple_globals");
    module.target_info = Some(native_host::target_info());
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let id = module
        .add_type(tuple.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type: id,
        size: 16,
        align: 8,
        field_offsets: vec![8, 0],
    });
    module.globals.push(global(
        "gl_tuple",
        tuple,
        Some(padded(0x12, 0x0123456789abcdef)),
    ));
    module.globals.push(global(
        "gl_tuple_array",
        Ty::Array(id, 2),
        Some(aggregate([padded(0x34, 123), padded(0x56, 456)])),
    ));
    module
}

#[test]
fn declared_tuple_global_layout_rejects_invalid_metadata() {
    let module = declared_tuple_module();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let images = module_object_globals(&module).unwrap();
    let mut expected = vec![0; 16];
    expected[..8].copy_from_slice(&0x0123456789abcdef_u64.to_le_bytes());
    expected[8] = 0x12;
    assert_eq!(images[0].data, expected);
    assert_eq!(images[0].align, 8);
    assert_eq!(images[1].data.len(), 32);
    assert_eq!(images[1].data[8], 0x34);
    assert_eq!(images[1].data[24], 0x56);
    for mutation in 0..8 {
        let mut bad = module.clone();
        match mutation {
            0 => bad.tuple_layouts[0].field_offsets = vec![0, 0],
            1 => bad.tuple_layouts[0].field_offsets = vec![8, 1],
            2 => bad.tuple_layouts[0].field_offsets = vec![16, 0],
            3 => bad.tuple_layouts[0]
                .field_offsets
                .pop()
                .map(|_| ())
                .unwrap(),
            4 => bad.tuple_layouts[0].align = 3,
            5 => bad.tuple_layouts[0].size = 8,
            6 => bad.target_info = None,
            7 => {
                let mut conflict = bad.tuple_layouts[0].clone();
                conflict.field_offsets = vec![0, 8];
                bad.tuple_layouts.push(conflict);
            }
            _ => unreachable!(),
        }
        assert!(module_object_globals(&bad).is_err(), "mutation {mutation}");
    }
}

#[test]
fn declared_tuple_object_fields_match_native_c() {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, Signature};
    let module = declared_tuple_module();
    let globals = module_object_globals(&module).unwrap();
    // Exercise the public object layer directly. Full Compiler admission
    // refuses this REORDERED descriptor (`DeclaredTupleLayoutDisagrees`,
    // WS7.7): it admits only rows equal to the declaration-order layout.
    let emit = |triple: &str| {
        let mut anchor =
            MachFunction::new("tuple_object_anchor".into(), Signature::new(vec![], vec![]));
        let ret = anchor.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        anchor.append_inst(anchor.entry, ret);
        Pipeline::new(PipelineConfig {
            target_triple: triple.into(),
            ..Default::default()
        })
        .compile_module_with_globals(&[anchor], &globals)
        .unwrap()
    };
    let object = emit("aarch64-unknown-linux-gnu");
    let elf = Elf::parse(&object);
    elf.assert_data("gl_tuple", &globals[0].data);
    elf.assert_data("gl_tuple_array", &globals[1].data);
    let native = if native_host::DARWIN {
        emit(native_host::TRIPLE)
    } else {
        object.clone()
    };
    let directory = fresh_dir::create("trust-cg-declared-tuple-");
    let driver = directory.join("driver.c");
    let object_path = directory.join("globals.o");
    let binary = directory.join("driver");
    fs::write(directory.join("linux-globals.o"), object).unwrap();
    fs::write(&object_path, native).unwrap();
    fs::write(
        &driver,
        r#"
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
struct Reordered { uint64_t word; uint8_t tag; };
_Static_assert(sizeof(struct Reordered)==16 && offsetof(struct Reordered,tag)==8,"oracle layout");
extern struct Reordered gl_tuple, gl_tuple_array[2];
int main(void) {
    if (gl_tuple.word!=UINT64_C(0x0123456789abcdef) || gl_tuple.tag!=0x12) return 1;
    if (gl_tuple_array[0].word!=123 || gl_tuple_array[0].tag!=0x34) return 2;
    if (gl_tuple_array[1].word!=456 || gl_tuple_array[1].tag!=0x56) return 3;
    gl_tuple_array[1].word=789; gl_tuple_array[0].tag=0x78;
    if (gl_tuple_array[1].tag!=0x56 || gl_tuple_array[0].word!=123) return 4;
    puts("declared tuple order and nested array stride agree");
    return 0;
}
"#,
    )
    .unwrap();
    command(
        Command::new("cc")
            .args(["-std=c11", "-O2"])
            .arg(&driver)
            .arg(&object_path)
            .arg("-o")
            .arg(&binary),
        &directory,
    );
    let output = command(&mut Command::new(&binary), &directory);
    assert!(output.contains("declared tuple order and nested array stride agree"));
    fs::write(directory.join("native.log"), output).unwrap();
    println!("DECLARED_TUPLE_ARTIFACTS={}", directory.display());
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
