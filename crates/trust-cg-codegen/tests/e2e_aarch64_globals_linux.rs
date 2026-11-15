// trust-cg-codegen/tests/e2e_aarch64_globals_linux.rs - AArch64 ELF globals:
// relocated thread-local initial-value templates, the JIT data image, body
// SymbolAddr addends and data attributes on Linux (L05-P10, L03-P6).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The Linux (ELF) twin of `e2e_aarch64_globals_darwin`.
//!
//! A thread-local whose initial-value template embeds symbol addresses
//! (`__thread void *p = &x;`, a per-thread function pointer, an interior
//! `&arr[2]`) keeps its template in `.tdata` and carries one
//! `R_AARCH64_ABS64` (addend in `r_addend`) per slot in `.rela.tdata`,
//! exactly as gcc emits for the same C.
//!
//! Object rows run on every host and read the emitted objects back with the
//! in-repo ELF reader (independent of the writer):
//!
//! * the trust-ir `Compiler` route under the `static`, `pie` and `pic`
//!   relocation models at O0-O3 (LE/IE or TLSDESC access, same template);
//! * an explicit `.tdata.*` section and a COMDAT `.tdata.X` template are
//!   relocated through their own `.rela.*` sections;
//! * the named refusals: a pointer slot whose TARGET is a thread-local
//!   (`[TCG-TLS-SLOT-TARGET]`, ELF and Mach-O, template and data holders,
//!   definitions and imports), a function-body `SymbolAddr` naming a
//!   thread-local (`[TCG-TLS-SYMBOL-ADDR]`, ELF and Mach-O) and a thread-local
//!   in a non-TLS explicit section (`TCG-SECTION-TLS`);
//! * the relocation inventory counts every `.rela.tdata` row;
//! * hidden data visibility and `SHF_GNU_RETAIN` on a retained data section.
//!
//! The Linux GNU rows link with `cc` and run a pthread C driver that compares
//! every thread's fixed-up template with a C `static __thread void *volatile
//! p = &x;` oracle at O0-O3: executables (static and PIE; local-exec and
//! initial-exec, through both the `Compiler` and the `Pipeline` object-global
//! routes) and a `dlopen`ed shared object (TLSDESC), with a thread that
//! predates the `dlopen`. GNU `readelf` checks each object's `.rela.tdata`
//! rows against a gcc-compiled twin and the oracle (addends print in hex) and
//! each linked image's dynamic relocations inside `PT_TLS`. Negative
//! controls: dropping one `.rela.tdata` record by byte mutation fails the
//! readelf row and the driver, and a deliberately non-TLS twin module fails
//! the driver's isolation check (a driver-sensitivity control, not a
//! compiler negative).
//!
//! The remaining Linux rows port the Darwin file's other rows: the in-memory
//! JIT's data image (module globals, a string constant, a relocated
//! function-pointer table, a GOT-bound import and the image identity), a body
//! `SymbolAddr` with a non-zero addend against gcc's `&g_arr[2]`, and the
//! ELF data attributes the other Linux targets do not cover: a hidden data
//! global absent from a shared object's `.dynsym`, and a retained,
//! unreferenced data global that survives `--gc-sections` while an
//! unretained control is collected.
//!
//! This is object and execution evidence for these programs on this host, not
//! a proof of the linker, the dynamic loader, the TLS runtime or the JIT
//! publication path. The inventory row names the `S + A` value written into
//! the template; that each thread starts from a copy of the relocated
//! template is loader behavior observed here, not proved.

use std::collections::BTreeMap;

use trust_cg_codegen::elf::reparse::{ElfObjectRecords, read_object_records};
use trust_cg_codegen::pipeline::{GlobalSymbolRef, ObjectGlobal, OptLevel};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig, RelocationModel};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage, Module,
    TlsModel, Ty, ValueId, Visibility,
};
// Used only by the Linux-GNU native module's JIT and addend modules.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
use trust_ir::{BinOp, CastOp};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const MODELS: [RelocationModel; 3] = [
    RelocationModel::Static,
    RelocationModel::Pie,
    RelocationModel::Pic,
];

// gABI / AArch64 psABI constants, spelled out here rather than imported.
const SHT_PROGBITS: u32 = 1;
const SHF_WRITE: u64 = 0x1;
const SHF_ALLOC: u64 = 0x2;
const SHF_GROUP: u64 = 0x200;
const SHF_TLS: u64 = 0x400;
const STT_TLS: u8 = 6;
const R_AARCH64_ABS64: u32 = 257;
const R_AARCH64_TLSDESC_CALL: u32 = 0x239;

// =============================================================================
// trust-ir module builders (shared shape with e2e_aarch64_globals_darwin)
// =============================================================================

fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(ValueId::new(result))
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![ValueId::new(value)],
    })
}

fn load(ty: Ty, ptr: u32, result: u32) -> InstrNode {
    node(
        Inst::Load {
            ty,
            ptr: ValueId::new(ptr),
            volatile: false,
            align: None,
        },
        result,
    )
}

fn store(ty: Ty, ptr: u32, value: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty,
        ptr: ValueId::new(ptr),
        value: ValueId::new(value),
        volatile: false,
        align: None,
    })
}

fn global_addr(index: u32, result: u32) -> InstrNode {
    node(
        Inst::GlobalAddr {
            global: GlobalId::new(index),
        },
        result,
    )
}

fn data_global(name: &str, ty: Ty, mutable: bool, initializer: Option<Constant>) -> Global {
    Global {
        name: name.to_string(),
        ty,
        mutable,
        initializer,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn i64_global(name: &str, value: i128) -> Global {
    data_global(name, Ty::I64, true, Some(Constant::Int(value)))
}

fn symbol_addr(symbol: &str, addend: i64) -> Constant {
    Constant::SymbolAddr {
        symbol: symbol.to_string(),
        addend,
    }
}

/// A thread-local pointer whose template holds `symbol + addend`.
fn tls_pointer_global(name: &str, symbol: &str, addend: i64) -> Global {
    let mut global = data_global(name, Ty::Ptr, true, Some(symbol_addr(symbol, addend)));
    // On ELF the relocation model, not this marking, selects the access model.
    global.tls = Some(TlsModel::GeneralDynamic);
    global
}

/// Append a one-block function. Block parameters are numbered from 0 in
/// `params` order; `body` values start after them.
fn add_function(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) -> FuncId {
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = Linkage::External;
    let mut block = Block::new(BlockId::new(0));
    block.params = params
        .into_iter()
        .enumerate()
        .map(|(index, ty)| (ValueId::new(index as u32), ty))
        .collect();
    block.body = body;
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

fn i64_array_global(module: &mut Module, name: &str, values: [i128; 4]) -> Global {
    let word = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    data_global(
        name,
        Ty::Array(word, 4),
        false,
        Some(Constant::Aggregate(
            values.into_iter().map(Constant::Int).collect(),
        )),
    )
}

/// The Darwin file's module, verbatim:
///
/// ```c
/// int64_t g_target = 77;
/// const int64_t g_arr[4] = {10, 20, 30, 40};
/// __thread void *tp = &g_target;          // data pointer
/// __thread void *tf = &tls_fn;            // function pointer
/// __thread void *tq = (char *)g_arr + 16; // interior pointer (addend)
/// int64_t tls_fn(void)  { return 4242; }
/// void *read_tp(void)   { return tp; }
/// void  set_tp(void *p) { tp = p; }
/// void *read_tf(void)   { return tf; }
/// void *read_tq(void)   { return tq; }
/// ```
fn tls_template_module() -> Module {
    let mut module = Module::new("tls_templates");
    module.globals.push(i64_global("g_target", 77));
    let arr = i64_array_global(&mut module, "g_arr", [10, 20, 30, 40]);
    module.globals.push(arr);
    module.globals.push(tls_pointer_global("tp", "g_target", 0));
    module.globals.push(tls_pointer_global("tf", "tls_fn", 0));
    module.globals.push(tls_pointer_global("tq", "g_arr", 16));
    add_function(
        &mut module,
        "tls_fn",
        vec![],
        vec![Ty::I64],
        vec![
            node(
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(4242),
                },
                0,
            ),
            ret(0),
        ],
    );
    for (name, index) in [("read_tp", 2), ("read_tf", 3), ("read_tq", 4)] {
        add_function(
            &mut module,
            name,
            vec![],
            vec![Ty::Ptr],
            vec![global_addr(index, 0), load(Ty::Ptr, 0, 1), ret(1)],
        );
    }
    add_function(
        &mut module,
        "set_tp",
        vec![Ty::Ptr],
        vec![],
        vec![
            global_addr(2, 1),
            store(Ty::Ptr, 1, 0),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    module
}

/// The template slots `(holder, target, addend)` of [`tls_template_module`].
const TEMPLATE_SLOTS: [(&str, &str, i64); 3] = [
    ("tp", "g_target", 0),
    ("tf", "tls_fn", 0),
    ("tq", "g_arr", 16),
];

fn compiler(opt_level: OptLevel, relocation_model: RelocationModel, triple: &str) -> Compiler {
    let target_spec = TargetSpec::parse(triple).expect("supported target triple");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            target: target_spec.architecture,
            parallel: false,
            relocation_model,
            ..CompilerConfig::default()
        },
        target_spec,
    )
    .with_codegen_license(permit_unlicensed())
}

fn compile_linux(module: &Module, opt_level: OptLevel, model: RelocationModel) -> Vec<u8> {
    compiler(opt_level, model, LINUX)
        .compile(module)
        .unwrap_or_else(|error| panic!("{} {model} {opt_level:?}: {error}", module.name))
        .object_code
}

// =============================================================================
// Object reading (in-repo reader, independent of the writer)
// =============================================================================

/// One relocation read back from an object: the section it patches, its
/// offset, kind, target symbol name and addend.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Row {
    section: String,
    offset: u64,
    kind: u32,
    symbol: String,
    addend: i64,
}

fn rows(records: &ElfObjectRecords) -> Vec<Row> {
    records
        .relocations
        .iter()
        .map(|relocation| Row {
            section: records.sections[relocation.target_section].name.clone(),
            offset: relocation.record.r_offset,
            kind: relocation.record.reloc_type,
            symbol: records.symbols[relocation.record.symbol_index as usize]
                .name
                .clone(),
            addend: relocation.record.r_addend,
        })
        .collect()
}

fn symbol_value(records: &ElfObjectRecords, name: &str) -> (u16, u64, u8) {
    let symbol = records
        .symbols
        .iter()
        .find(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("symbol `{name}` missing"));
    (symbol.section_index, symbol.value, symbol.symbol_type)
}

/// Every template slot of `slots` is one `R_AARCH64_ABS64` in the holder's
/// own TLS section, at the holder's symbol value plus the slot offset, and no
/// other relocation patches a TLS section. Returns the rows it matched.
fn assert_template_rows(
    label: &str,
    records: &ElfObjectRecords,
    slots: &[(&str, u64, &str, i64)],
) -> Vec<Row> {
    let all = rows(records);
    let tls_sections: Vec<usize> = records
        .sections
        .iter()
        .enumerate()
        .filter(|(_, section)| section.sh_flags & SHF_TLS != 0)
        .map(|(index, _)| index)
        .collect();
    let mut matched = Vec::new();
    for &(holder, slot_offset, target, addend) in slots {
        let (section, value, symbol_type) = symbol_value(records, holder);
        assert_eq!(symbol_type, STT_TLS, "{label}: `{holder}` must be STT_TLS");
        let section = usize::from(section);
        let header = &records.sections[section];
        assert!(
            tls_sections.contains(&section)
                && header.sh_type == SHT_PROGBITS
                && header.sh_flags & (SHF_ALLOC | SHF_WRITE | SHF_TLS)
                    == SHF_ALLOC | SHF_WRITE | SHF_TLS,
            "{label}: `{holder}` must live in a PROGBITS TLS section, got {header:?}"
        );
        let want = Row {
            section: header.name.clone(),
            offset: value + slot_offset,
            kind: R_AARCH64_ABS64,
            symbol: target.to_string(),
            addend,
        };
        assert!(
            all.contains(&want),
            "{label}: missing template relocation {want:?} in {all:#?}"
        );
        matched.push(want);
    }
    let in_tls: Vec<&Row> = all
        .iter()
        .filter(|row| {
            records
                .sections
                .iter()
                .any(|section| section.name == row.section && section.sh_flags & SHF_TLS != 0)
        })
        .collect();
    assert_eq!(
        in_tls.len(),
        slots.len(),
        "{label}: exactly one relocation per template slot patches a TLS section: {in_tls:#?}"
    );
    // No relocation of any kind may take an ABS64 against an STT_TLS symbol:
    // that would store a TLS-block offset where an address belongs.
    for row in &all {
        if row.kind == R_AARCH64_ABS64 {
            let target = records
                .symbols
                .iter()
                .find(|symbol| symbol.name == row.symbol)
                .unwrap();
            assert_ne!(
                target.symbol_type, STT_TLS,
                "{label}: ABS64 against thread-local `{}`",
                row.symbol
            );
        }
    }
    matched
}

fn template_slots_of_module() -> Vec<(&'static str, u64, &'static str, i64)> {
    TEMPLATE_SLOTS
        .iter()
        .map(|&(holder, target, addend)| (holder, 0, target, addend))
        .collect()
}

// =============================================================================
// Host-neutral object rows
// =============================================================================

/// The trust-ir route emits one `R_AARCH64_ABS64` per template slot into
/// `.rela.tdata` under every relocation model; the access sequence follows
/// the model (TLSDESC only for `pic`), the template does not.
#[test]
fn tls_template_object_relocates_tdata_slots_under_every_relocation_model() {
    let module = tls_template_module();
    for model in MODELS {
        for opt_level in LEVELS {
            let label = format!("{model} {opt_level:?}");
            let object = compile_linux(&module, opt_level, model);
            let records = read_object_records(&object).expect("reparse ELF");
            let matched = assert_template_rows(&label, &records, &template_slots_of_module());
            assert!(
                matched.iter().all(|row| row.section == ".tdata"),
                "{label}: implicit templates live in .tdata: {matched:?}"
            );
            assert!(
                records
                    .sections
                    .iter()
                    .all(|section| section.name != ".tbss"),
                "{label}: a relocated template is never zero-fill"
            );
            let tlsdesc = rows(&records)
                .iter()
                .any(|row| row.kind == R_AARCH64_TLSDESC_CALL);
            assert_eq!(
                tlsdesc,
                model == RelocationModel::Pic,
                "{label}: only a shared object reaches thread-locals through TLS descriptors"
            );
        }
    }
}

/// A relocated template in an explicit `.tdata.*` section and a COMDAT
/// (`LinkOnce`) template are relocated through their own `.rela.*` section;
/// the COMDAT one's relocation section joins its group.
#[test]
fn explicit_and_comdat_tdata_templates_are_relocated_in_their_own_sections() {
    let mut module = tls_template_module();
    module.globals[4].section = Some(".tdata.cgtls".to_string());
    module.globals[3].linkage = Linkage::LinkOnce;
    for opt_level in LEVELS {
        let label = format!("placed {opt_level:?}");
        let object = compile_linux(&module, opt_level, RelocationModel::Static);
        let records = read_object_records(&object).expect("reparse ELF");
        let matched = assert_template_rows(&label, &records, &template_slots_of_module());
        let sections: BTreeMap<&str, &str> = matched
            .iter()
            .zip(TEMPLATE_SLOTS)
            .map(|(row, (holder, ..))| (holder, row.section.as_str()))
            .collect();
        assert_eq!(
            sections,
            BTreeMap::from([
                ("tp", ".tdata"),
                ("tf", ".tdata.tf"),
                ("tq", ".tdata.cgtls")
            ]),
            "{label}"
        );
        for name in [".tdata.tf", ".rela.tdata.tf"] {
            let section = records
                .sections
                .iter()
                .find(|section| section.name == name)
                .unwrap_or_else(|| panic!("{label}: {name} missing"));
            assert_ne!(
                section.sh_flags & SHF_GROUP,
                0,
                "{label}: {name} must be a COMDAT group member"
            );
        }
        assert!(
            records
                .sections
                .iter()
                .any(|section| section.name == ".rela.tdata.cgtls"),
            "{label}: the explicit template has its own relocation section"
        );
    }

    // A thread-local in a NON-TLS explicit section stays refused by name.
    let mut module = tls_template_module();
    module.globals[4].section = Some(".data.cgtls".to_string());
    let error = compiler(OptLevel::O0, RelocationModel::Static, LINUX)
        .compile(&module)
        .expect_err("a thread-local in a non-TLS section is refused")
        .to_string();
    assert!(
        error.contains("TCG-SECTION-TLS") && error.contains("tq") && error.contains(".data.cgtls"),
        "unexpected diagnostic: {error}"
    );
}

/// A pointer slot whose TARGET is itself a thread-local has no link-time
/// address on any object format and is refused by name: from a template and
/// from ordinary data, naming a definition or an import, on ELF and Mach-O.
#[test]
fn pointer_slots_naming_thread_locals_are_refused_by_name_on_elf_and_macho() {
    let mut template_to_tls = tls_template_module();
    template_to_tls.globals[2].initializer = Some(symbol_addr("tf", 0));

    let mut data_to_tls = tls_template_module();
    data_to_tls.globals.push(data_global(
        "p_to_tls",
        Ty::Ptr,
        true,
        Some(symbol_addr("tq", 8)),
    ));

    let mut data_to_import = tls_template_module();
    let mut import = data_global("ext_tls", Ty::I64, true, None);
    import.tls = Some(TlsModel::GeneralDynamic);
    data_to_import.globals.push(import);
    data_to_import.globals.push(data_global(
        "p_to_ext",
        Ty::Ptr,
        false,
        Some(symbol_addr("ext_tls", 0)),
    ));

    for (module, holder, target) in [
        (&template_to_tls, "tp", "tf"),
        (&data_to_tls, "p_to_tls", "tq"),
        (&data_to_import, "p_to_ext", "ext_tls"),
    ] {
        for (triple, model) in [
            (LINUX, RelocationModel::Static),
            (LINUX, RelocationModel::Pic),
            (DARWIN, RelocationModel::Static),
        ] {
            let error = compiler(OptLevel::O0, model, triple)
                .compile(module)
                .expect_err("a pointer slot naming a thread-local is refused")
                .to_string();
            assert!(
                error.contains("[TCG-TLS-SLOT-TARGET]")
                    && error.contains(&format!("`{holder}`"))
                    && error.contains(&format!("thread-local `{target}`"))
                    && error.contains("fail-closed"),
                "{triple} {model}: unexpected diagnostic: {error}"
            );
        }
    }

    // The Pipeline object-global API and the relocation inventory refuse too
    // (the JIT data image's unit test covers the third validator caller).
    for triple in [LINUX, DARWIN] {
        let pipeline = pipeline(triple, OptLevel::O0);
        let mut globals = pipeline_route_globals();
        globals[1].symbol_refs[1].symbol = "cg_tls_plain".to_string();
        let error = pipeline
            .compile_module_with_globals(&[], &globals)
            .expect_err("a template slot naming a thread-local is refused")
            .to_string();
        assert!(
            error.contains("[TCG-TLS-SLOT-TARGET]")
                && error.contains("`cg_tls_mixed`")
                && error.contains("byte offset 16")
                && error.contains("thread-local `cg_tls_plain`"),
            "{triple}: unexpected diagnostic: {error}"
        );
        #[cfg(feature = "verify")]
        {
            let error = pipeline
                .module_relocation_inventory_report_with_object_state(
                    &[],
                    &globals,
                    &[],
                    "tls-slot-target.o",
                )
                .expect_err("the inventory refuses the same globals")
                .to_string();
            assert!(
                error.contains("[TCG-TLS-SLOT-TARGET]"),
                "{triple}: unexpected inventory diagnostic: {error}"
            );
        }
    }
}

/// A function-body `Constant::SymbolAddr` naming a thread-local would lower
/// to a plain page reference (ELF `R_AARCH64_ADR_PREL_PG_HI21` /
/// `ADD_ABS_LO12_NC` against the `STT_TLS` symbol, which GNU ld only warns
/// about and links to an address that is no thread's copy; a Mach-O page
/// reference to the TLV descriptor). It is refused by name on ELF under every
/// relocation model and on Mach-O, for a definition (with and without an
/// addend) and an import; the same body naming a plain data global compiles.
#[test]
fn body_symbol_addr_naming_a_thread_local_is_refused_by_name_on_elf_and_macho() {
    let module_naming = |symbol: &str, addend: i64| {
        let mut module = tls_template_module();
        let mut import = data_global("ext_tls", Ty::I64, true, None);
        import.tls = Some(TlsModel::GeneralDynamic);
        module.globals.push(import);
        add_function(
            &mut module,
            "body_addr",
            vec![],
            vec![Ty::Ptr],
            vec![body_symbol_addr(symbol, addend, 0), ret(0)],
        );
        module
    };
    let targets = [
        (LINUX, RelocationModel::Static),
        (LINUX, RelocationModel::Pie),
        (LINUX, RelocationModel::Pic),
        (DARWIN, RelocationModel::Static),
    ];
    for (triple, model) in targets {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let label = format!("{triple} {model} {opt_level:?}");
            for (symbol, addend) in [("tp", 0), ("tq", 8), ("ext_tls", 0)] {
                let error = compiler(opt_level, model, triple)
                    .compile(&module_naming(symbol, addend))
                    .expect_err("a body SymbolAddr naming a thread-local is refused")
                    .to_string();
                assert!(
                    error.contains("[TCG-TLS-SYMBOL-ADDR]")
                        && error.contains(&format!("thread-local `{symbol}`"))
                        && error.contains(&format!("addend {addend}"))
                        && error.contains("fail-closed"),
                    "{label} `{symbol}`+{addend}: unexpected diagnostic: {error}"
                );
            }
            let object = compiler(opt_level, model, triple)
                .compile(&module_naming("g_target", 8))
                .unwrap_or_else(|error| panic!("{label}: plain data refused: {error}"))
                .object_code;
            assert!(!object.is_empty(), "{label}: empty object");
        }
    }
}

// =============================================================================
// Pipeline object-global route
// =============================================================================

const PLAIN_TLS_WORD: u64 = 0xabcd_ef01_2345_6789;
const MIXED_PLAIN_WORD: u64 = 0x1122_3344_5566_7788;

/// Object globals of the `Pipeline` route:
///
/// ```c
/// __thread uint64_t cg_tls_plain = 0xabcdef0123456789;
/// __thread void *cg_tls_mixed[5] = {        // byte offsets 0, 8, 16, 24, 32
///     &c_target, (void *)0x1122334455667788, (void *)&c_fn,
///     (char *)c_arr + 16, (char *)cg_word + 8 };
/// int64_t cg_word[2] = {0x1111, 0x2222};
/// ```
///
/// `c_target`, `c_fn` and `c_arr` are defined by the C driver (undefined
/// here); `cg_word` is defined in this object. The second template sits at a
/// non-zero `.tdata` offset and interleaves a plain word with its slots.
fn pipeline_route_globals() -> Vec<ObjectGlobal> {
    let tls = |name: &str, data: Vec<u8>, symbol_refs: Vec<GlobalSymbolRef>| ObjectGlobal {
        name: name.to_string(),
        data,
        mutable: true,
        is_external: true,
        symbol_refs,
        is_thread_local: true,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    };
    let mut mixed = vec![0u8; 40];
    mixed[8..16].copy_from_slice(&MIXED_PLAIN_WORD.to_le_bytes());
    let slot = |offset: u64, symbol: &str, addend: i64| GlobalSymbolRef {
        offset,
        symbol: symbol.to_string(),
        addend,
    };
    vec![
        tls(
            "cg_tls_plain",
            PLAIN_TLS_WORD.to_le_bytes().to_vec(),
            vec![],
        ),
        tls(
            "cg_tls_mixed",
            mixed,
            vec![
                slot(0, "c_target", 0),
                slot(16, "c_fn", 0),
                slot(24, "c_arr", 16),
                slot(32, "cg_word", 8),
            ],
        ),
        ObjectGlobal {
            is_thread_local: false,
            data: [0x1111u64, 0x2222]
                .into_iter()
                .flat_map(u64::to_le_bytes)
                .collect(),
            ..tls("cg_word", vec![], vec![])
        },
    ]
}

const PIPELINE_ROUTE_SLOTS: [(&str, u64, &str, i64); 4] = [
    ("cg_tls_mixed", 0, "c_target", 0),
    ("cg_tls_mixed", 16, "c_fn", 0),
    ("cg_tls_mixed", 24, "c_arr", 16),
    ("cg_tls_mixed", 32, "cg_word", 8),
];

fn pipeline(triple: &str, opt_level: OptLevel) -> trust_cg_codegen::pipeline::Pipeline {
    trust_cg_codegen::pipeline::Pipeline::new(trust_cg_codegen::pipeline::PipelineConfig {
        target_triple: triple.to_string(),
        opt_level,
        ..trust_cg_codegen::pipeline::PipelineConfig::default()
    })
}

/// `name` returns the calling thread's address of thread-local `symbol`.
fn tls_addr_function(
    name: &str,
    symbol: &str,
    model: trust_cg_ir::TlsModel,
) -> trust_cg_lower::function::Function {
    use trust_cg_lower::function::{BasicBlock, Function as LowerFunction, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
    use trust_cg_lower::types::Type as LowerType;
    let mut func = LowerFunction::new(
        name.to_owned(),
        Signature {
            params: vec![],
            returns: vec![LowerType::I64],
        },
    );
    func.entry_block = Block(0);
    func.block_order = vec![Block(0)];
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::TlsRef {
                        name: symbol.to_owned(),
                        model,
                        local_exec_offset: None,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(0)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn pipeline_route_object(opt_level: OptLevel, model: trust_cg_ir::TlsModel) -> Vec<u8> {
    let pipeline = pipeline(LINUX, opt_level);
    let functions: Vec<_> = [
        ("cg_addr_plain", "cg_tls_plain"),
        ("cg_addr_mixed", "cg_tls_mixed"),
    ]
    .into_iter()
    .map(|(name, symbol)| {
        pipeline
            .prepare_function(&tls_addr_function(name, symbol, model))
            .expect("prepare TLS address function")
    })
    .collect();
    pipeline
        .compile_module_with_globals(&functions, &pipeline_route_globals())
        .expect("a relocated TLS template compiles on the AArch64 ELF Pipeline route")
}

/// The `Pipeline` route relocates a template at a non-zero `.tdata` offset
/// whose slots name undefined data, an undefined function and a defined
/// global, each with its addend; the plain words keep their bytes.
#[test]
fn pipeline_route_template_rows_name_every_slot_with_its_addend() {
    for model in [
        trust_cg_ir::TlsModel::LocalExec,
        trust_cg_ir::TlsModel::InitialExec,
    ] {
        for opt_level in LEVELS {
            let label = format!("pipeline {model:?} {opt_level:?}");
            let object = pipeline_route_object(opt_level, model);
            let records = read_object_records(&object).expect("reparse ELF");
            let matched = assert_template_rows(&label, &records, &PIPELINE_ROUTE_SLOTS);
            let (_, mixed_base, _) = symbol_value(&records, "cg_tls_mixed");
            assert_ne!(mixed_base, 0, "{label}: the second template is not at 0");
            assert!(matched.iter().all(|row| row.section == ".tdata"));
            for (name, section_index) in [("c_target", 0), ("c_fn", 0), ("c_arr", 0)] {
                assert_eq!(
                    symbol_value(&records, name).0,
                    section_index,
                    "{label}: `{name}` is an undefined reference"
                );
            }
            #[cfg(feature = "verify")]
            {
                use trust_cg_verify::ObjectRelocationKind;
                let pipeline = pipeline(LINUX, opt_level);
                let functions: Vec<_> = [
                    ("cg_addr_plain", "cg_tls_plain"),
                    ("cg_addr_mixed", "cg_tls_mixed"),
                ]
                .into_iter()
                .map(|(name, symbol)| {
                    pipeline
                        .prepare_function(&tls_addr_function(name, symbol, model))
                        .unwrap()
                })
                .collect();
                let report = pipeline
                    .module_relocation_inventory_report_with_object_state(
                        &functions,
                        &pipeline_route_globals(),
                        &[],
                        "tls-template.o",
                    )
                    .expect("inventory report")
                    .expect("ELF inventory");
                assert_eq!(
                    report.entries.len(),
                    records.relocations.len(),
                    "{label}: the inventory names every relocation the object carries"
                );
                assert_eq!(
                    report
                        .entries
                        .iter()
                        .filter(|entry| entry.kind == ObjectRelocationKind::AArch64ElfAbs64)
                        .count(),
                    PIPELINE_ROUTE_SLOTS.len(),
                    "{label}: one ABS64 inventory row per .rela.tdata record"
                );
            }
        }
    }
}

// =============================================================================
// JIT data image, SymbolAddr addend and data attributes (module builders)
// =============================================================================

/// The Darwin file's JIT module, verbatim:
///
/// ```c
/// int64_t g_counter = 100;
/// static const uint8_t g_str[6] = "hello";
/// static void *const tbl[1] = { &bump };
/// extern int64_t host_value;             // bound by the embedder
/// int64_t bump(int64_t x) { g_counter += x; return g_counter; }
/// const void *str_ptr(void) { return g_str; }
/// int64_t str_byte1(void)   { return *((const uint8_t *)g_str + 1); }
/// void *tbl_read(void)      { return tbl[0]; }
/// int64_t read_host(void)   { return host_value; }
/// ```
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn jit_globals_module() -> Module {
    let mut module = Module::new("jit_globals");
    module.globals.push(i64_global("g_counter", 100));
    let byte = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let mut text = data_global(
        "g_str",
        Ty::Array(byte, 6),
        false,
        Some(Constant::Aggregate(
            b"hello\0"
                .iter()
                .map(|b| Constant::Int(i128::from(*b)))
                .collect(),
        )),
    );
    text.linkage = Linkage::Internal;
    module.globals.push(text);
    let ptr = module
        .add_type(Ty::Ptr)
        .expect("Module::add_type: test fixture");
    let mut table = data_global(
        "tbl",
        Ty::Array(ptr, 1),
        false,
        Some(Constant::Array(vec![symbol_addr("bump", 0)])),
    );
    table.linkage = Linkage::Internal;
    module.globals.push(table);
    module
        .globals
        .push(data_global("host_value", Ty::I64, true, None));
    add_function(
        &mut module,
        "bump",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![
            global_addr(0, 1),
            load(Ty::I64, 1, 2),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(0),
                },
                3,
            ),
            store(Ty::I64, 1, 3),
            ret(3),
        ],
    );
    add_function(
        &mut module,
        "str_ptr",
        vec![],
        vec![Ty::Ptr],
        vec![global_addr(1, 0), ret(0)],
    );
    add_function(
        &mut module,
        "str_byte1",
        vec![],
        vec![Ty::I64],
        vec![
            body_symbol_addr("g_str", 1, 0),
            load(Ty::U8, 0, 1),
            node(
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::U8,
                    dst_ty: Ty::I64,
                    operand: ValueId::new(1),
                },
                2,
            ),
            ret(2),
        ],
    );
    add_function(
        &mut module,
        "tbl_read",
        vec![],
        vec![Ty::Ptr],
        vec![global_addr(2, 0), load(Ty::Ptr, 0, 1), ret(1)],
    );
    add_function(
        &mut module,
        "read_host",
        vec![],
        vec![Ty::I64],
        vec![global_addr(3, 0), load(Ty::I64, 0, 1), ret(1)],
    );
    module
}

/// A body-level `Constant::SymbolAddr { symbol, addend }` value.
fn body_symbol_addr(symbol: &str, addend: i64, result: u32) -> InstrNode {
    node(
        Inst::Const {
            ty: Ty::Ptr,
            value: Constant::SymbolAddr {
                symbol: symbol.to_string(),
                addend,
            },
        },
        result,
    )
}

/// ```c
/// const int64_t g_arr[4] = {10, 20, 30, 40};
/// int64_t third(void)      { return *(const int64_t *)((const char *)g_arr + 16); }
/// const void *third_addr(void) { return (const char *)g_arr + 16; }
/// ```
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn addend_module() -> Module {
    let mut module = Module::new("symbol_addr_addend");
    let arr = i64_array_global(&mut module, "g_arr", [10, 20, 30, 40]);
    module.globals.push(arr);
    add_function(
        &mut module,
        "third",
        vec![],
        vec![Ty::I64],
        vec![
            body_symbol_addr("g_arr", 16, 0),
            load(Ty::I64, 0, 1),
            ret(1),
        ],
    );
    add_function(
        &mut module,
        "third_addr",
        vec![],
        vec![Ty::Ptr],
        vec![body_symbol_addr("g_arr", 16, 0), ret(0)],
    );
    module
}

/// The ELF data-attribute rows the other Linux targets do not cover:
///
/// ```c
/// __attribute__((visibility("hidden"))) int64_t g_hidden = 6;
/// __attribute__((used, retain, section(".data.cg_used"))) int64_t g_used = 7;
/// __attribute__((section(".data.cg_dropped"))) int64_t g_dropped = 8;
/// int64_t read_hidden(void) { return g_hidden; }
/// int64_t *hidden_addr(void) { return &g_hidden; }
/// ```
///
/// Neither `g_used` nor `g_dropped` is referenced by anything, so under
/// `--gc-sections` only `SHF_GNU_RETAIN` can keep `g_used`; `g_dropped`
/// is the control that the garbage collection really runs.
fn attributes_module() -> Module {
    let mut module = Module::new("elf_data_attributes");
    let mut hidden = i64_global("g_hidden", 6);
    hidden.visibility = Visibility::Hidden;
    let mut used = i64_global("g_used", 7);
    used.retained = true;
    used.section = Some(".data.cg_used".to_string());
    let mut dropped = i64_global("g_dropped", 8);
    dropped.section = Some(".data.cg_dropped".to_string());
    module.globals.extend([hidden, used, dropped]);
    add_function(
        &mut module,
        "read_hidden",
        vec![],
        vec![Ty::I64],
        vec![global_addr(0, 0), load(Ty::I64, 0, 1), ret(1)],
    );
    add_function(
        &mut module,
        "hidden_addr",
        vec![],
        vec![Ty::Ptr],
        vec![global_addr(0, 0), ret(0)],
    );
    module
}

const SHF_GNU_RETAIN: u64 = 0x20_0000;
const STV_HIDDEN: u8 = 2;

/// The attribute module's object carries the attributes the linker acts on:
/// a hidden `STV_HIDDEN` data symbol, and each explicit data section with
/// `SHF_GNU_RETAIN` exactly when its global is retained.
#[test]
fn data_attribute_object_marks_hidden_visibility_and_retained_sections() {
    for model in MODELS {
        for opt_level in LEVELS {
            let label = format!("attributes {model} {opt_level:?}");
            let records =
                read_object_records(&compile_linux(&attributes_module(), opt_level, model))
                    .expect("reparse ELF");
            let hidden = records
                .symbols
                .iter()
                .find(|symbol| symbol.name == "g_hidden")
                .expect("g_hidden");
            assert_eq!(hidden.visibility, STV_HIDDEN, "{label}");
            for (section, retained) in [(".data.cg_used", true), (".data.cg_dropped", false)] {
                let header = records
                    .sections
                    .iter()
                    .find(|header| header.name == section)
                    .unwrap_or_else(|| panic!("{label}: {section} missing"));
                assert_eq!(
                    header.sh_flags & SHF_GNU_RETAIN != 0,
                    retained,
                    "{label}: {section} {header:?}"
                );
            }
        }
    }
}

// =============================================================================
// Linux-native controls
// =============================================================================

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod native_process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::*;
    use sha2::{Digest, Sha256};
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};

    /// The shared pthread harness. A driver defines `NSLOTS`,
    /// `INITIAL_TARGET`, `expect[]`, `cg_get(i)`, `c_get(i)` (the C oracle's
    /// per-thread value), `cg_set0(p)` and `check_targets()` before it.
    ///
    /// Three live threads check that their fresh template equals the C
    /// oracle's and the expected addresses, then each re-points its own slot 0
    /// and must still see only its own value (isolation). A thread created
    /// after the main thread re-pointed its copy must again start from the
    /// template. Every thread passes every barrier, so a failed check exits
    /// with its code instead of hanging.
    const HARNESS: &str = r#"
static pthread_barrier_t barrier;
static int64_t locals[3];
static int fresh_failed = -1;
static int check_template(const char *who) {
    for (int i = 0; i < NSLOTS; ++i) {
        void *cg = cg_get(i), *c = c_get(i);
        if (cg != c || cg != expect[i]) {
            fprintf(stderr, "%s: template slot %d: cg=%p c=%p expected=%p\n",
                    who, i, cg, c, expect[i]);
            return 1;
        }
    }
    if (check_targets()) {
        fprintf(stderr, "%s: a relocated pointer does not reach its target\n", who);
        return 1;
    }
    return 0;
}
static void *worker(void *arg) {
    int id = (int)(intptr_t)arg;
    int failed = check_template("worker") ? 10 : 0;
    pthread_barrier_wait(&barrier);
    cg_set0(&locals[id]);
    pthread_barrier_wait(&barrier);
    if (!failed && cg_get(0) != &locals[id]) {
        fprintf(stderr, "worker %d: isolation: sees %p, set %p\n", id, cg_get(0),
                (void *)&locals[id]);
        failed = 11;
    }
    if (!failed && c_get(0) != expect[0]) failed = 12;
    pthread_barrier_wait(&barrier);
    return (void *)(intptr_t)failed;
}
static void *fresh(void *arg) {
    (void)arg;
    fresh_failed = check_template("thread created after re-pointing");
    return NULL;
}
static int run(void) {
    if (check_template("main")) return 20;
    if (*(int64_t *)cg_get(0) != INITIAL_TARGET) return 21;
    /* A write through the per-thread pointer lands in the shared target. */
    *(int64_t *)cg_get(0) = 78;
    if (*(int64_t *)expect[0] != 78) return 22;
    if (pthread_barrier_init(&barrier, 0, 3)) return 23;
    pthread_t threads[2];
    for (intptr_t i = 1; i <= 2; ++i)
        if (pthread_create(&threads[i - 1], 0, worker, (void *)i)) return 23;
    pthread_barrier_wait(&barrier);
    cg_set0(&locals[0]);
    pthread_barrier_wait(&barrier);
    int failed = 0;
    if (cg_get(0) != &locals[0]) {
        fprintf(stderr, "main: isolation: sees %p, set %p\n", cg_get(0), (void *)&locals[0]);
        failed = 24;
    }
    pthread_barrier_wait(&barrier);
    for (int i = 0; i < 2; ++i) {
        void *result;
        if (pthread_join(threads[i], &result)) return 25;
        if (result && !failed) failed = (int)(intptr_t)result;
    }
    if (failed) return failed;
    pthread_t t;
    if (pthread_create(&t, 0, fresh, 0) || pthread_join(t, 0)) return 26;
    if (fresh_failed) return 27;
    if (cg_get(0) != &locals[0]) return 28;
    return pthread_barrier_destroy(&barrier) ? 29 : 0;
}
"#;

    /// Exit code of `run()` when the main thread's fresh template disagrees.
    const MAIN_TEMPLATE_MISMATCH: i32 = 20;
    /// Exit codes of the isolation checks (worker, main).
    const ISOLATION_FAILURES: [i32; 2] = [11, 24];

    /// The C oracle for [`tls_template_module`], linked into the same image.
    /// `volatile` keeps gcc from folding a never-written `static` template
    /// into constants (it does at -O2), so every read is a real per-thread
    /// load of a relocated `.tdata` template; [`oracle_object`] pins that.
    const ORACLE: &str = r#"
#include <stdint.h>
extern int64_t g_target;
extern const int64_t g_arr[4];
extern int64_t tls_fn(void);
static __thread void *volatile o_tp = &g_target;
static __thread void *volatile o_tf = (void *)&tls_fn;
static __thread void *volatile o_tq = (char *)g_arr + 16;
void *c_read_tp(void) { return o_tp; }
void *c_read_tf(void) { return o_tf; }
void *c_read_tq(void) { return o_tq; }
"#;

    /// A gcc twin of [`tls_template_module`]: its `.rela.tdata` rows are the
    /// object-level oracle for the trust-cg rows.
    const GCC_TWIN: &str = r#"
#include <stdint.h>
int64_t g_target = 77;
const int64_t g_arr[4] = {10, 20, 30, 40};
int64_t tls_fn(void) { return 4242; }
__thread void *tp = &g_target;
__thread void *tf = (void *)&tls_fn;
__thread void *tq = (char *)g_arr + 16;
void *read_tp(void) { return tp; }
void set_tp(void *p) { tp = p; }
void *read_tf(void) { return tf; }
void *read_tq(void) { return tq; }
"#;

    const EXEC_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#define NSLOTS 3
#define INITIAL_TARGET 77
extern int64_t g_target;
extern const int64_t g_arr[4];
extern int64_t tls_fn(void);
extern void *read_tp(void), *read_tf(void), *read_tq(void);
extern void set_tp(void *);
extern void *c_read_tp(void), *c_read_tf(void), *c_read_tq(void);
static void *expect[NSLOTS];
static void *cg_get(int i) { return i == 0 ? read_tp() : i == 1 ? read_tf() : read_tq(); }
static void *c_get(int i) { return i == 0 ? c_read_tp() : i == 1 ? c_read_tf() : c_read_tq(); }
static void cg_set0(void *p) { set_tp(p); }
static int check_targets(void) {
    return ((int64_t (*)(void))cg_get(1))() != 4242 || *(const int64_t *)cg_get(2) != 30;
}
HARNESS
int main(void) {
    expect[0] = &g_target;
    expect[1] = (void *)&tls_fn;
    expect[2] = (void *)&g_arr[2];
    int rc = run();
    if (rc) return rc;
    if (g_target != 78) return 3;
    puts("relocated TLS templates matched the C oracle in every thread");
    return 0;
}
"#;

    const DLOPEN_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <dlfcn.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>
#define NSLOTS 3
#define INITIAL_TARGET 77
typedef void *(*ptr_fn)(void);
static ptr_fn cg_fns[NSLOTS], c_fns[NSLOTS];
static void (*cg_set)(void *);
static void *expect[NSLOTS];
static void *lib;
static void *need(const char *name) {
    void *p = dlsym(lib, name);
    if (!p) { fprintf(stderr, "missing %s: %s\n", name, dlerror()); _exit(90); }
    return p;
}
static void *cg_get(int i) { return cg_fns[i](); }
static void *c_get(int i) { return c_fns[i](); }
static void cg_set0(void *p) { cg_set(p); }
static int check_targets(void) {
    return ((int64_t (*)(void))cg_get(1))() != 4242 || *(const int64_t *)cg_get(2) != 30;
}
HARNESS
static pthread_barrier_t pre_barrier;
static int pre_failed = -1;
/* A thread that exists before dlopen gets its copy of the library's TLS block
   on its first access, from the already relocated template. */
static void *pre_thread(void *arg) {
    (void)arg;
    pthread_barrier_wait(&pre_barrier);
    pre_failed = check_template("thread created before dlopen");
    return NULL;
}
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    if (pthread_barrier_init(&pre_barrier, 0, 2)) return 4;
    pthread_t pre;
    if (pthread_create(&pre, 0, pre_thread, 0)) return 4;
    lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    const char *cg_names[NSLOTS] = {"read_tp", "read_tf", "read_tq"};
    const char *c_names[NSLOTS] = {"c_read_tp", "c_read_tf", "c_read_tq"};
    for (int i = 0; i < NSLOTS; ++i) {
        cg_fns[i] = (ptr_fn)need(cg_names[i]);
        c_fns[i] = (ptr_fn)need(c_names[i]);
    }
    cg_set = (void (*)(void *))need("set_tp");
    expect[0] = need("g_target");
    expect[1] = need("tls_fn");
    expect[2] = (char *)need("g_arr") + 16;
    pthread_barrier_wait(&pre_barrier);
    if (pthread_join(pre, 0) || pre_failed) return 5;
    if (pthread_barrier_destroy(&pre_barrier)) return 4;
    int rc = run();
    if (rc) return rc;
    if (*(int64_t *)expect[0] != 78) return 6;
    puts("relocated TLS templates in a dlopened shared object matched the C oracle in every thread");
    return dlclose(lib) ? 91 : 0;
}
"#;

    /// Driver for the `Pipeline` route (`pipeline_route_globals`): the C
    /// oracle is the driver's own `static __thread` array (`volatile`, as in
    /// [`ORACLE`]), whose `.rela.tdata` rows equal trust-cg's.
    const PIPELINE_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#define NSLOTS 4
#define INITIAL_TARGET 5
int64_t c_target = 5;
const int64_t c_arr[4] = {10, 20, 30, 40};
int64_t c_fn(void) { return 99; }
extern int64_t cg_word[2];
extern void **cg_addr_mixed(void);
extern uint64_t *cg_addr_plain(void);
static __thread void *volatile oracle[NSLOTS] = {
    &c_target, (void *)&c_fn, (char *)c_arr + 16, (char *)cg_word + 8 };
static const int slot_word[NSLOTS] = {0, 2, 3, 4};
static void *expect[NSLOTS];
static void *cg_get(int i) { return cg_addr_mixed()[slot_word[i]]; }
static void *c_get(int i) { return oracle[i]; }
static void cg_set0(void *p) { cg_addr_mixed()[0] = p; }
static int check_targets(void) {
    return ((int64_t (*)(void))cg_get(1))() != 99 || *(const int64_t *)cg_get(2) != 30
        || *(const int64_t *)cg_get(3) != 0x2222
        || (uint64_t)(uintptr_t)cg_addr_mixed()[1] != UINT64_C(0x1122334455667788)
        || *cg_addr_plain() != UINT64_C(0xabcdef0123456789);
}
HARNESS
int main(void) {
    expect[0] = &c_target;
    expect[1] = (void *)&c_fn;
    expect[2] = (void *)&c_arr[2];
    expect[3] = (void *)&cg_word[1];
    int rc = run();
    if (rc) return rc;
    if (c_target != 78) return 3;
    puts("pipeline-route relocated TLS templates matched the C oracle in every thread");
    return 0;
}
"#;

    const EXEC_PASS: &str = "relocated TLS templates matched the C oracle in every thread";
    const DLOPEN_PASS: &str =
        "relocated TLS templates in a dlopened shared object matched the C oracle in every thread";
    const PIPELINE_PASS: &str =
        "pipeline-route relocated TLS templates matched the C oracle in every thread";

    fn command_output(command: &mut Command, timeout: std::time::Duration) -> Output {
        let result = native_process::command_output_with_timeout(command, timeout)
            .unwrap_or_else(|error| panic!("required native command {command:?}: {error}"));
        assert!(!result.timed_out, "{command:?} timed out");
        result.output
    }

    fn checked(command: &mut Command, timeout: std::time::Duration) -> Output {
        let output = command_output(command, timeout);
        assert!(
            output.status.success(),
            "{command:?}: {}\nstdout={}\nstderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        output
    }

    fn scratch(label: &str) -> tempfile::TempDir {
        tempfile::Builder::new()
            .prefix(&format!("trust-cg-globals-linux-{label}-"))
            .tempdir()
            .unwrap()
    }

    fn write(dir: &Path, name: &str, bytes: &[u8]) -> PathBuf {
        let path = dir.join(name);
        std::fs::write(&path, bytes).unwrap();
        path
    }

    fn c_source(dir: &Path, name: &str, body: &str) -> PathBuf {
        write(dir, name, body.replace("HARNESS", HARNESS).as_bytes())
    }

    fn cc(args: &[&str], inputs: &[&Path], output: &Path) {
        let mut command = Command::new("cc");
        command.args(args);
        for input in inputs {
            command.arg(input);
        }
        checked(
            command.arg("-o").arg(output),
            native_process::codegen_link_timeout(),
        );
    }

    fn readelf(args: &[&str], path: &Path) -> String {
        String::from_utf8(
            checked(
                Command::new("readelf")
                    .env("LC_ALL", "C")
                    .args(args)
                    .arg(path),
                native_process::codegen_link_timeout(),
            )
            .stdout,
        )
        .unwrap()
    }

    /// Record the object's identity and `.rela.tdata` rows in the test log.
    fn log_object(label: &str, path: &Path) {
        let digest = Sha256::digest(std::fs::read(path).unwrap());
        let hex: String = digest.iter().map(|byte| format!("{byte:02x}")).collect();
        println!("sha256 {hex} {label}");
    }

    /// One `readelf -rW` row: `(offset, type, "symbol + addend")`.
    type ReadelfRow = (u64, String, String);

    /// The rows of relocation section `section` in `readelf -rW` output, or
    /// `None` when the section is absent.
    fn readelf_rows(text: &str, section: &str) -> Option<Vec<ReadelfRow>> {
        let header = format!("Relocation section '{section}' at offset");
        let mut lines = text.lines().skip_while(|line| !line.starts_with(&header));
        lines.next()?;
        lines.next(); // column header
        Some(
            lines
                .take_while(|line| !line.trim().is_empty())
                .map(|line| {
                    let fields: Vec<&str> = line.split_whitespace().collect();
                    let offset = u64::from_str_radix(fields[0], 16).unwrap();
                    let target = if fields.len() >= 7 {
                        format!("{} + {}", fields[4], fields[6])
                    } else {
                        // `R_AARCH64_RELATIVE <addend>`: no symbol.
                        format!("+ {}", fields.last().unwrap())
                    };
                    (offset, fields[2].to_string(), target)
                })
                .collect(),
        )
    }

    /// The object's `.rela.tdata` rows must be exactly `expected` (type and
    /// `symbol + hex addend`, as readelf prints them), at `offsets`.
    fn check_rela_tdata(
        text: &str,
        expected: &[&str],
        offsets: &[u64],
    ) -> Result<Vec<ReadelfRow>, String> {
        let rows = readelf_rows(text, ".rela.tdata").ok_or("no .rela.tdata section")?;
        let mut got: Vec<(u64, &str, &str)> = rows
            .iter()
            .map(|(offset, kind, target)| (*offset, kind.as_str(), target.as_str()))
            .collect();
        got.sort();
        let mut want: Vec<(u64, &str, &str)> = offsets
            .iter()
            .zip(expected)
            .map(|(offset, target)| (*offset, "R_AARCH64_ABS64", *target))
            .collect();
        want.sort();
        if got == want {
            Ok(rows)
        } else {
            Err(format!(".rela.tdata rows {got:?} != expected {want:?}"))
        }
    }

    const MODULE_ROWS: [&str; 3] = ["g_target + 0", "tls_fn + 0", "g_arr + 10"];

    /// Offsets of the module's template slots, from the in-repo reader.
    fn module_slot_offsets(object: &[u8]) -> Vec<u64> {
        let records = read_object_records(object).unwrap();
        TEMPLATE_SLOTS
            .iter()
            .map(|(holder, ..)| symbol_value(&records, holder).1)
            .collect()
    }

    /// `(vaddr, filesz)` of the image's `PT_TLS` segment.
    fn pt_tls(image: &Path) -> (u64, u64) {
        let text = readelf(&["-lW"], image);
        let line = text
            .lines()
            .find(|line| line.trim_start().starts_with("TLS "))
            .unwrap_or_else(|| panic!("{}: no PT_TLS", image.display()));
        let fields: Vec<&str> = line.split_whitespace().collect();
        let hex = |field: &str| u64::from_str_radix(field.trim_start_matches("0x"), 16).unwrap();
        (hex(fields[2]), hex(fields[4]))
    }

    /// Dynamic relocations of a linked image that patch its `PT_TLS`
    /// template, as `(type, target)`.
    fn dynamic_rows_in_tls(image: &Path) -> Vec<(String, String)> {
        let (vaddr, filesz) = pt_tls(image);
        let text = readelf(&["-rW"], image);
        let mut rows: Vec<(String, String)> = readelf_rows(&text, ".rela.dyn")
            .unwrap_or_default()
            .into_iter()
            .filter(|(offset, ..)| (vaddr..vaddr + filesz).contains(offset))
            .map(|(_, kind, target)| (kind, target))
            .collect();
        rows.sort();
        rows
    }

    /// Compile C `source` (already harness-expanded) to `object` with gcc
    /// and return its sorted `.rela.tdata` rows as `"TYPE symbol + addend"`.
    fn gcc_tdata_rows(label: &str, source: &Path, object: &Path, pic: bool) -> Vec<String> {
        let mut args = vec!["-O2", "-c"];
        if pic {
            args.push("-fPIC");
        }
        cc(&args, &[source], object);
        let text = readelf(&["-rW"], object);
        let mut rows: Vec<String> = readelf_rows(&text, ".rela.tdata")
            .unwrap_or_else(|| panic!("{label}: gcc emitted no .rela.tdata:\n{text}"))
            .into_iter()
            .map(|(_, kind, target)| format!("{kind} {target}"))
            .collect();
        rows.sort();
        println!("{label} (gcc, pic={pic}) .rela.tdata: {rows:?}");
        rows
    }

    /// The gcc twin's rows: the object-level oracle for trust-cg's rows.
    fn gcc_twin_rows(dir: &Path, pic: bool) -> Vec<String> {
        let source = write(dir, "gcc-twin.c", GCC_TWIN.as_bytes());
        let object = dir.join(if pic { "gcc-twin-pic.o" } else { "gcc-twin.o" });
        gcc_tdata_rows("gcc twin", &source, &object, pic)
    }

    /// Compile [`ORACLE`] and require its template to be a real relocated
    /// `.tdata` template with the module's rows (not folded to constants).
    fn oracle_object(dir: &Path, pic: bool) -> PathBuf {
        let source = c_source(dir, "oracle.c", ORACLE);
        let object = dir.join(if pic { "oracle-pic.o" } else { "oracle.o" });
        assert_eq!(
            gcc_tdata_rows("C oracle", &source, &object, pic),
            sorted_abs64_rows(&MODULE_ROWS),
            "the C oracle's template must stay a relocated .tdata template"
        );
        object
    }

    fn sorted_abs64_rows(targets: &[&str]) -> Vec<String> {
        let mut rows: Vec<String> = targets
            .iter()
            .map(|target| format!("R_AARCH64_ABS64 {target}"))
            .collect();
        rows.sort();
        rows
    }

    fn run_driver(binary: &Path, args: &[&Path]) -> Output {
        let mut command = Command::new(binary);
        for arg in args {
            command.arg(arg);
        }
        command_output(&mut command, native_process::codegen_run_timeout())
    }

    fn assert_passes(label: &str, output: &Output, expected: &str) {
        assert!(
            output.status.success(),
            "{label}: {}\nstdout={}\nstderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout).trim(),
            expected,
            "{label}"
        );
    }

    /// Static (local-exec) and PIE executables through the trust-ir route:
    /// every thread's template equals the C oracle's at O0-O3; readelf shows
    /// the gcc twin's `.rela.tdata` rows in each object, none left for the
    /// non-PIE image and one `R_AARCH64_RELATIVE` per template slot inside the
    /// PIE's `PT_TLS` (trust-cg's three and the oracle's three).
    #[test]
    fn compiler_route_templates_match_c_oracle_in_executables_at_o0_through_o3() {
        let dir = scratch("exec");
        let dir = dir.path();
        let gcc_rows = gcc_twin_rows(dir, false);
        assert_eq!(gcc_rows, sorted_abs64_rows(&MODULE_ROWS), "gcc twin rows");
        let oracle = oracle_object(dir, false);
        let driver = c_source(dir, "driver.c", EXEC_DRIVER);
        let mut executions = 0;
        for (model, link) in [
            (RelocationModel::Static, "-no-pie"),
            (RelocationModel::Pie, "-pie"),
        ] {
            for opt_level in LEVELS {
                let label = format!("{model} {opt_level:?}");
                let bytes = compile_linux(&tls_template_module(), opt_level, model);
                let object = write(dir, &format!("cg-{model}-{opt_level:?}.o"), &bytes);
                log_object(&label, &object);
                let text = readelf(&["-rW"], &object);
                let rows = check_rela_tdata(&text, &MODULE_ROWS, &module_slot_offsets(&bytes))
                    .unwrap_or_else(|error| panic!("{label}: {error}\n{text}"));
                println!("{label} .rela.tdata: {rows:?}");
                let binary = dir.join(format!("exec-{model}-{opt_level:?}"));
                cc(
                    &["-O2", "-pthread", link],
                    &[&driver, &oracle, &object],
                    &binary,
                );
                let dynamic = dynamic_rows_in_tls(&binary);
                if model == RelocationModel::Pie {
                    assert_eq!(
                        dynamic.len(),
                        6,
                        "{label}: one RELATIVE per slot in PT_TLS: {dynamic:?}"
                    );
                    assert!(
                        dynamic.iter().all(|(kind, _)| kind == "R_AARCH64_RELATIVE"),
                        "{label}: {dynamic:?}"
                    );
                } else {
                    assert!(dynamic.is_empty(), "{label}: {dynamic:?}");
                }
                assert_passes(&label, &run_driver(&binary, &[]), EXEC_PASS);
                executions += 1;
            }
        }
        assert_eq!(executions, 8);
        println!(
            "trust-ir route executables: {executions} executions (three live threads and a late thread each)"
        );
    }

    /// A `pic` (TLSDESC) shared object `dlopen`ed by a C driver: a thread
    /// that predates the `dlopen` and three later threads start from the
    /// relocated template; the image carries TLSDESC and one dynamic
    /// `R_AARCH64_ABS64` per slot inside `PT_TLS`, trust-cg's and the C
    /// oracle's alike (the symbols are preemptible).
    #[test]
    fn compiler_route_templates_match_c_oracle_in_dlopened_shared_object_at_o0_through_o3() {
        let dir = scratch("dlopen");
        let dir = dir.path();
        let gcc_rows = gcc_twin_rows(dir, true);
        assert_eq!(
            gcc_rows,
            sorted_abs64_rows(&MODULE_ROWS),
            "gcc -fPIC twin rows"
        );
        let oracle = oracle_object(dir, true);
        let driver_source = c_source(dir, "driver.c", DLOPEN_DRIVER);
        let driver = dir.join("driver");
        cc(&["-O2", "-pthread"], &[&driver_source], &driver);
        let mut executions = 0;
        for opt_level in LEVELS {
            let label = format!("pic {opt_level:?}");
            let bytes = compile_linux(&tls_template_module(), opt_level, RelocationModel::Pic);
            let object = write(dir, &format!("cg-pic-{opt_level:?}.o"), &bytes);
            log_object(&label, &object);
            let text = readelf(&["-rW"], &object);
            let rows = check_rela_tdata(&text, &MODULE_ROWS, &module_slot_offsets(&bytes))
                .unwrap_or_else(|error| panic!("{label}: {error}\n{text}"));
            println!("{label} .rela.tdata: {rows:?}");
            let library = dir.join(format!("libcg-{opt_level:?}.so"));
            cc(
                &["-shared", "-pthread", "-Wl,-z,defs,-z,text,-z,now"],
                &[&object, &oracle],
                &library,
            );
            let dynamic = readelf(&["-rW", "--dynamic"], &library);
            assert!(!dynamic.contains("TEXTREL"), "{label}: text relocation");
            assert!(
                dynamic.contains("R_AARCH64_TLSDESC"),
                "{label}: the shared object reaches its thread-locals through TLS descriptors"
            );
            let in_tls = dynamic_rows_in_tls(&library);
            let mut want: Vec<(String, String)> = MODULE_ROWS
                .iter()
                .flat_map(|target| {
                    [
                        ("R_AARCH64_ABS64".to_string(), target.to_string()),
                        ("R_AARCH64_ABS64".to_string(), target.to_string()),
                    ]
                })
                .collect();
            want.sort();
            assert_eq!(in_tls, want, "{label}: dynamic template relocations");
            assert_passes(&label, &run_driver(&driver, &[&library]), DLOPEN_PASS);
            executions += 1;
        }
        assert_eq!(executions, 4);
        println!(
            "dlopened shared objects: {executions} executions (a pre-dlopen thread, three live threads and a late thread each)"
        );
    }

    /// The `Pipeline` object-global route with local-exec and initial-exec
    /// access, static and PIE links: the second template (non-zero `.tdata`
    /// offset, plain word between slots) matches the driver's C oracle.
    #[test]
    fn pipeline_route_templates_match_c_oracle_with_le_and_ie_at_o0_through_o3() {
        let dir = scratch("pipeline");
        let dir = dir.path();
        let expected = ["c_target + 0", "c_fn + 0", "c_arr + 10", "cg_word + 8"];
        let driver_source = c_source(dir, "driver.c", PIPELINE_DRIVER);
        let driver = dir.join("driver.o");
        assert_eq!(
            gcc_tdata_rows("pipeline C oracle", &driver_source, &driver, false),
            sorted_abs64_rows(&expected),
            "the driver's C oracle template carries the same rows as trust-cg's"
        );
        let mut executions = 0;
        for model in [
            trust_cg_ir::TlsModel::LocalExec,
            trust_cg_ir::TlsModel::InitialExec,
        ] {
            for opt_level in LEVELS {
                let bytes = pipeline_route_object(opt_level, model);
                let records = read_object_records(&bytes).unwrap();
                let base = symbol_value(&records, "cg_tls_mixed").1;
                let offsets: Vec<u64> = PIPELINE_ROUTE_SLOTS
                    .iter()
                    .map(|(_, slot, ..)| base + slot)
                    .collect();
                let object = write(dir, &format!("cg-{model:?}-{opt_level:?}.o"), &bytes);
                log_object(&format!("pipeline {model:?} {opt_level:?}"), &object);
                let text = readelf(&["-rW"], &object);
                let rows = check_rela_tdata(&text, &expected, &offsets)
                    .unwrap_or_else(|error| panic!("{model:?} {opt_level:?}: {error}\n{text}"));
                println!("pipeline {model:?} {opt_level:?} .rela.tdata: {rows:?}");
                for link in ["-no-pie", "-pie"] {
                    let label = format!("pipeline {model:?} {opt_level:?} {link}");
                    let binary = dir.join(format!("pipeline-{model:?}-{opt_level:?}{link}"));
                    cc(&["-O2", "-pthread", link], &[&driver, &object], &binary);
                    assert_passes(&label, &run_driver(&binary, &[]), PIPELINE_PASS);
                    executions += 1;
                }
            }
        }
        assert_eq!(executions, 16);
        println!(
            "pipeline route executables: {executions} executions (three live threads and a late thread each)"
        );
    }

    /// Negative control: drop the last `.rela.tdata` record by shrinking the
    /// section's `sh_size` (a byte mutation that keeps a well-formed object).
    /// The readelf row check must fail, the in-repo reader must see one row
    /// fewer, and the linked driver must report the unrelocated slot.
    #[test]
    fn dropping_one_rela_tdata_record_fails_the_readelf_row_and_the_driver() {
        let dir = scratch("mutation");
        let dir = dir.path();
        let oracle = oracle_object(dir, false);
        let driver = c_source(dir, "driver.c", EXEC_DRIVER);
        for opt_level in LEVELS {
            let label = format!("mutant {opt_level:?}");
            let mut bytes =
                compile_linux(&tls_template_module(), opt_level, RelocationModel::Static);
            let offsets = module_slot_offsets(&bytes);
            let text = readelf(&["-rW"], &write(dir, "intact.o", &bytes));
            let rows = check_rela_tdata(&text, &MODULE_ROWS, &offsets)
                .unwrap_or_else(|error| panic!("{label}: intact object: {error}"));
            let (_, _, dropped) = rows.last().unwrap().clone();
            let slot = MODULE_ROWS
                .iter()
                .position(|target| *target == dropped)
                .unwrap();

            shrink_section(&mut bytes, ".rela.tdata", 24);
            let records = read_object_records(&bytes).unwrap();
            assert_eq!(
                rows_in_section(&records, ".tdata"),
                TEMPLATE_SLOTS.len() - 1,
                "{label}: the mutant carries one template relocation fewer"
            );
            let object = write(dir, &format!("mutant-{opt_level:?}.o"), &bytes);
            log_object(&label, &object);
            let text = readelf(&["-rW"], &object);
            let error = check_rela_tdata(&text, &MODULE_ROWS, &offsets)
                .expect_err("the readelf row check must reject the mutant");
            println!("{label}: readelf row check rejected the mutant: {error}");

            let binary = dir.join(format!("mutant-{opt_level:?}"));
            cc(
                &["-O2", "-pthread", "-no-pie"],
                &[&driver, &oracle, &object],
                &binary,
            );
            let output = run_driver(&binary, &[]);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                output.status.code(),
                Some(MAIN_TEMPLATE_MISMATCH),
                "{label}: the driver must report the unrelocated slot: stderr={stderr}"
            );
            assert!(
                stderr.contains(&format!("main: template slot {slot}: cg=(nil)")),
                "{label}: {stderr}"
            );
            println!("{label}: driver rejected the mutant: {}", stderr.trim());
        }
    }

    /// Driver-sensitivity control (not a compiler negative): the same module
    /// with `tp`/`tf`/`tq` deliberately NOT thread-local links against the
    /// same driver, which must fail its isolation check at every level.
    #[test]
    fn driver_isolation_check_rejects_a_non_tls_twin_module() {
        let dir = scratch("non-tls");
        let dir = dir.path();
        let oracle = oracle_object(dir, false);
        let driver = c_source(dir, "driver.c", EXEC_DRIVER);
        let mut module = tls_template_module();
        for global in &mut module.globals[2..5] {
            global.tls = None;
        }
        for opt_level in LEVELS {
            let label = format!("non-TLS twin {opt_level:?}");
            let bytes = compile_linux(&module, opt_level, RelocationModel::Static);
            let records = read_object_records(&bytes).unwrap();
            assert_eq!(rows_in_section(&records, ".tdata"), 0, "{label}");
            assert_eq!(rows_in_section(&records, ".data"), 3, "{label}");
            let object = write(dir, &format!("non-tls-{opt_level:?}.o"), &bytes);
            let binary = dir.join(format!("non-tls-{opt_level:?}"));
            cc(
                &["-O2", "-pthread", "-no-pie"],
                &[&driver, &oracle, &object],
                &binary,
            );
            let output = run_driver(&binary, &[]);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                output
                    .status
                    .code()
                    .is_some_and(|code| ISOLATION_FAILURES.contains(&code))
                    && stderr.contains("isolation"),
                "{label}: the isolation check must reject shared storage: {} stderr={stderr}",
                output.status
            );
            println!("{label}: driver rejected shared storage: {}", stderr.trim());
        }
    }

    fn rows_in_section(records: &ElfObjectRecords, section: &str) -> usize {
        rows(records)
            .iter()
            .filter(|row| row.section == section)
            .count()
    }

    /// Reduce the named section's `sh_size` by `bytes` (an independent
    /// section-header walk over the fixed ELF64 little-endian layout).
    fn shrink_section(object: &mut [u8], name: &str, bytes: u64) {
        let u16_at = |b: &[u8], off: usize| u16::from_le_bytes([b[off], b[off + 1]]) as usize;
        let u32_at = |b: &[u8], off: usize| u32::from_le_bytes(b[off..off + 4].try_into().unwrap());
        let u64_at = |b: &[u8], off: usize| u64::from_le_bytes(b[off..off + 8].try_into().unwrap());
        let shoff = u64_at(object, 0x28) as usize;
        let shentsize = u16_at(object, 0x3a);
        let shnum = u16_at(object, 0x3c);
        let shstrndx = u16_at(object, 0x3e);
        let strtab = u64_at(object, shoff + shstrndx * shentsize + 0x18) as usize;
        let header = (0..shnum)
            .map(|index| shoff + index * shentsize)
            .find(|&header| {
                let start = strtab + u32_at(object, header) as usize;
                let end = start + object[start..].iter().position(|&c| c == 0).unwrap();
                &object[start..end] == name.as_bytes()
            })
            .unwrap_or_else(|| panic!("section {name} missing"));
        let size = u64_at(object, header + 0x20);
        assert!(size >= bytes);
        object[header + 0x20..header + 0x28].copy_from_slice(&(size - bytes).to_le_bytes());
    }

    // -------------------------------------------------------------------------
    // JIT data image on Linux (the Darwin rows, verbatim)
    // -------------------------------------------------------------------------

    use std::collections::HashMap;
    use std::sync::atomic::{AtomicI64, Ordering};
    use trust_cg_codegen::Target;

    static HOST_VALUE: AtomicI64 = AtomicI64::new(4321);

    fn jit_externs() -> HashMap<String, *const u8> {
        HashMap::from([(
            "host_value".to_string(),
            &HOST_VALUE as *const AtomicI64 as *const u8,
        )])
    }

    /// A JIT body reads and writes a module global, addresses a string
    /// constant and a function-pointer table placed in the JIT data image,
    /// and loads a data import through a GOT slot; the buffer records the
    /// image identity. Unchecked execution: no obligation models the image.
    #[test]
    fn jit_reads_and_writes_module_globals_and_string_constant_at_o0_through_o3() {
        let module = jit_globals_module();
        let externs = jit_externs();
        for opt_level in LEVELS {
            HOST_VALUE.store(4321, Ordering::SeqCst);
            let config = CompilerConfig {
                opt_level,
                ..CompilerConfig::jit_fast(Target::Aarch64)
            };
            let result = Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &externs)
                .unwrap_or_else(|error| panic!("{opt_level:?}: JIT compile failed: {error}"));
            let buffer = result.buffer;
            let bump = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn(i64) -> i64>("bump")
                    .expect("bump")
            };
            let str_ptr = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn() -> *const u8>("str_ptr")
                    .expect("str_ptr")
            };
            let str_byte1 = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn() -> i64>("str_byte1")
                    .expect("str_byte1")
            };
            let tbl_read = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn() -> *const u8>("tbl_read")
                    .expect("tbl_read")
            };
            let read_host = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn() -> i64>("read_host")
                    .expect("read_host")
            };
            let counter = buffer
                .data_symbol_ptr("g_counter")
                .expect("g_counter placed") as *mut i64;
            let text = buffer.data_symbol_ptr("g_str").expect("g_str placed");
            assert!(buffer.data_symbol_ptr("host_value").is_none());
            assert!(buffer.data_symbol_ptr("bump").is_none());
            let (data_base, data_len) = buffer.data_image_range().expect("data mapping");
            assert!(
                (counter as u64) >= data_base && (counter as u64) < data_base + data_len as u64
            );

            assert_eq!((*bump.as_ref())(5), 105, "{opt_level:?}");
            assert_eq!(unsafe { counter.read() }, 105, "{opt_level:?}");
            unsafe { counter.write(200) };
            assert_eq!(
                (*bump.as_ref())(1),
                201,
                "{opt_level:?}: host write seen by the JIT"
            );
            assert_eq!((*str_ptr.as_ref())(), text, "{opt_level:?}");
            let bytes = unsafe { std::slice::from_raw_parts(text, 6) };
            assert_eq!(bytes, b"hello\0", "{opt_level:?}");
            assert_eq!((*str_byte1.as_ref())(), i64::from(b'e'), "{opt_level:?}");
            assert_eq!(
                (*tbl_read.as_ref())(),
                buffer
                    .get_fn_ptr_bound("bump")
                    .expect("bump address")
                    .as_ptr(),
                "{opt_level:?}"
            );
            assert_eq!((*read_host.as_ref())(), 4321, "{opt_level:?}");
            HOST_VALUE.store(-7, Ordering::SeqCst);
            assert_eq!((*read_host.as_ref())(), -7, "{opt_level:?}");

            let record = buffer.data_image().expect("data image record");
            assert_eq!(record.global_count, 3, "{opt_level:?}");
            assert_eq!(record.import_count, 1, "{opt_level:?}");
            assert_eq!(record.relocation_count, 1, "{opt_level:?}");
            assert!(record.direct_site_count >= 2, "{opt_level:?}: {record:?}");
            assert_eq!(record.got_slot_count, 1, "{opt_level:?}: {record:?}");
            assert_eq!(record.manifest_sha256.len(), 64);
            let metadata = buffer.replay_report_metadata();
            assert_eq!(
                metadata.properties.get("jit_data_image_manifest_sha256"),
                Some(&format!("sha256:{}", record.manifest_sha256)),
                "{opt_level:?}"
            );
            assert_eq!(
                metadata.properties.get("jit_got_slot_count"),
                Some(&"1".to_string())
            );
        }
    }

    /// The image identity binds the initial bytes and the relocation list.
    #[test]
    fn jit_data_image_identity_binds_bytes_and_relocations() {
        let module = jit_globals_module();
        let mut changed = jit_globals_module();
        changed.globals[0].initializer = Some(Constant::Int(101));
        let compile = |module: &Module| {
            Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(module, &jit_externs())
                .expect("JIT compile")
                .buffer
                .data_image()
                .expect("data image")
                .clone()
        };
        let first = compile(&module);
        let again = compile(&module);
        let other = compile(&changed);
        assert_eq!(first, again);
        assert_ne!(first.manifest_sha256, other.manifest_sha256);
        assert_eq!(first.image_len, other.image_len);
    }

    // -------------------------------------------------------------------------
    // SymbolAddr with a non-zero addend in a body
    // -------------------------------------------------------------------------

    const ADDEND_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern const int64_t g_arr[4];
extern int64_t third(void);
extern const void *third_addr(void);
int main(void) {
    if (third_addr() != (const void *)&g_arr[2]) { printf("addr\n"); return 1; }
    if (third() != 30) { printf("value\n"); return 2; }
    printf("interior address: third=%lld same=%d\n", (long long)third(),
           third_addr() == (const void *)&g_arr[2]);
    return 0;
}
"#;

    /// A body-level `SymbolAddr` with addend 16 is the interior address
    /// gcc's `&g_arr[2]` names, in static and PIE executables at O0-O3.
    #[test]
    fn symbol_addr_with_addend_in_body_matches_c_oracle_at_o0_through_o3() {
        let dir = scratch("addend");
        let dir = dir.path();
        let driver = c_source(dir, "driver.c", ADDEND_DRIVER);
        let mut executions = 0;
        for (model, link) in [
            (RelocationModel::Static, "-no-pie"),
            (RelocationModel::Pie, "-pie"),
        ] {
            for opt_level in LEVELS {
                let label = format!("addend {model} {opt_level:?}");
                let object = write(
                    dir,
                    &format!("addend-{model}-{opt_level:?}.o"),
                    &compile_linux(&addend_module(), opt_level, model),
                );
                let binary = dir.join(format!("addend-{model}-{opt_level:?}"));
                cc(&["-O2", link], &[&driver, &object], &binary);
                assert_passes(
                    &label,
                    &run_driver(&binary, &[]),
                    "interior address: third=30 same=1",
                );
                executions += 1;
            }
        }
        assert_eq!(executions, 8);
    }

    // -------------------------------------------------------------------------
    // Hidden data visibility and non-vacuous data retention
    // -------------------------------------------------------------------------

    const HIDDEN_DRIVER: &str = r#"
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    void *lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!lib) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 3; }
    int64_t (*read_hidden)(void) = (int64_t (*)(void))dlsym(lib, "read_hidden");
    int64_t *(*hidden_addr)(void) = (int64_t *(*)(void))dlsym(lib, "hidden_addr");
    if (!read_hidden || !hidden_addr) return 4;
    if (dlsym(lib, "g_hidden")) { printf("hidden data is exported\n"); return 5; }
    if (read_hidden() != 6 || *hidden_addr() != 6) return 6;
    *hidden_addr() = 66;
    if (read_hidden() != 66) return 7;
    puts("hidden data stays local to its shared object");
    return dlclose(lib) ? 8 : 0;
}
"#;

    const GC_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern int64_t read_hidden(void);
int main(void) {
    if (read_hidden() != 6) return 1;
    puts("gc-sections image runs");
    return 0;
}
"#;

    /// Defined symbol names in a linked image's `.symtab`.
    fn defined_symbols(image: &Path) -> Vec<String> {
        readelf(&["-sW"], image)
            .lines()
            .filter_map(|line| {
                let columns: Vec<&str> = line.split_whitespace().collect();
                (columns.len() == 8 && columns[0].ends_with(':') && columns[6] != "UND")
                    .then(|| columns[7].to_string())
            })
            .collect()
    }

    /// A hidden data global is absent from a `pic` shared object's `.dynsym`
    /// and from `dlsym`, while the functions that address it work; under
    /// `-Wl,--gc-sections` the retained, unreferenced `g_used` survives while
    /// the unreferenced, unretained `g_dropped` is collected (the control that
    /// makes the retention check non-vacuous).
    #[test]
    fn hidden_data_stays_local_and_retained_data_survives_gc_sections_at_o0_through_o3() {
        let dir = scratch("attributes");
        let dir = dir.path();
        let hidden_driver = c_source(dir, "hidden.c", HIDDEN_DRIVER);
        let hidden_binary = dir.join("hidden-driver");
        cc(&["-O2"], &[&hidden_driver], &hidden_binary);
        let gc_driver = c_source(dir, "gc.c", GC_DRIVER);
        for opt_level in LEVELS {
            let label = format!("attributes {opt_level:?}");
            let pic = write(
                dir,
                &format!("attributes-pic-{opt_level:?}.o"),
                &compile_linux(&attributes_module(), opt_level, RelocationModel::Pic),
            );
            let library = dir.join(format!("libattributes-{opt_level:?}.so"));
            cc(&["-shared", "-Wl,-z,defs,-z,text"], &[&pic], &library);
            let dynsym = readelf(&["--dyn-syms", "-W"], &library);
            assert!(
                dynsym.contains(" read_hidden") && !dynsym.contains(" g_hidden"),
                "{label}: hidden data must not be exported:\n{dynsym}"
            );
            assert_passes(
                &label,
                &run_driver(&hidden_binary, &[&library]),
                "hidden data stays local to its shared object",
            );

            let object = write(
                dir,
                &format!("attributes-{opt_level:?}.o"),
                &compile_linux(&attributes_module(), opt_level, RelocationModel::Static),
            );
            let binary = dir.join(format!("gc-{opt_level:?}"));
            cc(
                &["-O2", "-no-pie", "-Wl,--gc-sections"],
                &[&gc_driver, &object],
                &binary,
            );
            let defined = defined_symbols(&binary);
            assert!(
                defined.iter().any(|name| name == "g_used"),
                "{label}: the retained global was collected: {defined:?}"
            );
            assert!(
                !defined.iter().any(|name| name == "g_dropped"),
                "{label}: --gc-sections kept the unretained control, so the retention check is vacuous: {defined:?}"
            );
            assert_passes(&label, &run_driver(&binary, &[]), "gc-sections image runs");
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
