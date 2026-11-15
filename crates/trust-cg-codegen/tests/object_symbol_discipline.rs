// trust-cg-codegen/tests/object_symbol_discipline.rs
//
// The AArch64 objects `Compiler::compile` emits can be partitioned into the
// module's functions by symbol alone, and the same module always compiles to
// the same bytes.
//
// * Determinism: one module (module-local, hidden, ODR-weak and External
//   functions, direct calls, address takings, a function-pointer global, a
//   dense switch whose jump table lies in its function's body, and enough
//   functions for the parallel emitter) is compiled several times by fresh
//   compilers on different threads, for AArch64 Mach-O and ELF, at O0 and O2,
//   sequential and parallel: every object of one configuration is
//   byte-identical.
// * Symbol discipline, read back by the crate's independent object readers:
//   every instruction section starts at a function symbol, holds no other
//   symbol, and no two symbols share an address; each function has exactly
//   one symbol, with the binding its linkage and visibility dictate (a hidden
//   External definition is Mach-O `N_EXT | N_PEXT`, ELF `STB_GLOBAL` +
//   `STV_HIDDEN`). `Compiler::compile` refuses an object that breaks this
//   (`CompileError::AotObjectSymbolDisciplineViolated`; the refusal side is
//   unit-tested beside the check in `compiler.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, SwitchCase, Ty, ValueId, Visibility,
};

const DARWIN: &str = "aarch64-apple-darwin";
const LINUX: &str = "aarch64-unknown-linux-gnu";

/// External `pad_<n>` fillers: enough functions for the parallel emitter
/// (`worker_count_for_items` needs at least 32 items).
const PADDING: u32 = 32;

/// `x + constant`, returned.
fn add_constant_body(constant: i128) -> Vec<Block> {
    vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(constant),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }]
}

/// The module both tests compile. Functions, by id:
///
/// * 0-3: `helper_internal` (Internal), `helper_private` (Private),
///   `helper_hidden` (External, Hidden) and `helper_odr` (LinkOnceOdr),
///   computing `x + 1` .. `x + 4`;
/// * 4: `dense_switch(x)`, a six-case dense switch (a jump table);
/// * 5: `entry(x)`, which calls 0-4 and sums the results;
/// * 6: `address_of_internal()`, the address of `helper_internal`;
/// * 7 onward: `pad_<n>(x) = x + n`, External;
///
/// plus the External global `helper_slot`, initialized with
/// `helper_private`'s address (a `SymbolAddr`).
fn discipline_module() -> Module {
    let mut module = Module::new("object_symbol_discipline");
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let pointer = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for (id, name, linkage, visibility) in [
        (0, "helper_internal", Linkage::Internal, Visibility::Default),
        (1, "helper_private", Linkage::Private, Visibility::Default),
        (2, "helper_hidden", Linkage::External, Visibility::Hidden),
        (3, "helper_odr", Linkage::LinkOnceOdr, Visibility::Default),
    ] {
        let mut function = Function::new(FuncId::new(id), name, unary, BlockId::new(0));
        function.linkage = linkage;
        function.visibility = visibility;
        function.blocks = add_constant_body(i128::from(id) + 1);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }

    // 4. A dense switch: arms 1..=6 return 100 + 11 * case, default 7 returns -1.
    let mut switch = Function::new(FuncId::new(4), "dense_switch", unary, BlockId::new(0));
    let cases: Vec<SwitchCase> = (0..6)
        .map(|case| SwitchCase {
            value: Constant::Int(case),
            target: BlockId::new(case as u32 + 1),
            args: vec![],
        })
        .collect();
    let mut blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(7),
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    for (arm, value) in (1..=7).zip((0..6).map(|case| 100 + 11 * case).chain([-1])) {
        blocks.push(Block {
            id: BlockId::new(arm),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(value),
                })
                .with_result(ValueId::new(arm + 10)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(arm + 10)],
                }),
            ],
        });
    }
    switch.blocks = blocks;
    module
        .try_add_function(switch)
        .expect("Module::try_add_function: test fixture");

    // 5. `entry(x)`: the sum of every helper's and the switch's result.
    let mut entry = Function::new(FuncId::new(5), "entry", unary, BlockId::new(0));
    let mut body = Vec::new();
    for callee in 0..5u32 {
        body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(callee),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(10 + callee)),
        );
    }
    let mut sum = ValueId::new(10);
    for callee in 1..5u32 {
        let next = ValueId::new(20 + callee);
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: sum,
                rhs: ValueId::new(10 + callee),
            })
            .with_result(next),
        );
        sum = next;
    }
    body.push(InstrNode::new(Inst::Return { values: vec![sum] }));
    entry.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body,
    }];
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");

    // 6. The address of the Internal helper.
    let mut address = Function::new(
        FuncId::new(6),
        "address_of_internal",
        pointer,
        BlockId::new(0),
    );
    address.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(unary),
                value: Constant::FnDef(FuncId::new(0)),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ReifyFnPointer,
                src_ty: Ty::Func(unary),
                dst_ty: Ty::Ptr,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(address)
        .expect("Module::try_add_function: test fixture");

    for pad in 0..PADDING {
        let mut function = Function::new(
            FuncId::new(7 + pad),
            format!("pad_{pad}"),
            unary,
            BlockId::new(0),
        );
        function.blocks = add_constant_body(i128::from(pad) + 10);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
    }

    module.globals.push(Global {
        name: "helper_slot".into(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: Some(Constant::SymbolAddr {
            symbol: "helper_private".into(),
            addend: 0,
        }),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    module
}

fn config(opt_level: OptLevel, parallel: bool) -> CompilerConfig {
    CompilerConfig {
        opt_level,
        parallel,
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    }
}

fn compile(triple: &str, config: CompilerConfig, module: &Module) -> CompilationResult {
    Compiler::new_for_target_spec(config, TargetSpec::parse(triple).expect("triple"))
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .unwrap_or_else(|error| panic!("{triple}: {error:?}"))
}

/// The emission path `Compiler::compile` records for the object.
fn emission_path(result: &CompilationResult) -> String {
    result
        .trace
        .as_ref()
        .expect("CompilerTraceLevel::Full records a trace")
        .entries
        .iter()
        .find(|entry| entry.phase == "compile_module")
        .and_then(|entry| entry.detail.clone())
        .expect("the compile_module trace entry names its emission path")
}

/// The same module compiled by fresh compilers on three threads is the same
/// object, byte for byte, for every format, optimization level and emission
/// path (the trace confirms the parallel emitter ran when asked).
#[test]
fn module_object_is_deterministic() {
    let module = discipline_module();
    for triple in [DARWIN, LINUX] {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for parallel in [false, true] {
                let label = format!("{triple} {opt_level:?} parallel={parallel}");
                let first = compile(triple, config(opt_level, parallel), &module);
                let path = emission_path(&first);
                assert!(
                    path.contains(if parallel {
                        "parallel preparation and emission"
                    } else {
                        "sequential preparation and emission"
                    }),
                    "{label}: {path}"
                );
                let others: Vec<Vec<u8>> = std::thread::scope(|scope| {
                    let handles: Vec<_> = (0..2)
                        .map(|_| {
                            scope.spawn(|| {
                                compile(triple, config(opt_level, parallel), &module).object_code
                            })
                        })
                        .collect();
                    handles
                        .into_iter()
                        .map(|handle| handle.join().expect("compile thread"))
                        .collect()
                });
                for (index, other) in others.iter().enumerate() {
                    assert!(
                        *other == first.object_code,
                        "{label}: recompile {index} differs from the first object ({} vs {} \
                         bytes, first difference at byte {:?})",
                        other.len(),
                        first.object_code.len(),
                        other
                            .iter()
                            .zip(&first.object_code)
                            .position(|(left, right)| left != right)
                    );
                }
            }
        }
    }
}

/// A function's symbol as the test reads it: the instruction section it is
/// defined in (by label), its offset there, and its binding spelled per
/// format.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TextSymbol {
    section: String,
    offset: u64,
    binding: String,
}

/// Every symbol defined in an instruction section of `object`, by name
/// (Mach-O names without their `_`), plus each instruction section's size.
/// Panics on a name defined twice.
fn text_symbols(
    triple: &str,
    object: &[u8],
) -> (BTreeMap<String, TextSymbol>, BTreeMap<String, u64>) {
    let mut symbols = BTreeMap::new();
    let mut sections = BTreeMap::new();
    if triple == DARWIN {
        const S_ATTR_PURE_INSTRUCTIONS: u32 = 0x8000_0000;
        const S_ATTR_SOME_INSTRUCTIONS: u32 = 0x0000_0400;
        const N_WEAK_DEF: u16 = 0x0080;
        let records =
            trust_cg_codegen::macho::reparse::read_object_records(object).expect("Mach-O object");
        for section in &records.sections {
            if section.flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS) != 0 {
                sections.insert(
                    format!("{},{}", section.segname, section.sectname),
                    section.size,
                );
            }
        }
        for symbol in &records.symbols {
            if !symbol.is_section_definition() {
                continue;
            }
            let section = records.section(symbol.n_sect).expect("symbol section");
            let label = format!("{},{}", section.segname, section.sectname);
            if !sections.contains_key(&label) {
                continue;
            }
            let name = symbol.name.strip_prefix('_').expect("C symbol").to_owned();
            let binding = format!(
                "n_type={:#04x}{}",
                symbol.n_type,
                if symbol.n_desc & N_WEAK_DEF != 0 {
                    " weak_def"
                } else {
                    ""
                }
            );
            let previous = symbols.insert(
                name.clone(),
                TextSymbol {
                    section: label,
                    offset: symbol.n_value - section.addr,
                    binding,
                },
            );
            assert!(previous.is_none(), "`{name}` is defined twice");
        }
    } else {
        const SHF_EXECINSTR: u64 = 0x4;
        const STT_SECTION: u8 = 3;
        const STT_FILE: u8 = 4;
        let records =
            trust_cg_codegen::elf::reparse::read_object_records(object).expect("ELF object");
        for section in &records.sections {
            if section.sh_flags & SHF_EXECINSTR != 0 {
                sections.insert(section.name.clone(), section.size);
            }
        }
        for symbol in &records.symbols {
            if matches!(symbol.symbol_type, STT_SECTION | STT_FILE) {
                continue;
            }
            let Some(section) = symbol
                .defining_section()
                .map(|index| &records.sections[index])
            else {
                continue;
            };
            if section.sh_flags & SHF_EXECINSTR == 0 {
                continue;
            }
            let binding = format!(
                "bind={} type={} vis={}",
                symbol.binding, symbol.symbol_type, symbol.visibility
            );
            let previous = symbols.insert(
                symbol.name.clone(),
                TextSymbol {
                    section: section.name.clone(),
                    offset: symbol.value,
                    binding,
                },
            );
            assert!(previous.is_none(), "`{}` is defined twice", symbol.name);
        }
    }
    (symbols, sections)
}

/// Every instruction section of every object starts at a function symbol and
/// holds only the module's function symbols, at distinct offsets, each with
/// the binding its linkage and visibility dictate. Checked for both formats,
/// sequential and parallel, at O0 and O2, for Mach-O also with DWARF
/// (`emit_debug`) and for ELF also with function sections.
#[test]
fn every_text_symbol_is_one_function_at_its_own_address() {
    let module = discipline_module();
    let function_names: Vec<&str> = module
        .functions
        .iter()
        .map(|function| function.name.as_str())
        .collect();
    let mut configurations = Vec::new();
    for triple in [DARWIN, LINUX] {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for parallel in [false, true] {
                configurations.push((triple, config(opt_level, parallel)));
            }
        }
    }
    // DWARF on Mach-O (ELF refuses `-g` for COMDAT text, which `helper_odr`
    // needs).
    let mut debug = config(OptLevel::O2, false);
    debug.emit_debug = true;
    configurations.push((DARWIN, debug));
    let mut sectioned = config(OptLevel::O2, false);
    sectioned.function_sections = true;
    configurations.push((LINUX, sectioned));

    for (triple, config) in configurations {
        let label = format!(
            "{triple} {:?} parallel={} debug={} function_sections={}",
            config.opt_level, config.parallel, config.emit_debug, config.function_sections
        );
        let function_sections = config.function_sections;
        let object = compile(triple, config, &module).object_code;
        let (symbols, sections) = text_symbols(triple, &object);
        let defined: Vec<&str> = symbols.keys().map(String::as_str).collect();
        let mut expected = function_names.clone();
        expected.sort_unstable();
        assert_eq!(
            defined, expected,
            "{label}: the text symbols are the functions"
        );
        for (section, size) in &sections {
            let mut offsets: Vec<u64> = symbols
                .values()
                .filter(|symbol| &symbol.section == section)
                .map(|symbol| symbol.offset)
                .collect();
            offsets.sort_unstable();
            if *size == 0 {
                assert!(offsets.is_empty(), "{label}: {section}");
                continue;
            }
            assert_eq!(
                offsets.first(),
                Some(&0),
                "{label}: {section} starts at a symbol"
            );
            assert!(
                offsets.windows(2).all(|pair| pair[0] < pair[1]),
                "{label}: {section} symbols at distinct offsets: {offsets:?}"
            );
            assert!(
                offsets.iter().all(|offset| offset < size),
                "{label}: {section}"
            );
        }
        let binding = |name: &str| symbols[name].binding.as_str();
        if triple == DARWIN {
            assert_eq!(binding("helper_internal"), "n_type=0x0e", "{label}");
            assert_eq!(binding("helper_private"), "n_type=0x0e", "{label}");
            assert_eq!(
                binding("helper_hidden"),
                "n_type=0x1f",
                "{label}: N_EXT | N_PEXT"
            );
            assert_eq!(binding("helper_odr"), "n_type=0x0f weak_def", "{label}");
            assert_eq!(binding("entry"), "n_type=0x0f", "{label}");
        } else {
            assert_eq!(binding("helper_internal"), "bind=0 type=2 vis=0", "{label}");
            assert_eq!(binding("helper_private"), "bind=0 type=2 vis=0", "{label}");
            assert_eq!(
                binding("helper_hidden"),
                "bind=1 type=2 vis=2",
                "{label}: STV_HIDDEN"
            );
            assert_eq!(binding("helper_odr"), "bind=2 type=2 vis=0", "{label}");
            assert_eq!(binding("entry"), "bind=1 type=2 vis=0", "{label}");
            // The ODR body lands in its own COMDAT section; with function
            // sections every body does.
            assert_ne!(symbols["helper_odr"].section, ".text", "{label}");
            if function_sections {
                assert!(
                    symbols.values().all(|symbol| symbol.section != ".text"),
                    "{label}"
                );
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
