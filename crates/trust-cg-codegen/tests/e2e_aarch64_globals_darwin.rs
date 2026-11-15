// trust-cg-codegen/tests/e2e_aarch64_globals_darwin.rs - Darwin AArch64
// globals: relocated TLS templates, JIT data images, SymbolAddr addends and
// data-symbol attributes (L05-P10).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Native aarch64-apple-darwin evidence for the global-variable surface the
//! L05-P10 ledger row names:
//!
//! * a thread-local whose initial-value template embeds symbol addresses
//!   (`__thread void *p = &x;`, a per-thread function pointer, an interior
//!   `&arr[2]`) relocates `__DATA,__thread_data`; a C driver checks every
//!   thread starts from the fixed-up template, that writes through the
//!   per-thread pointer land in the shared global, and that one thread's
//!   re-pointing never reaches another, linked by ld64 and by the in-repo
//!   standalone linker at O0-O3;
//! * the in-memory JIT publishes module globals in a JIT-owned data image
//!   (a mutable counter, a string constant, a function-pointer table and a
//!   data import bound through a GOT slot) and records the image, its
//!   relocation list and every patched site in the buffer's identity;
//! * `Constant::SymbolAddr` with a non-zero addend in a body is an interior
//!   address (`&arr + 16`), checked against clang's `&arr[2]`;
//! * explicit sections, hidden visibility, `#[used]` retention and weak
//!   definitions on DATA globals reach the object (`nm -m`, `otool -l`) and
//!   agree with a C driver that defines its own weak twin;
//! * the refusals that stay: `ExternalWeak` data on Mach-O, a thread-local
//!   in an explicit section, a pointer slot whose target is itself a
//!   thread-local (`[TCG-TLS-SLOT-TARGET]`, Mach-O and ELF), a JIT body
//!   naming a thread-local, and any data or GOT site under a verifying JIT
//!   request; the same module's ELF object relocates its template in
//!   `.rela.tdata` (executed natively in e2e_aarch64_globals_linux).
//!
//! This is execution evidence for these programs on this host, not a proof
//! of the linker, dyld or the JIT publication path.
#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

mod common;

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicI64, Ordering};
use std::time::Duration;

use common::rosetta::{
    TimedCommandOutput, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout,
};
use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::elf::reparse::read_object_records;
use trust_cg_codegen::jit::{JitCompiler, JitConfig, JitError};
use trust_cg_codegen::macho::linker::{DylibConfig, MachOParser, link_with_dylibs};
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, TlsModel, Ty, ValueId, Visibility,
};

const DARWIN: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// =============================================================================
// trust-ir module builders
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

fn symbol_addr(symbol: &str, addend: i64, result: u32) -> InstrNode {
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

/// A thread-local pointer whose template holds `symbol + addend`: a `ptr`
/// global's initializer is the address constant itself (trust-ir refuses a
/// one-element aggregate at `ptr` as `ConstTypeMismatch`, and every ingestion
/// entry refuses what the validator refuses, WS7.3).
fn tls_pointer_global(name: &str, symbol: &str, addend: i64) -> Global {
    let mut global = data_global(
        name,
        Ty::Ptr,
        true,
        Some(Constant::SymbolAddr {
            symbol: symbol.to_string(),
            addend,
        }),
    );
    // Any dynamic model selects the Darwin TLV path on Mach-O.
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
        Some(Constant::Array(vec![Constant::SymbolAddr {
            symbol: "bump".to_string(),
            addend: 0,
        }])),
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
            symbol_addr("g_str", 1, 0),
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

/// ```c
/// const int64_t g_arr[4] = {10, 20, 30, 40};
/// int64_t third(void)      { return *(const int64_t *)((const char *)g_arr + 16); }
/// const void *third_addr(void) { return (const char *)g_arr + 16; }
/// ```
fn addend_module() -> Module {
    let mut module = Module::new("symbol_addr_addend");
    let arr = i64_array_global(&mut module, "g_arr", [10, 20, 30, 40]);
    module.globals.push(arr);
    add_function(
        &mut module,
        "third",
        vec![],
        vec![Ty::I64],
        vec![symbol_addr("g_arr", 16, 0), load(Ty::I64, 0, 1), ret(1)],
    );
    add_function(
        &mut module,
        "third_addr",
        vec![],
        vec![Ty::Ptr],
        vec![symbol_addr("g_arr", 16, 0), ret(0)],
    );
    module
}

/// ```c
/// __attribute__((section("__DATA,__cgdata"))) int64_t g_sec = 5;
/// __attribute__((visibility("hidden"))) int64_t g_hidden = 6;
/// __attribute__((used)) int64_t g_used = 7;          // unreferenced
/// __attribute__((weak)) int64_t g_weak = 8;
/// __attribute__((section("__TEXT,__const"))) const int64_t g_ro_sec = 9;
/// ```
fn attributes_module() -> Module {
    let mut module = Module::new("data_attributes");
    let mut sec = i64_global("g_sec", 5);
    sec.section = Some("__DATA,__cgdata".to_string());
    let mut hidden = i64_global("g_hidden", 6);
    hidden.visibility = Visibility::Hidden;
    let mut used = i64_global("g_used", 7);
    used.retained = true;
    let mut weak = i64_global("g_weak", 8);
    weak.linkage = Linkage::Weak;
    let mut ro_sec = data_global("g_ro_sec", Ty::I64, false, Some(Constant::Int(9)));
    ro_sec.section = Some("__TEXT,__const".to_string());
    module.globals.extend([sec, hidden, used, weak, ro_sec]);
    for (name, index) in [
        ("read_sec", 0),
        ("read_hidden", 1),
        ("read_weak", 3),
        ("read_ro_sec", 4),
    ] {
        add_function(
            &mut module,
            name,
            vec![],
            vec![Ty::I64],
            vec![global_addr(index, 0), load(Ty::I64, 0, 1), ret(1)],
        );
    }
    add_function(
        &mut module,
        "weak_addr",
        vec![],
        vec![Ty::Ptr],
        vec![global_addr(3, 0), ret(0)],
    );
    module
}

// =============================================================================
// Compilation and linking
// =============================================================================

fn macho_compiler(opt_level: OptLevel) -> Compiler {
    let spec = TargetSpec::parse(DARWIN).expect("aarch64-apple-darwin parses");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
}

fn compile_macho(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    macho_compiler(opt_level)
        .compile(module)
        .unwrap_or_else(|error| panic!("{} at {opt_level:?}: {error}", module.name))
        .object_code
}

fn checked(command: &mut Command, what: &str) -> TimedCommandOutput {
    let output = command_output_with_timeout(command, Duration::from_secs(120))
        .unwrap_or_else(|error| panic!("{what}: {error}"));
    assert!(!output.timed_out, "{what} timed out");
    assert!(
        output.output.status.success(),
        "{what} failed:\n{}\n{}",
        String::from_utf8_lossy(&output.output.stdout),
        String::from_utf8_lossy(&output.output.stderr)
    );
    output
}

fn stdout_of(command: &mut Command, what: &str) -> String {
    String::from_utf8_lossy(&checked(command, what).output.stdout).into_owned()
}

fn make_executable(path: &Path) {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
}

fn libsystem(extra: &[&str]) -> DylibConfig {
    let mut config = DylibConfig::with_libsystem();
    config.dylibs[0]
        .symbols
        .extend(extra.iter().map(|symbol| symbol.to_string()));
    config
}

struct Twins {
    standalone: TimedCommandOutput,
    ld64: TimedCommandOutput,
    ld64_path: PathBuf,
    object_path: PathBuf,
    _directory: tempfile::TempDir,
}

/// Compile `driver` with clang, link it with the CG object standalone and
/// with ld64 (`extra_ld64_args`), run both under the codegen timeout.
fn link_twins(
    label: &str,
    driver: &str,
    object: &[u8],
    driver_imports: &[&str],
    extra_ld64_args: &[&str],
) -> Twins {
    let directory = tempfile::Builder::new()
        .prefix(&format!("trust-cg-globals-darwin-{label}-"))
        .tempdir()
        .unwrap();
    let source = directory.path().join("driver.c");
    let driver_object = directory.path().join("driver.o");
    let object_path = directory.path().join("cg.o");
    std::fs::write(&source, driver).unwrap();
    std::fs::write(&object_path, object).unwrap();
    checked(
        Command::new("/usr/bin/clang")
            .args(["-O1", "-fno-stack-protector", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&driver_object),
        "clang -c driver",
    );
    let parsed = vec![
        MachOParser::parse(&std::fs::read(&driver_object).unwrap()).unwrap(),
        MachOParser::parse(object).unwrap(),
    ];
    let standalone_path = directory.path().join("standalone");
    let image = link_with_dylibs(&parsed, &libsystem(driver_imports))
        .unwrap_or_else(|error| panic!("{label}: standalone link failed: {error}"));
    std::fs::write(&standalone_path, image).unwrap();
    make_executable(&standalone_path);
    let ld64_path = directory.path().join("ld64");
    checked(
        Command::new("/usr/bin/clang")
            .arg(&driver_object)
            .arg(&object_path)
            .args(extra_ld64_args)
            .arg("-o")
            .arg(&ld64_path),
        "ld64 link",
    );
    for path in [&standalone_path, &ld64_path] {
        let output = checked(
            Command::new("/usr/bin/dyld_info")
                .arg("-validate_only")
                .arg(path),
            "dyld_info -validate_only",
        );
        let report = String::from_utf8_lossy(&output.output.stdout).to_string()
            + &String::from_utf8_lossy(&output.output.stderr);
        let report = report.to_ascii_lowercase();
        assert!(
            !report.contains("malformed") && !report.contains("error"),
            "dyld_info rejected {}: {report}",
            path.display()
        );
    }
    let run = |path: &Path| {
        let output = run_executable_with_timeout(path, codegen_run_timeout()).unwrap();
        assert!(!output.timed_out, "{label}: {} timed out", path.display());
        output
    };
    Twins {
        standalone: run(&standalone_path),
        ld64: run(&ld64_path),
        ld64_path,
        object_path,
        _directory: directory,
    }
}

fn assert_twins_agree(label: &str, twins: &Twins, expected_stdout: &str) {
    for (name, output) in [("standalone", &twins.standalone), ("ld64", &twins.ld64)] {
        assert_eq!(
            output.output.status.code(),
            Some(0),
            "{label} {name}: stdout={} stderr={}",
            String::from_utf8_lossy(&output.output.stdout),
            String::from_utf8_lossy(&output.output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.output.stdout),
            expected_stdout,
            "{label} {name}"
        );
    }
}

// =============================================================================
// (1) Mach-O TLS templates with relocations
// =============================================================================

const TLS_DRIVER: &str = r#"
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

extern int64_t g_target;
extern const int64_t g_arr[4];
extern void *read_tp(void);
extern void  set_tp(void *);
extern void *read_tf(void);
extern void *read_tq(void);
extern int64_t tls_fn(void);

static int worker_ok;

static void *worker(void *arg) {
    (void)arg;
    // A fresh thread starts from the relocated template: the data pointer,
    // the function pointer and the interior pointer are all fixed up.
    int ok = read_tp() == &g_target && *(int64_t *)read_tp() == 78;
    ok = ok && ((int64_t (*)(void))read_tf)() != 0
            && ((int64_t (*)(void))read_tf())() == 4242;
    ok = ok && read_tq() == (const void *)&g_arr[2] && *(const int64_t *)read_tq() == 30;
    // Re-pointing this thread's copy never reaches the main thread.
    int64_t local = 5;
    set_tp(&local);
    ok = ok && read_tp() == &local && *(int64_t *)read_tp() == 5;
    worker_ok = ok;
    return NULL;
}

int main(void) {
    if (read_tp() != &g_target) { printf("tp\n"); return 1; }
    if (*(int64_t *)read_tp() != 77) { printf("deref\n"); return 2; }
    // A write through the per-thread pointer lands in the shared global.
    *(int64_t *)read_tp() = 78;
    if (g_target != 78) { printf("shared write\n"); return 3; }
    if (((int64_t (*)(void))read_tf())() != 4242) { printf("tf\n"); return 4; }
    if (read_tq() != (const void *)&g_arr[2] || *(const int64_t *)read_tq() != 30) {
        printf("tq\n"); return 5;
    }
    int64_t other = 9;
    set_tp(&other);
    pthread_t t;
    pthread_create(&t, NULL, worker, NULL);
    pthread_join(t, NULL);
    if (!worker_ok) { printf("worker\n"); return 6; }
    if (read_tp() != &other) { printf("isolation\n"); return 7; }
    printf("tls templates relocated: tp=%d tf=%lld tq=%lld target=%lld\n",
           read_tp() == &other, (long long)((int64_t (*)(void))read_tf())(),
           (long long)*(const int64_t *)read_tq(), (long long)g_target);
    return 0;
}
"#;

const TLS_DRIVER_IMPORTS: &[&str] = &["_pthread_create", "_pthread_join", "_printf"];

/// The object carries one `ARM64_RELOC_UNSIGNED` per template slot in
/// `__DATA,__thread_data`, with the addend baked into the slot.
#[test]
fn tls_template_object_relocates_thread_data_slots_at_o0_through_o3() {
    let module = tls_template_module();
    for opt_level in OPT_LEVELS {
        let object = compile_macho(&module, opt_level);
        let parsed = MachOParser::parse(&object).unwrap();
        let thread_data = parsed
            .sections
            .iter()
            .find(|section| section.name == "__thread_data" && section.segment == "__DATA")
            .unwrap_or_else(|| panic!("{opt_level:?}: no __thread_data section"));
        let mut slots: Vec<(u32, String, i64)> = thread_data
            .relocations
            .iter()
            .map(|reloc| {
                assert_eq!(reloc.kind, AArch64RelocKind::Unsigned, "{opt_level:?}");
                assert!(reloc.is_extern && !reloc.pc_relative && reloc.length == 3);
                let offset = reloc.offset as usize;
                let inline =
                    i64::from_le_bytes(thread_data.data[offset..offset + 8].try_into().unwrap());
                (
                    reloc.offset,
                    parsed.symbols[reloc.symbol_index as usize]
                        .name
                        .as_str()
                        .to_owned(),
                    inline,
                )
            })
            .collect();
        slots.sort();
        assert_eq!(
            slots,
            vec![
                (0, "_g_target".to_string(), 0),
                (8, "_tls_fn".to_string(), 0),
                (16, "_g_arr".to_string(), 16),
            ],
            "{opt_level:?}: every template slot relocates with its addend"
        );
        let thread_vars = parsed
            .sections
            .iter()
            .find(|section| section.name == "__thread_vars")
            .unwrap();
        assert_eq!(
            thread_vars.relocations.len(),
            6,
            "{opt_level:?}: three descriptors keep their two pointers each"
        );
    }
}

/// ld64 and the standalone linker both rebase the template; every thread
/// starts from the fixed-up pointers and the C driver's view agrees.
#[test]
fn tls_template_symbol_addresses_match_c_oracle_with_ld64_and_standalone() {
    let module = tls_template_module();
    for opt_level in OPT_LEVELS {
        let label = format!("tls-template-{opt_level:?}");
        let twins = link_twins(
            &label,
            TLS_DRIVER,
            &compile_macho(&module, opt_level),
            TLS_DRIVER_IMPORTS,
            &[],
        );
        assert_twins_agree(
            &label,
            &twins,
            "tls templates relocated: tp=1 tf=4242 tq=30 target=78\n",
        );
        // The linked template is rebased: dyld_info lists fixups inside
        // __thread_data for the ld64 image.
        let fixups = stdout_of(
            Command::new("/usr/bin/dyld_info")
                .arg("-fixups")
                .arg(&twins.ld64_path),
            "dyld_info -fixups",
        );
        assert!(
            fixups.contains("__thread_data"),
            "{label}: ld64 image carries no __thread_data fixup:\n{fixups}"
        );
    }
}

// =============================================================================
// (2) JIT data image
// =============================================================================

static HOST_VALUE: AtomicI64 = AtomicI64::new(4321);

fn jit_externs() -> HashMap<String, *const u8> {
    HashMap::from([(
        "host_value".to_string(),
        &HOST_VALUE as *const AtomicI64 as *const u8,
    )])
}

/// A JIT body reads and writes a module global, addresses a string constant
/// and a function-pointer table placed in the JIT data image, and loads a
/// data import through a GOT slot; the buffer records the image identity.
#[test]
fn jit_reads_and_writes_module_globals_and_string_constant_at_o0_through_o3() {
    let module = jit_globals_module();
    let externs = jit_externs();
    for opt_level in OPT_LEVELS {
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
        // The image holds the definitions; the import and the functions are
        // not data symbols.
        let counter = buffer
            .data_symbol_ptr("g_counter")
            .expect("g_counter placed") as *mut i64;
        let text = buffer.data_symbol_ptr("g_str").expect("g_str placed");
        assert!(buffer.data_symbol_ptr("host_value").is_none());
        assert!(buffer.data_symbol_ptr("bump").is_none());
        let (data_base, data_len) = buffer.data_image_range().expect("data mapping");
        assert!((counter as u64) >= data_base && (counter as u64) < data_base + data_len as u64);

        // Read-modify-write through the JIT, then observed from the host.
        assert_eq!((*bump.as_ref())(5), 105, "{opt_level:?}");
        assert_eq!(unsafe { counter.read() }, 105, "{opt_level:?}");
        unsafe { counter.write(200) };
        assert_eq!(
            (*bump.as_ref())(1),
            201,
            "{opt_level:?}: host write seen by the JIT"
        );
        // The string constant is real module data, not a leaked heap image.
        assert_eq!((*str_ptr.as_ref())(), text, "{opt_level:?}");
        let bytes = unsafe { std::slice::from_raw_parts(text, 6) };
        assert_eq!(bytes, b"hello\0", "{opt_level:?}");
        assert_eq!((*str_byte1.as_ref())(), i64::from(b'e'), "{opt_level:?}");
        // The table slot was relocated to the JIT function.
        assert_eq!(
            (*tbl_read.as_ref())(),
            buffer
                .get_fn_ptr_bound("bump")
                .expect("bump address")
                .as_ptr(),
            "{opt_level:?}"
        );
        // The import is loaded through a GOT slot bound to the host static.
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

/// The image identity binds the initial bytes and the relocation list: two
/// modules that differ only in a global's initializer publish different
/// manifests, and the same module publishes the same manifest twice.
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

// =============================================================================
// (3) SymbolAddr with a non-zero addend in a body
// =============================================================================

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

#[test]
fn symbol_addr_with_addend_in_body_matches_c_oracle_at_o0_through_o3() {
    let module = addend_module();
    for opt_level in OPT_LEVELS {
        let label = format!("addend-{opt_level:?}");
        let twins = link_twins(
            &label,
            ADDEND_DRIVER,
            &compile_macho(&module, opt_level),
            &["_printf"],
            &[],
        );
        assert_twins_agree(&label, &twins, "interior address: third=30 same=1\n");
    }
}

// =============================================================================
// (4) Sections, visibility, retention and weak definitions on data globals
// =============================================================================

const ATTRIBUTES_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern int64_t g_sec;
extern int64_t g_hidden;
extern int64_t g_used;
extern const int64_t g_ro_sec;
__attribute__((weak)) int64_t g_weak = 99;
extern int64_t read_sec(void);
extern int64_t read_hidden(void);
extern int64_t read_weak(void);
extern int64_t read_ro_sec(void);
extern void *weak_addr(void);
int main(void) {
    if (read_sec() != 5 || g_sec != 5) { printf("sec\n"); return 1; }
    g_sec = 55;
    if (read_sec() != 55) { printf("sec write\n"); return 2; }
    if (read_hidden() != 6 || g_hidden != 6) { printf("hidden\n"); return 3; }
    if (g_used != 7) { printf("used\n"); return 4; }
    if (read_ro_sec() != 9 || g_ro_sec != 9) { printf("ro\n"); return 5; }
    // Both weak definitions coalesce to one symbol: same value, same address.
    if (read_weak() != g_weak) { printf("weak value\n"); return 6; }
    if (weak_addr() != &g_weak) { printf("weak address\n"); return 7; }
    printf("attributes: sec=%lld hidden=%lld used=%lld ro=%lld weak_same=%d\n",
           (long long)read_sec(), (long long)read_hidden(), (long long)g_used,
           (long long)read_ro_sec(), weak_addr() == &g_weak);
    return 0;
}
"#;

#[test]
fn data_global_sections_visibility_retained_and_weak_match_c_oracle_at_o0_through_o3() {
    let module = attributes_module();
    for opt_level in OPT_LEVELS {
        let label = format!("attributes-{opt_level:?}");
        let object = compile_macho(&module, opt_level);
        let twins = link_twins(
            &label,
            ATTRIBUTES_DRIVER,
            &object,
            &["_printf"],
            &["-Wl,-dead_strip"],
        );
        assert_twins_agree(
            &label,
            &twins,
            "attributes: sec=55 hidden=6 used=7 ro=9 weak_same=1\n",
        );
        // Object level: the attributes reach the nlist and section table.
        let nm = stdout_of(
            Command::new("/usr/bin/nm")
                .arg("-m")
                .arg(&twins.object_path),
            "nm -m",
        );
        let line = |symbol: &str| {
            nm.lines()
                .find(|line| line.ends_with(&format!(" {symbol}")))
                .unwrap_or_else(|| panic!("{label}: `{symbol}` missing from nm -m:\n{nm}"))
                .to_string()
        };
        assert!(
            line("_g_hidden").contains("private external"),
            "{label}: {nm}"
        );
        assert!(line("_g_used").contains("[no dead strip]"), "{label}: {nm}");
        assert!(line("_g_weak").contains("weak"), "{label}: {nm}");
        assert!(
            line("_g_sec").contains("(__DATA,__cgdata)"),
            "{label}: {nm}"
        );
        assert!(
            line("_g_ro_sec").contains("(__TEXT,__const)"),
            "{label}: {nm}"
        );
        let sections = stdout_of(
            Command::new("/usr/bin/otool")
                .arg("-l")
                .arg(&twins.object_path),
            "otool -l",
        );
        assert!(
            sections.contains("sectname __cgdata"),
            "{label}: {sections}"
        );
        // ld64 -dead_strip keeps the retained, unreferenced definition.
        let linked = stdout_of(Command::new("/usr/bin/nm").arg(&twins.ld64_path), "nm");
        let defined: BTreeSet<&str> = linked
            .lines()
            .filter_map(|line| line.split_whitespace().last())
            .collect();
        assert!(
            defined.contains("_g_used"),
            "{label}: retained global stripped:\n{linked}"
        );
    }
}

// =============================================================================
// (5) Named refusals that stay closed
// =============================================================================

fn lir_global_ref_function() -> LirFunction {
    let mut func = LirFunction::new(
        "read_global",
        Signature {
            params: vec![],
            returns: vec![LirType::I64],
        },
    );
    func.entry_block = LirBlock(0);
    func.block_order = vec![LirBlock(0)];
    func.blocks.insert(
        LirBlock(0),
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::GlobalRef {
                        name: "jit_word".into(),
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: LirType::I64,
                        align: Some(8),
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(1)],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn jit_word_global() -> ObjectGlobal {
    ObjectGlobal {
        name: "jit_word".into(),
        data: 11i64.to_le_bytes().to_vec(),
        mutable: true,
        is_external: true,
        symbol_refs: vec![],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 8,
        visibility: Visibility::Default,
        retained: false,
        section: None,
        comdat: false,
    }
}

#[test]
fn named_refusals_stay_closed() {
    // ExternalWeak data on Mach-O: ld64 on this host refuses an undefined
    // weak reference, and the Mach-O emitter does not spell N_WEAK_REF.
    let mut module = Module::new("external_weak");
    let mut weak = data_global("ext_weak", Ty::I64, true, None);
    weak.linkage = Linkage::ExternalWeak;
    module.globals.push(weak);
    add_function(
        &mut module,
        "read_ext_weak",
        vec![],
        vec![Ty::I64],
        vec![global_addr(0, 0), load(Ty::I64, 0, 1), ret(1)],
    );
    let error = macho_compiler(OptLevel::O0)
        .compile(&module)
        .expect_err("ExternalWeak data stays refused on Mach-O")
        .to_string();
    assert!(
        error.contains("ext_weak") && error.contains("refusing"),
        "unexpected diagnostic: {error}"
    );

    // A thread-local in an explicit section: the TLV descriptor sections
    // are its only placement.
    let mut module = tls_template_module();
    module.globals[2].section = Some("__DATA,__cgtls".to_string());
    let error = macho_compiler(OptLevel::O0)
        .compile(&module)
        .expect_err("a thread-local in an explicit section is refused")
        .to_string();
    assert!(
        error.contains("tp") && error.contains("thread-local") && error.contains("TCG-SECTION"),
        "unexpected diagnostic: {error}"
    );

    // The ELF dialect relocates the same templates (object emission is
    // host-independent): one R_AARCH64_ABS64 per slot in `.rela.tdata`.
    // Its native Linux execution lives in e2e_aarch64_globals_linux.
    let elf = || {
        Compiler::new_for_target_spec(
            CompilerConfig::default(),
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
    };
    let object = elf()
        .compile(&tls_template_module())
        .expect("ELF relocates a TLS initial-value template")
        .object_code;
    let records = read_object_records(&object).expect("reparse ELF");
    let mut slots: Vec<(String, u32, String, i64)> = records
        .relocations
        .iter()
        .map(|relocation| {
            (
                records.sections[relocation.target_section].name.clone(),
                relocation.record.reloc_type,
                records.symbols[relocation.record.symbol_index as usize]
                    .name
                    .clone(),
                relocation.record.r_addend,
            )
        })
        .filter(|(section, ..)| section == ".tdata")
        .collect();
    slots.sort();
    assert_eq!(
        slots,
        vec![
            (".tdata".to_string(), 257, "g_arr".to_string(), 16),
            (".tdata".to_string(), 257, "g_target".to_string(), 0),
            (".tdata".to_string(), 257, "tls_fn".to_string(), 0),
        ],
        "ELF template slots are R_AARCH64_ABS64 rows in .rela.tdata"
    );

    // A pointer slot whose TARGET is itself a thread-local has no link-time
    // address on either dialect and is refused by name.
    let mut module = tls_template_module();
    module.globals[2].initializer = Some(Constant::SymbolAddr {
        symbol: "tf".to_string(),
        addend: 0,
    });
    for error in [
        macho_compiler(OptLevel::O0).compile(&module).err(),
        elf().compile(&module).err(),
    ] {
        let error = error
            .expect("a template slot naming a thread-local is refused")
            .to_string();
        assert!(
            error.contains("[TCG-TLS-SLOT-TARGET]")
                && error.contains("`tp`")
                && error.contains("thread-local `tf`"),
            "unexpected diagnostic: {error}"
        );
    }

    // A JIT body naming a thread-local: the data image places no TLV.
    let error = Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&tls_template_module(), &HashMap::new())
        .expect_err("a JIT body reading a thread-local is refused");
    assert!(
        matches!(
            error,
            CompileError::Jit(JitError::JitDataGlobalUnplaceable { ref global, ref reason, .. })
                if module_names_tls(global) && reason.contains("thread-local")
        ),
        "unexpected refusal: {error}"
    );

    // A verifying raw JIT request refuses the first data site by name: no
    // obligation models the data image.
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: DARWIN.into(),
        opt_level: OptLevel::O0,
        ..PipelineConfig::default()
    });
    let prepared = pipeline
        .prepare_function(&lir_global_ref_function())
        .expect("prepare GlobalRef function");
    let verifying = JitCompiler::new(JitConfig {
        verify: true,
        ..JitConfig::default()
    });
    let error = verifying
        .compile_raw_with_globals(
            std::slice::from_ref(&prepared),
            &[jit_word_global()],
            &HashMap::new(),
        )
        .expect_err("verifying JIT refuses data relocations");
    assert!(
        matches!(
            error,
            JitError::JitDataRelocationProofUnavailable { ref symbol, .. } if symbol == "jit_word"
        ),
        "unexpected refusal: {error}"
    );
    // The unchecked raw path publishes the same function against the image.
    let unchecked = JitCompiler::new(JitConfig::default());
    let buffer = unchecked
        .compile_raw_with_globals(
            std::slice::from_ref(&prepared),
            &[jit_word_global()],
            &HashMap::new(),
        )
        .expect("unchecked raw JIT with a data image");
    let read = unsafe {
        buffer
            .get_fn_bound::<extern "C" fn() -> i64>("read_global")
            .expect("read_global")
    };
    assert_eq!((*read.as_ref())(), 11);
    // A raw module whose body names a global the caller did not supply is
    // still an unresolved symbol, never a silent process binding.
    let error = unchecked
        .compile_raw(std::slice::from_ref(&prepared), &HashMap::new())
        .expect_err("a GlobalRef without its global stays unresolved");
    assert!(
        matches!(error, JitError::UnresolvedSymbol(ref name) if name == "jit_word"),
        "unexpected refusal: {error}"
    );
}

fn module_names_tls(global: &str) -> bool {
    matches!(global, "tp" | "tf" | "tq")
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
