#![allow(dead_code)]
// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared harness of the construct-sweep native controls (ledger L05-P2,
//! Darwin row D05): `e2e_aarch64_construct_sweep_{types,insts,casts,tables}`.
//!
//! A sweep module is compiled for aarch64-apple-darwin at O0-O3 through the
//! public `Compiler`, linked by the host `cc` against a generated C driver and
//! executed. The driver calls each exported function with fixed arguments,
//! prints the result's bit pattern as `key=<32 hex digits>`, and checks it
//! against the C spelling of the construct where it has one (`PASS n`). The
//! test replays every call it has an interpreter oracle for through the pinned
//! trust-ir reference interpreter and requires the native pattern to equal
//! the interpreter's. Trap rows run the driver once per mode and require the
//! process to die by a trap signal where the interpreter refuses the same run.
//!
//! Execution evidence on this host only; not a proof of any lowering.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::interpret::{
    InterpretErrorCode, InterpretInt, InterpretValue, InterpretValueKind, Interpreter,
};
use trust_ir::{
    Block, BlockId, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructPassingPolicy, TargetInfo, Ty, ValueId,
};

// Share the native helper and its process module with consumers that also
// need direct native execution, so each support file is loaded only once.
#[path = "aarch64_native.rs"]
pub mod native;
use native::process;

pub const TRIPLE: &str = "aarch64-apple-darwin";
pub const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// SIGILL and SIGTRAP: the two signals an AArch64 trap instruction raises.
const TRAP_SIGNALS: [i32; 2] = [4, 5];

/// An empty module stamped for the Darwin AArch64 C ABI.
pub fn sweep_module(name: &str) -> Module {
    let mut module = Module::new(name);
    module.target_info = Some(TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module
}

/// A function body under construction: every `Inst::` node is spelled by
/// the caller, so the sweep files name each construct they execute.
pub struct Body {
    next: u32,
    blocks: Vec<Block>,
    current: usize,
}

impl Default for Body {
    fn default() -> Self {
        Self::new()
    }
}

impl Body {
    pub fn new() -> Self {
        Body {
            next: 0,
            blocks: vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![],
            }],
            current: 0,
        }
    }

    fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        value
    }

    /// A parameter of the entry block (a function parameter).
    pub fn param(&mut self, ty: Ty) -> ValueId {
        let value = self.fresh();
        self.blocks[0].params.push((value, ty));
        value
    }

    /// Append `inst` with one result.
    pub fn emit(&mut self, inst: Inst) -> ValueId {
        let value = self.fresh();
        self.blocks[self.current]
            .body
            .push(InstrNode::new(inst).with_result(value));
        value
    }

    /// Append `inst` with `count` results.
    pub fn emit_n(&mut self, inst: Inst, count: usize) -> Vec<ValueId> {
        let results: Vec<ValueId> = (0..count).map(|_| self.fresh()).collect();
        self.blocks[self.current]
            .body
            .push(InstrNode::new(inst).with_results(results.clone()));
        results
    }

    /// Append `inst` with no result.
    pub fn effect(&mut self, inst: Inst) {
        self.blocks[self.current].body.push(InstrNode::new(inst));
    }

    /// A new block with parameters of `params`; the cursor stays put.
    pub fn block(&mut self, params: &[Ty]) -> (BlockId, Vec<ValueId>) {
        let id = BlockId::new(self.blocks.len() as u32);
        let values: Vec<ValueId> = params.iter().map(|_| self.fresh()).collect();
        self.blocks.push(Block {
            id,
            params: values.iter().copied().zip(params.iter().cloned()).collect(),
            body: vec![],
        });
        (id, values)
    }

    /// Move the cursor to `block`.
    pub fn switch_to(&mut self, block: BlockId) {
        self.current = self
            .blocks
            .iter()
            .position(|candidate| candidate.id == block)
            .unwrap_or_else(|| panic!("no block {block:?}"));
    }
}

/// Add a bodied function `name` to `module`.
pub fn define(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Body,
) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    function.blocks = body.blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// A scalar argument: its trust-ir type and bit pattern.
#[derive(Clone, Debug)]
pub struct Arg(pub Ty, pub u128);

/// Who else computes a native call's value.
#[derive(Clone, Debug)]
pub enum Oracle {
    /// The reference interpreter runs the same function on the same arguments.
    Same,
    /// The reference interpreter runs another function (a twin spelling the
    /// same semantics in constructs it executes) on these arguments.
    Twin(&'static str, Vec<Arg>),
}

/// One call the driver makes natively.
#[derive(Clone, Debug)]
pub struct Call {
    pub key: String,
    pub func: &'static str,
    pub args: Vec<Arg>,
    pub ret: Ty,
    /// C expression over `a0`, `a1`, ... (the typed arguments) whose value,
    /// at the result's C type, is the construct's C meaning.
    pub c_model: Option<String>,
    pub oracle: Option<Oracle>,
}

impl Call {
    pub fn new(key: impl Into<String>, func: &'static str, args: Vec<Arg>, ret: Ty) -> Self {
        Call {
            key: key.into(),
            func,
            args,
            ret,
            c_model: None,
            oracle: Some(Oracle::Same),
        }
    }

    pub fn c(mut self, model: impl Into<String>) -> Self {
        self.c_model = Some(model.into());
        self
    }

    pub fn twin(mut self, func: &'static str, args: Vec<Arg>) -> Self {
        self.oracle = Some(Oracle::Twin(func, args));
        self
    }

    pub fn c_only(mut self) -> Self {
        self.oracle = None;
        self
    }
}

/// A driver mode that must die by a trap where the interpreter refuses.
#[derive(Clone, Debug)]
pub struct Trap {
    pub mode: &'static str,
    pub func: &'static str,
    pub args: Vec<Arg>,
    /// The interpreter's refusal of the same run.
    pub refusal: InterpretErrorCode,
}

/// The C spelling of a scalar trust-ir type at an ABI boundary.
pub fn c_type(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "int8_t",
        Ty::I16 => "int16_t",
        Ty::I32 => "int32_t",
        Ty::I64 => "int64_t",
        Ty::I128 => "__int128",
        Ty::U8 => "uint8_t",
        Ty::U16 => "uint16_t",
        Ty::U32 | Ty::Char => "uint32_t",
        Ty::U64 => "uint64_t",
        Ty::U128 => "unsigned __int128",
        Ty::Isize => "intptr_t",
        Ty::Usize => "uintptr_t",
        Ty::Bool => "bool",
        Ty::F16 => "_Float16",
        Ty::F32 => "float",
        Ty::F64 => "double",
        Ty::Unit => "void",
        Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) => "void *",
        other => panic!("no C spelling for {other:?} at the driver boundary"),
    }
}

/// `(bits, signed)` of an integer-like scalar.
fn int_shape(ty: &Ty) -> Option<(u32, bool)> {
    Some(match ty {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 | Ty::Isize => (64, true),
        Ty::I128 => (128, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 | Ty::Char => (32, false),
        Ty::U64 | Ty::Usize => (64, false),
        Ty::U128 => (128, false),
        _ => return None,
    })
}

fn c_u128_literal(bits: u128) -> String {
    format!(
        "(((u128)0x{:016x}ULL << 64) | (u128)0x{:016x}ULL)",
        (bits >> 64) as u64,
        bits as u64
    )
}

/// The C expression of an argument of `ty` with bit pattern `bits`.
fn c_arg(ty: &Ty, bits: u128) -> String {
    match ty {
        Ty::F16 => format!("f16_of(0x{:04x})", bits as u16),
        Ty::F32 => format!("f32_of(0x{:08x}u)", bits as u32),
        Ty::F64 => format!("f64_of(0x{:016x}ULL)", bits as u64),
        Ty::Bool => format!("(bool){}", bits & 1),
        Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) => {
            format!("(void *)(uintptr_t)0x{:016x}ULL", bits as u64)
        }
        other => format!("({}){}", c_type(other), c_u128_literal(bits)),
    }
}

/// The C expression of the bit pattern (a `u128`) of `value` of type `ty`.
fn c_bits(ty: &Ty, value: &str) -> String {
    match ty {
        Ty::F16 => format!("(u128)bits_f16({value})"),
        Ty::F32 => format!("(u128)bits_f32({value})"),
        Ty::F64 => format!("(u128)bits_f64({value})"),
        Ty::Bool => format!("(u128)({value} ? 1 : 0)"),
        Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_) => {
            format!("(u128)(uintptr_t)({value})")
        }
        Ty::I128 | Ty::U128 => format!("(u128)({value})"),
        other => {
            let (bits, _) = int_shape(other)
                .unwrap_or_else(|| panic!("no bit pattern for {other:?} at the driver boundary"));
            format!("(u128)(uint{bits}_t)({value})")
        }
    }
}

const DRIVER_PRELUDE: &str = r#"#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;
static unsigned checks, fails;

#define SWEEP_UNUSED __attribute__((unused))
SWEEP_UNUSED static _Float16 f16_of(uint16_t b) { _Float16 v; memcpy(&v, &b, 2); return v; }
SWEEP_UNUSED static float f32_of(uint32_t b) { float v; memcpy(&v, &b, 4); return v; }
SWEEP_UNUSED static double f64_of(uint64_t b) { double v; memcpy(&v, &b, 8); return v; }
SWEEP_UNUSED static uint16_t bits_f16(_Float16 v) { uint16_t b; memcpy(&b, &v, 2); return b; }
SWEEP_UNUSED static uint32_t bits_f32(float v) { uint32_t b; memcpy(&b, &v, 4); return b; }
SWEEP_UNUSED static uint64_t bits_f64(double v) { uint64_t b; memcpy(&b, &v, 8); return b; }

/* Print one native value; compare it with its C model when there is one. */
static void report(const char *key, u128 got, int modelled, u128 want) {
    printf("%s=%016llx%016llx\n", key, (unsigned long long)(got >> 64),
           (unsigned long long)got);
    if (!modelled) return;
    checks++;
    if (got != want) {
        fails++;
        printf("MISMATCH %s c-model=%016llx%016llx\n", key,
               (unsigned long long)(want >> 64), (unsigned long long)want);
    }
}
"#;

/// The generated C driver: prototypes for every called function, the calls,
/// their C models, `extra` (a C statement block that may call `report`), and
/// one `argv[1]` mode per trap.
pub fn driver(
    module: &Module,
    calls: &[Call],
    traps: &[Trap],
    prelude: &str,
    extra: &str,
) -> String {
    let mut out = String::from(DRIVER_PRELUDE);
    let mut declared = BTreeMap::new();
    let mut declare = |name: &str| {
        if declared.contains_key(name) {
            return;
        }
        let function = module
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("the sweep module defines no `{name}`"));
        let signature = &module.func_types[function.ty.as_usize()];
        let ret = match signature.returns.as_slice() {
            [] => "void",
            [Ty::Never] => "void",
            [ty] => c_type(&representation(module, ty)),
            more => panic!("`{name}` returns {} values", more.len()),
        };
        let params: Vec<&str> = signature
            .params
            .iter()
            .map(|ty| c_type(&representation(module, ty)))
            .collect();
        let params = if params.is_empty() {
            "void".to_string()
        } else {
            params.join(", ")
        };
        declared.insert(
            name.to_string(),
            format!("extern {ret} {name}({params});\n"),
        );
    };
    for call in calls {
        declare(call.func);
    }
    for trap in traps {
        declare(trap.func);
    }
    for prototype in declared.values() {
        out.push_str(prototype);
    }
    out.push_str(prelude);
    out.push_str("\nint main(int argc, char **argv) {\n");
    out.push_str("    if (argc > 1) {\n");
    for trap in traps {
        let args: Vec<String> = trap
            .args
            .iter()
            .map(|Arg(ty, bits)| c_arg(&representation(module, ty), *bits))
            .collect();
        let _ = writeln!(
            out,
            "        if (!strcmp(argv[1], \"{}\")) {{ {}({}); printf(\"RETURNED {}\\n\"); return 98; }}",
            trap.mode,
            trap.func,
            args.join(", "),
            trap.mode
        );
    }
    out.push_str("        printf(\"UNKNOWN MODE %s\\n\", argv[1]);\n        return 99;\n    }\n");
    for call in calls {
        out.push_str("    {\n");
        for (index, Arg(ty, bits)) in call.args.iter().enumerate() {
            let ty = representation(module, ty);
            let _ = writeln!(
                out,
                "        {} a{index} = {};",
                c_type(&ty),
                c_arg(&ty, *bits)
            );
        }
        let ret = representation(module, &call.ret);
        let args: Vec<String> = (0..call.args.len())
            .map(|index| format!("a{index}"))
            .collect();
        let _ = writeln!(
            out,
            "        {} r = {}({});",
            c_type(&ret),
            call.func,
            args.join(", ")
        );
        match &call.c_model {
            Some(model) => {
                let _ = writeln!(out, "        {} w = ({model});", c_type(&ret));
                let _ = writeln!(
                    out,
                    "        report(\"{}\", {}, 1, {});",
                    call.key,
                    c_bits(&ret, "r"),
                    c_bits(&ret, "w")
                );
            }
            None => {
                let _ = writeln!(
                    out,
                    "        report(\"{}\", {}, 0, 0);",
                    call.key,
                    c_bits(&ret, "r")
                );
            }
        }
        out.push_str("    }\n");
    }
    out.push_str(extra);
    out.push_str(
        "    if (fails) { printf(\"FAIL %u of %u c-model checks\\n\", fails, checks); return 1; }\n",
    );
    out.push_str("    printf(\"PASS %u c-model checks\\n\", checks);\n    return 0;\n}\n");
    out
}

/// A refinement's representation (`Ty::Refine` erases to its base); every
/// other type is its own.
pub fn representation(module: &Module, ty: &Ty) -> Ty {
    module
        .representation_ty(ty)
        .cloned()
        .unwrap_or_else(|| panic!("{ty:?} has no representation in the sweep module"))
}

/// The interpreter value of an argument, typed at the argument's own type
/// (a refined argument carries its refinement; its bits are its base's).
pub fn interpret_arg(module: &Module, Arg(ty, bits): &Arg) -> InterpretValue {
    let kind = match &representation(module, ty) {
        Ty::Bool => InterpretValueKind::Bool(bits & 1 == 1),
        Ty::F16 | Ty::F32 | Ty::F64 => InterpretValueKind::FloatBits(*bits as u64),
        Ty::Ptr if *bits == 0 => InterpretValueKind::NullPtr,
        Ty::Ptr => InterpretValueKind::DanglingPtr(*bits as u64),
        other => {
            let (width, signed) = int_shape(other)
                .unwrap_or_else(|| panic!("no interpreter argument of type {other:?}"));
            InterpretValueKind::Int(
                InterpretInt::from_raw(width, signed, *bits)
                    .unwrap_or_else(|| panic!("no {width}-bit integer")),
            )
        }
    };
    InterpretValue {
        ty: ty.clone(),
        kind,
    }
}

/// The bit pattern of a scalar interpreter result.
pub fn interpret_bits(value: &InterpretValue) -> u128 {
    match &value.kind {
        InterpretValueKind::Int(int) => int.as_unsigned(),
        InterpretValueKind::Bool(flag) => u128::from(*flag),
        InterpretValueKind::FloatBits(bits) => u128::from(*bits),
        InterpretValueKind::NullPtr => 0,
        InterpretValueKind::DanglingPtr(address) => u128::from(*address),
        other => panic!("no scalar bit pattern for {other:?}"),
    }
}

/// Run `name(args)` under the reference interpreter, in-format.
pub fn interpret(
    module: &Module,
    name: &str,
    args: &[Arg],
) -> Result<Vec<InterpretValue>, trust_ir::interpret::InterpretError> {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("the sweep module defines no `{name}`"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args.iter().map(|arg| interpret_arg(module, arg)))?;
    assert_eq!(outcome.host_calls, 0, "`{name}`: the run must be in-format");
    Ok(outcome.returns)
}

/// The interpreter's value of `call` (its oracle), or `None` for a
/// C-model-only call.
pub fn oracle_bits(module: &Module, call: &Call) -> Option<u128> {
    let (func, args) = match call.oracle.as_ref()? {
        Oracle::Same => (call.func, call.args.clone()),
        Oracle::Twin(func, args) => (*func, args.clone()),
    };
    let returns = interpret(module, func, &args)
        .unwrap_or_else(|error| panic!("{}: interpret `{func}`: {error:?}", call.key));
    let [value] = returns.as_slice() else {
        panic!("{}: `{func}` returned {returns:?}", call.key)
    };
    Some(interpret_bits(value))
}

/// The sweep modules are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Every sweep compile states `Permit` explicitly, so
/// no row passes or is refused because the license silently refused it.
pub fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}

/// Compile `module` for aarch64-apple-darwin.
pub fn compile(module: &Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    compile_with(module, opt_level, false)
}

/// [`compile`] with DWARF emission on or off.
pub fn compile_with(
    module: &Module,
    opt_level: OptLevel,
    emit_debug: bool,
) -> Result<Vec<u8>, String> {
    let spec = TargetSpec::parse(TRIPLE).map_err(|error| format!("{error:?}"))?;
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_debug,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error:?}"))
}

/// A linked driver executable in its own scratch directory.
pub struct Linked {
    pub dir: PathBuf,
    pub binary: PathBuf,
}

impl Drop for Linked {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

/// Link `object` with the C `driver` into an executable.
pub fn link(tag: &str, object: &[u8], driver: &str) -> Linked {
    assert_eq!(
        &object[..4],
        &[0xcf, 0xfa, 0xed, 0xfe],
        "{tag}: Mach-O 64 object expected"
    );
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-construct-sweep-{tag}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|elapsed| elapsed.as_nanos())
            .unwrap_or_default()
    ));
    fs::create_dir_all(&dir).unwrap_or_else(|error| panic!("{tag}: {dir:?}: {error}"));
    fs::write(dir.join("module.o"), object).unwrap_or_else(|error| panic!("{tag}: {error}"));
    fs::write(dir.join("driver.c"), driver).unwrap_or_else(|error| panic!("{tag}: {error}"));
    let binary = dir.join("driver");
    let linked = process::command_output_with_timeout(
        Command::new("cc")
            .arg("-O1")
            .arg("-Wall")
            .arg("-Werror")
            .arg(dir.join("driver.c"))
            .arg(dir.join("module.o"))
            .arg("-o")
            .arg(&binary),
        process::codegen_link_timeout(),
    )
    .unwrap_or_else(|error| panic!("{tag}: cc: {error}"));
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{tag}: link failed (files kept in {dir:?}): {}",
        String::from_utf8_lossy(&linked.output.stderr)
    );
    Linked { dir, binary }
}

/// Run the driver with no mode; the `key=value` table and the verdict line.
pub fn run_calls(tag: &str, linked: &Linked) -> (BTreeMap<String, u128>, String) {
    let run = process::run_executable_with_timeout(&linked.binary, process::codegen_run_timeout())
        .unwrap_or_else(|error| panic!("{tag}: run: {error}"));
    let stdout = String::from_utf8_lossy(&run.output.stdout).to_string();
    assert!(
        !run.timed_out && run.output.status.success(),
        "{tag}: driver failed ({:?}): {stdout}{}",
        run.output.status,
        String::from_utf8_lossy(&run.output.stderr)
    );
    let mut values = BTreeMap::new();
    let mut verdict = String::new();
    for line in stdout.lines() {
        match line.split_once('=') {
            Some((key, hex)) if !line.starts_with("MISMATCH") => {
                let bits = u128::from_str_radix(hex.trim(), 16)
                    .unwrap_or_else(|error| panic!("{tag}: `{line}`: {error}"));
                values.insert(key.to_string(), bits);
            }
            _ => verdict = line.trim().to_string(),
        }
    }
    (values, verdict)
}

/// Run the driver in trap `mode`; the terminating signal, if any.
pub fn run_trap(tag: &str, linked: &Linked, mode: &str) -> Option<i32> {
    let run = process::command_output_with_timeout(
        Command::new(&linked.binary).arg(mode),
        process::codegen_run_timeout(),
    )
    .unwrap_or_else(|error| panic!("{tag}: run {mode}: {error}"));
    assert!(!run.timed_out, "{tag}: `{mode}` timed out");
    run.output.status.signal()
}

/// The whole native sweep of `calls` and `traps` over `module` at O0-O3:
/// compile, link, run; every call's C model must agree (`PASS n`), every
/// oracle'd call must equal the interpreter, and every trap mode must die by
/// a trap signal where the interpreter refuses with the named code. Returns
/// the number of interpreter comparisons made per level.
pub fn sweep(
    tag: &str,
    module: &Module,
    calls: &[Call],
    traps: &[Trap],
    prelude: &str,
    extra: &str,
) -> usize {
    let validation = trust_ir_build::validate_module(module);
    assert!(
        validation.is_empty(),
        "{tag}: the sweep module must be valid trust-ir: {validation:?}"
    );
    let expected: Vec<(String, u128)> = calls
        .iter()
        .filter_map(|call| oracle_bits(module, call).map(|bits| (call.key.clone(), bits)))
        .collect();
    for trap in traps {
        let refused = interpret(module, trap.func, &trap.args).expect_err(trap.mode);
        assert_eq!(
            refused.code, trap.refusal,
            "{tag}: `{}`: the interpreter must refuse with {:?}: {refused:?}",
            trap.mode, trap.refusal
        );
    }
    let models = calls.iter().filter(|call| call.c_model.is_some()).count()
        + extra.matches("report(\"").count();
    let source = driver(module, calls, traps, prelude, extra);
    for opt_level in LEVELS {
        let level_tag = format!("{tag}-{opt_level:?}");
        let object = compile(module, opt_level)
            .unwrap_or_else(|error| panic!("{level_tag}: compile: {error}"));
        let linked = link(&level_tag, &object, &source);
        let (native, verdict) = run_calls(&level_tag, &linked);
        assert_eq!(
            verdict,
            format!("PASS {models} c-model checks"),
            "{level_tag}: the driver's C models disagree (files in {:?})",
            linked.dir
        );
        for call in calls {
            assert!(
                native.contains_key(&call.key),
                "{level_tag}: no native value for `{}`",
                call.key
            );
        }
        for (key, want) in &expected {
            assert_eq!(
                native.get(key),
                Some(want),
                "{level_tag}: native `{key}` disagrees with the reference interpreter"
            );
        }
        for trap in traps {
            let signal = run_trap(&level_tag, &linked, trap.mode);
            assert!(
                signal.is_some_and(|signal| TRAP_SIGNALS.contains(&signal)),
                "{level_tag}: `{}` must die by a trap signal, got {signal:?}",
                trap.mode
            );
        }
        eprintln!(
            "{level_tag}: {verdict}; {} interpreter comparisons; {} trap mode(s)",
            expected.len(),
            traps.len()
        );
    }
    expected.len()
}

/// Whether `object` carries the 32-bit instruction word `word` at a 4-byte
/// aligned offset of its bytes (a structural read-back, not a disassembly).
pub fn object_has_word(object: &[u8], word: u32) -> bool {
    object
        .as_chunks::<4>()
        .0
        .iter()
        .any(|chunk| u32::from_le_bytes(*chunk) == word)
}

/// `dwarfdump` output for `object` (written to a scratch file).
pub fn dwarfdump(tag: &str, object: &[u8], args: &[&str]) -> String {
    let path = std::env::temp_dir().join(format!(
        "trust-cg-construct-sweep-{tag}-{}.o",
        std::process::id()
    ));
    fs::write(&path, object).unwrap_or_else(|error| panic!("{tag}: {error}"));
    let run = process::command_output_with_timeout(
        Command::new("/usr/bin/dwarfdump").args(args).arg(&path),
        process::codegen_link_timeout(),
    )
    .unwrap_or_else(|error| panic!("{tag}: dwarfdump: {error}"));
    let _ = fs::remove_file(&path);
    assert!(
        !run.timed_out && run.output.status.success(),
        "{tag}: dwarfdump {args:?}: {}",
        String::from_utf8_lossy(&run.output.stderr)
    );
    String::from_utf8_lossy(&run.output.stdout).to_string()
}

/// Whether `path` exists (host tool probe).
pub fn has_tool(path: &str) -> bool {
    Path::new(path).exists()
}
