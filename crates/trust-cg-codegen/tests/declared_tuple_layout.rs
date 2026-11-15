//! WS7.7 — v42 declared tuple layouts are consumed natively when they agree
//! with the byte path, and refused by name when they do not.
//!
//! Before WS7.7 every module carrying a nonempty `Module.tuple_layouts`
//! outside the flat pointer-transport profile was refused
//! (`DeclaredTupleLayoutUnsupported`). tRust stamps a row for every tuple it
//! emits, so that refusal covered ordinary Rust — and masked the F-111
//! aliasing miscompile on real producer output (row `verify.c13.L1`: "Source
//! trust-cg pin+HEAD REFUSE that module … (v42 tuple_layout unsupported)").
//!
//! The rule (`trust_cg_lower::declared_tuple_layout`): a row is admitted only
//! when it EQUALS the declaration-order layout the byte path emits for that
//! tuple (every field offset, the size, the align), so the declared layout is
//! honoured by construction; any other row is refused as
//! `DeclaredTupleLayoutDisagrees`, naming the first component that differs.
//!
//! * Positive, row `verify.c13.L1`: `c13c.trust_ir`, the source-built trustc's
//!   output for ordinary safe Rust that takes two `InsertField`s off ONE tuple
//!   value (`let s = (0, 5); let mut p = s; let mut q = s; p.0 = a; q.0 = b;`),
//!   vendored verbatim from the 2026-09-17 proof program. Its row is the
//!   natural `[0, 8]`, so it now compiles, and runs to the Rust value
//!   `c13_tuple(1, 2) == 1002` at O0-O3, equal to the reference interpreter.
//!   It is correct only because insert results own fresh storage (the WS7.1
//!   value lowering, trust-cg `fda1c5e5c`); the aliasing lowering gave
//!   `2002002` on this module once the row was stripped.
//! * Negative twin: the same module with the row's offsets swapped is refused
//!   as `DeclaredTupleLayoutDisagrees` at field 0 (declared 8, emitted 0).
//! * Adversarial: a padded tuple, the same offsets but a declared size one
//!   alignment step larger (24) than the carrier (16), is refused at the size.
//! * Adversarial, real rustc output: `tup.trust_ir` (the c14 by-design lens,
//!   `file` path shortened to `tup.rs`) holds rustc's reordered
//!   `(u16, u64, u8)` (`u64@0 u16@8 u8@10`, size 16), refused at its field 0.
//! * Declared-layout storage read by by-value code: a tuple-typed global is
//!   laid out by the object writer at the DECLARED offsets, and loaded and
//!   projected by the byte path at the declaration-order ones. Under an
//!   agreeing row the native read equals the interpreter.
//! * Mutation control (`--features mutation-knobs`): admitting the REORDERED
//!   row of that same global (substituting the declaration-order layout for
//!   the producer's) compiles, and the native read then disagrees with the
//!   interpreter — so the refusal is what keeps this module correct.
//!
//! Fixture licensing: the c13/c14 modules carry the producer's
//! `gated "trust-direct-lane-structural"` license, which this test's compiler
//! recognizes EXPLICITLY; the hand-built global module has no license and
//! runs under an explicit `Permit`.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::HashMap;
use std::sync::Mutex;

use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, jit::ExecutableBuffer, pipeline::OptLevel,
};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::value::GlobalId;
use trust_ir::{
    Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, StructPassingPolicy, TargetInfo, TupleLayoutDescriptor, Ty, ValueId,
};

/// The mutation knob is process-global; every test that compiles holds this.
static KNOB: Mutex<()> = Mutex::new(());

const FIXTURES: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/declared_tuple_layout"
);

/// The license the source-built trustc stamps on these bodies.
const STRUCTURAL_AUTHORITY: &str = "trust-direct-lane-structural";

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn fixture_text(name: &str) -> String {
    let path = format!("{FIXTURES}/{name}");
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"))
}

/// Parse `text` and require it to be VALID trust-ir at the pinned trust-ir: a
/// finding about the consumer is only meaningful on input the format accepts.
fn parse_valid(label: &str, text: &str) -> Module {
    let module =
        trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("parse {label}: {e:?}"));
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "{label} must be valid trust-ir"
    );
    module
}

fn compiler(opt: OptLevel) -> Compiler {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt;
    Compiler::new_for_target_spec(config, host.target_spec()).with_codegen_license(
        CodegenLicensePolicy::default()
            .with_recognized_authority(STRUCTURAL_AUTHORITY)
            .with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}

fn jit(module: &Module, opt: OptLevel) -> ExecutableBuffer {
    compiler(opt)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|e| panic!("JIT compile of `{}` at {opt:?}: {e}", module.name))
        .buffer
}

/// The refusal text for `module`, which must NOT compile.
fn refusal(module: &Module) -> String {
    match compiler(OptLevel::O0).compile_module_to_jit(module, &HashMap::new()) {
        Ok(_) => panic!("`{}` must be refused", module.name),
        Err(e) => e.to_string(),
    }
}

/// The `DeclaredTupleLayoutDisagrees` message for one component.
fn disagreement(tuple: &str, ty: u32, component: &str, declared: u64, emitted: u64) -> String {
    format!(
        "the declared layout of tuple `{tuple}` (ty.{ty}) disagrees with the \
         declaration-order layout this backend emits at its {component}: \
         declared {declared}, emitted {emitted}"
    )
}

fn interpret(module: &Module, name: &str, args: &[u64]) -> u64 {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let args = args
        .iter()
        .map(|v| InterpretValue::int(Ty::U64, i128::from(*v)).expect("u64 argument"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args)
        .unwrap_or_else(|e| panic!("interpret {name}: {e:?}"));
    let [ret] = outcome.returns.as_slice() else {
        panic!("{name}: expected one result, got {:?}", outcome.returns)
    };
    u64::try_from(ret.as_int().expect("integer result").as_unsigned()).expect("u64 result")
}

fn call2(buffer: &ExecutableBuffer, name: &str, a: u64, b: u64) -> u64 {
    // SAFETY: `name` is declared `(u64, u64) -> (u64)`, and `buffer` outlives
    // the call.
    unsafe {
        buffer
            .get_fn_bound::<extern "C" fn(u64, u64) -> u64>(name)
            .expect(name)
            .as_ref()(a, b)
    }
}

fn call0(buffer: &ExecutableBuffer, name: &str) -> u64 {
    // SAFETY: `name` is declared `() -> (u64)`, and `buffer` outlives the call.
    unsafe {
        buffer
            .get_fn_bound::<extern "C" fn() -> u64>(name)
            .expect(name)
            .as_ref()()
    }
}

/// `c13_tuple(a, b) = p.0 * 1000 + q.0 + s.0 * 1000000` with `p.0 = a`,
/// `q.0 = b`, `s.0 = 0`. The vectors stay clear of overflow.
fn c13_tuple(a: u64, b: u64) -> u64 {
    a * 1000 + b
}

const C13_VECTORS: &[(u64, u64)] = &[(1, 2), (0, 0), (7, 999), (1 << 40, 3), (123_456, 1)];

/// Row `verify.c13.L1`: the tRust-produced Rust tuple module (natural row
/// `[0, 8]`) is no longer refused for its tuple layout, and runs to the Rust
/// value `c13_tuple(1, 2) == 1002` — not the aliasing `2002002`.
#[test]
fn verify_c13_l1_rust_tuple_module_with_declared_layout_runs_to_1002() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let text = fixture_text("c13c.trust_ir");
    assert!(
        text.contains("tuple_layout ty.0 size=16 align=8 offsets=[0,8]"),
        "the vendored module must carry its declared tuple layout"
    );
    let module = parse_valid("c13c.trust_ir", &text);
    assert_eq!(module.tuple_layouts.len(), 1);
    for &(a, b) in C13_VECTORS {
        assert_eq!(
            interpret(&module, "c13_tuple", &[a, b]),
            c13_tuple(a, b),
            "interpreter c13_tuple({a}, {b})"
        );
    }
    for opt in OPTS {
        let buffer = jit(&module, opt);
        assert_eq!(
            call2(&buffer, "c13_tuple", 1, 2),
            1002,
            "c13_tuple(1, 2) at {opt:?}"
        );
        for &(a, b) in C13_VECTORS {
            assert_eq!(
                call2(&buffer, "c13_tuple", a, b),
                c13_tuple(a, b),
                "c13_tuple({a}, {b}) at {opt:?}"
            );
        }
    }
}

/// Negative twin: the SAME module with the row's offsets swapped (valid
/// trust-ir: `u64@8 u64@0` is a coherent layout) is refused by name.
#[test]
fn swapped_tuple_offsets_are_refused_as_a_layout_disagreement() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let text = fixture_text("c13c.trust_ir").replace(
        "tuple_layout ty.0 size=16 align=8 offsets=[0,8]",
        "tuple_layout ty.0 size=16 align=8 offsets=[8,0]",
    );
    let module = parse_valid("c13c.swapped", &text);
    let message = refusal(&module);
    let expected = disagreement("(u64, u64)", 0, "field 0 offset", 8, 0);
    assert!(
        message.contains(&expected),
        "want `{expected}`, got: {message}"
    );
}

/// Adversarial: a padded tuple — the offsets agree, but the declared size is
/// one alignment step past the carrier every slot and copy is sized from.
#[test]
fn padded_tuple_size_is_refused_as_a_layout_disagreement() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let text = fixture_text("c13c.trust_ir").replace(
        "tuple_layout ty.0 size=16 align=8 offsets=[0,8]",
        "tuple_layout ty.0 size=24 align=8 offsets=[0,8]",
    );
    let module = parse_valid("c13c.padded", &text);
    let message = refusal(&module);
    let expected = disagreement("(u64, u64)", 0, "size", 24, 16);
    assert!(
        message.contains(&expected),
        "want `{expected}`, got: {message}"
    );
}

/// Adversarial, real rustc output: rustc reorders `repr(Rust)` tuples, and
/// the producer states it. The module's first row agrees; the second
/// (`(u16, u64, u8)`: `u64@0 u16@8 u8@10`, size 16) is refused at field 0.
#[test]
fn rustc_reordered_tuple_is_refused_as_a_layout_disagreement() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = parse_valid("tup.trust_ir", &fixture_text("tup.trust_ir"));
    assert_eq!(module.tuple_layouts.len(), 3);
    let message = refusal(&module);
    let expected = disagreement("(u16, u64, u8)", 1, "field 0 offset", 8, 0);
    assert!(
        message.contains(&expected),
        "want `{expected}`, got: {message}"
    );
}

/// `(u8, u64)` global `{ 0x12, 0x0123456789abcdef }` under `offsets`, read
/// back by `read_word() = extractfield u64 (load (u8, u64), @gl_tuple), 1`
/// and `read_tag() = zext (extractfield u8 (load ..), 0)`.
fn tuple_global_module(offsets: [u64; 2]) -> Module {
    let mut module = Module::new("declared_tuple_global");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let tuple_type = module
        .add_type(tuple.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type,
        size: 16,
        align: 8,
        field_offsets: offsets.to_vec(),
    });
    module.globals.push(Global {
        name: "gl_tuple".into(),
        ty: tuple.clone(),
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(0x12),
            Constant::Int(0x0123_4567_89ab_cdef),
        ])),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let v = ValueId::new;
    for (index, (name, field)) in [("read_word", 1u32), ("read_tag", 0u32)]
        .into_iter()
        .enumerate()
    {
        let mut function = Function::new(
            FuncId::new(u32::try_from(index).expect("two functions")),
            name,
            sig,
            BlockId::new(0),
        );
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: tuple.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
        );
        let lane = if field == 1 { Ty::U64 } else { Ty::U8 };
        block.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: lane.clone(),
                aggregate: v(1),
                field,
            })
            .with_result(v(2)),
        );
        let result = if field == 1 {
            v(2)
        } else {
            block.body.push(
                InstrNode::new(Inst::Cast {
                    op: trust_ir::CastOp::ZExt,
                    src_ty: Ty::U8,
                    dst_ty: Ty::U64,
                    operand: v(2),
                })
                .with_result(v(3)),
            );
            v(3)
        };
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![result],
        }));
        function.blocks.push(block);
        module.functions.push(function);
    }
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "the tuple-global module must be valid trust-ir"
    );
    module
}

const GLOBAL_READS: [(&str, u64); 2] = [("read_word", 0x0123_4567_89ab_cdef), ("read_tag", 0x12)];

/// The object writer lays the global out at the DECLARED offsets; the byte
/// path loads and projects it at the declaration-order ones. Under an
/// agreeing row the two are one layout, and the native read is the
/// interpreter's.
#[test]
fn agreeing_declared_layout_global_reads_back_through_by_value_code() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = tuple_global_module([0, 8]);
    for (name, want) in GLOBAL_READS {
        assert_eq!(interpret(&module, name, &[]), want, "interpreter {name}");
    }
    for opt in OPTS {
        let buffer = jit(&module, opt);
        for (name, want) in GLOBAL_READS {
            assert_eq!(call0(&buffer, name), want, "{name} at {opt:?}");
        }
    }
}

/// The reordered twin of that global is refused, not substituted.
#[test]
fn reordered_declared_layout_global_is_refused_by_name() {
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = tuple_global_module([8, 0]);
    for (name, want) in GLOBAL_READS {
        assert_eq!(interpret(&module, name, &[]), want, "interpreter {name}");
    }
    let message = refusal(&module);
    let expected = disagreement("(u8, u64)", 0, "field 0 offset", 8, 0);
    assert!(
        message.contains(&expected),
        "want `{expected}`, got: {message}"
    );
}

/// A default build carries no mutation knob.
#[test]
fn default_build_has_no_mutation_knobs() {
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}

/// Mutation control: admit the REORDERED row (the declaration-order layout
/// silently substituted for the producer's). The module then compiles, and
/// the native reads disagree with the interpreter — the object writer placed
/// the word at byte 0 and the tag at byte 8, and the byte path reads them at
/// 8 and 0. So the refusal above is what keeps this module correct.
#[cfg(feature = "mutation-knobs")]
#[test]
fn mutation_admitting_a_disagreeing_row_is_caught_by_the_differential() {
    use trust_cg_lower::mutation_knobs::set_admit_disagreeing_tuple_layouts;
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            set_admit_disagreeing_tuple_layouts(false);
        }
    }
    let _knob = KNOB.lock().unwrap_or_else(|p| p.into_inner());
    let module = tuple_global_module([8, 0]);
    let _reset = Reset;
    set_admit_disagreeing_tuple_layouts(true);
    for opt in OPTS {
        let buffer = jit(&module, opt);
        let mismatches = GLOBAL_READS
            .iter()
            .filter(|(name, _)| call0(&buffer, name) != interpret(&module, name, &[]))
            .count();
        assert_eq!(
            mismatches,
            GLOBAL_READS.len(),
            "the substituted tuple layout went unnoticed at {opt:?}"
        );
    }
}
