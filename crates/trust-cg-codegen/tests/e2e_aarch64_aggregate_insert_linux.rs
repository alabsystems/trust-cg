// Copyright 2026 Andrew Yates | Apache-2.0
//! Value semantics of aggregate `InsertField` / `InsertElement` on AArch64
//! (Linux floor target, with host-neutral rows the Darwin floor also runs).
//!
//! trust-ir aggregates are values, while the backend represents one by the
//! address of its storage. An insert therefore has to produce storage of its
//! own whenever its source is still live: `swap(s) = insert(insert(s, 0,
//! s.1), 1, s.0)` reads `s.0` after the first insert, and the adapter used to
//! lower every insert as a store into the source's storage (2026-09-23:
//! `{1,2}` swapped to `{2,2}` at every optimization level). The same class
//! covers a source that is a parameter, a load, a constant, a call result, a
//! `Copy`, a `Select`, a block parameter, an interior field, a stored value,
//! and loop-carried values; the corpus (`fixtures/aggregate_insert`) has one
//! function per shape.
//!
//! Host-neutral rows: the corpus is canonical trust-ir, the reference
//! interpreter agrees with a closed-form model of every shape it can run,
//! the adapter's copy/in-place decisions and parameter storage are pinned on
//! the lowered LIR, the store form (an insert through a pointer, invalid
//! trust-ir) is refused by name, and the corpus compiles for Linux and
//! Darwin at O0-O3. The
//! Linux-only row links each object with `cc` against the C oracle
//! (`driver.c`) and requires every field of every shape to match bit-exactly
//! at O0-O3. Execution and structural evidence, not a proof.
//!
//! Zero-sized aggregates (`fixtures/aggregate_insert/zero_sized.trust_ir`):
//! the first version of this lowering emitted a zero-length `Memcpy` for a
//! `()` or empty-struct block parameter, staging copy or insert copy.
//! Selection lowers that to no machine instruction and the dataflow-integrity
//! gate refused the dropped effect, so shapes the base compiled failed to
//! compile at O0-O3. Host-neutral rows pin that no such copy is emitted and
//! that the eight shapes compile for Linux and Darwin at O0-O3 and agree with
//! the reference interpreter; a Linux-only row runs them against
//! `zero_sized_driver.c`.

use std::collections::BTreeMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::{Instruction, Opcode, Value};
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{Module, StructId, Ty};

const CORPUS: &str = include_str!("fixtures/aggregate_insert/corpus.trust_ir");
const ZERO_SIZED: &str = include_str!("fixtures/aggregate_insert/zero_sized.trust_ir");
const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Every corpus function the C driver checks, with its expected number of
/// bit-exact field checks (the driver's `shape NAME checks=N` line).
/// `make_pair` is only a callee of `call_result`.
const SHAPES: &[(&str, u32)] = &[
    ("swap_i64", 8),
    ("swap_f32", 8),
    ("swap_f16", 8),
    ("old_new", 64),
    ("big_callee", 20),
    ("big_caller", 16),
    ("load_insert", 96),
    ("global_insert", 24),
    ("nested_inner", 64),
    ("nested_outer", 64),
    ("array_elem", 64),
    ("copy_shape", 64),
    ("select_shape", 128),
    ("phi_join", 128),
    ("loop_prev", 96),
    ("loop_exit_old", 96),
    ("loop_swap", 48),
    ("loop_rotate", 96),
    ("const_twice", 16),
    ("call_result", 16),
    ("store_after", 80),
    ("vec_shape", 16),
    ("packed_shape", 16),
    ("fanout", 64),
    ("vec_f32", 16),
    ("loop_load_prev", 12),
    ("loop_const_prev", 96),
];

fn corpus() -> Module {
    trust_ir::parser::parse_module(CORPUS).expect("the corpus parses")
}

fn corpus_for(triple: &str) -> Module {
    let mut module = corpus();
    module
        .target_info
        .as_mut()
        .expect("the corpus declares a target")
        .triple = triple.into();
    module
}

fn compile(module: &Module, triple: &str, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error:?}"))
}

// ---------------------------------------------------------------------------
// Closed-form model and reference interpreter
// ---------------------------------------------------------------------------

const PAIRS: [[i64; 2]; 4] = [
    [1, 2],
    [-5, i64::MAX],
    [0x0123_4567_89ab_cdef, -1],
    [0, i64::MIN],
];
const VALUES: [i64; 4] = [42, -9, i64::MIN, 0x5a5a_5a5a_5a5a_5a5a];
const TRIPS: [i64; 6] = [0, 1, 2, 3, 5, 8];

fn int(ty: Ty, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("integer argument")
}

fn i64v(value: i64) -> InterpretValue {
    int(Ty::I64, value.into())
}

fn aggregate(id: u32, fields: Vec<InterpretValue>) -> InterpretValue {
    InterpretValue {
        ty: Ty::Struct(StructId::new(id)),
        kind: InterpretValueKind::Aggregate(fields),
    }
}

fn float(ty: Ty, bits: u64) -> InterpretValue {
    InterpretValue {
        ty,
        kind: InterpretValueKind::FloatBits(bits),
    }
}

fn pair(p: [i64; 2]) -> InterpretValue {
    aggregate(0, vec![i64v(p[0]), i64v(p[1])])
}

fn quad(q: [i64; 4]) -> InterpretValue {
    aggregate(3, q.iter().map(|v| i64v(*v)).collect())
}

fn outer(p: [i64; 2], x: i64) -> InterpretValue {
    aggregate(4, vec![pair(p), i64v(x)])
}

/// The leaves of an interpreter value as raw bit patterns, depth-first.
fn leaves(value: &InterpretValue, out: &mut Vec<u64>) {
    match &value.kind {
        InterpretValueKind::Int(int) => out.push(int.as_unsigned() as u64),
        InterpretValueKind::FloatBits(bits) => out.push(*bits),
        InterpretValueKind::Aggregate(fields) => {
            for field in fields {
                leaves(field, out);
            }
        }
        // trust-ir v50: a vector value is an `ArrayValue` rope; these are
        // short fixed vectors, so every lane is read in order.
        InterpretValueKind::Vector(lanes) => {
            for lane in lanes.iter() {
                leaves(lane, out);
            }
        }
        other => panic!("unexpected interpreter value {other:?}"),
    }
}

fn interpret(module: &Module, name: &str, args: Vec<InterpretValue>) -> Vec<u64> {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args)
        .unwrap_or_else(|e| panic!("interpret {name}: {e:?}"));
    let mut out = Vec::new();
    for value in &outcome.returns {
        leaves(value, &mut out);
    }
    out
}

fn bits(values: &[i64]) -> Vec<u64> {
    values.iter().map(|v| *v as u64).collect()
}

/// One interpreter call and the closed-form value-semantics model's answer.
struct Case {
    name: &'static str,
    args: Vec<InterpretValue>,
    want: Vec<u64>,
}

fn model_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let mut add = |name, args, want| cases.push(Case { name, args, want });
    for p in PAIRS {
        add("swap_i64", vec![pair(p)], bits(&[p[1], p[0]]));
    }
    for (a, b) in [(1.0f32, 2.0f32), (-0.0, 3.5), (1e30, -1e-30), (0.1, -7.25)] {
        let (a, b) = (u64::from(a.to_bits()), u64::from(b.to_bits()));
        let arg = aggregate(1, vec![float(Ty::F32, a), float(Ty::F32, b)]);
        add("swap_f32", vec![arg], vec![b, a]);
    }
    for (a, b) in [
        (0x3c00u64, 0x4000u64),
        (0x8000, 0x4300),
        (0x7bff, 0xb400),
        (0x3000, 0xc700),
    ] {
        let arg = aggregate(2, vec![float(Ty::F16, a), float(Ty::F16, b)]);
        add("swap_f16", vec![arg], vec![b, a]);
    }
    for (i, p) in PAIRS.iter().enumerate() {
        let v = VALUES[i];
        add(
            "old_new",
            vec![pair(*p), i64v(v)],
            bits(&[p[0], p[1], v, p[1]]),
        );
        add(
            "copy_shape",
            vec![pair(*p), i64v(v)],
            bits(&[p[0], p[1], v, p[0]]),
        );
        let w = !v;
        add(
            "fanout",
            vec![pair(*p), i64v(v), i64v(w)],
            bits(&[v, w, p[1], p[1]]),
        );
        let o = outer(*p, 1000 + i as i64);
        add(
            "nested_inner",
            vec![o.clone(), i64v(v)],
            bits(&[p[1], v, p[1], 1000 + i as i64]),
        );
        add(
            "nested_outer",
            vec![o, pair([v, !v])],
            bits(&[p[0], v, p[1], 1000 + i as i64]),
        );
        let b = PAIRS[(i + 1) % PAIRS.len()];
        for c in [0i64, 1] {
            let sel = if c != 0 { *p } else { b };
            add(
                "select_shape",
                vec![pair(*p), pair(b), i64v(c), i64v(v)],
                bits(&[p[0], b[0], v, sel[0]]),
            );
            add(
                "phi_join",
                vec![pair(*p), pair(b), i64v(c), i64v(v)],
                bits(&[p[1], b[1], sel[1], v]),
            );
        }
    }
    for (i, v) in VALUES.iter().enumerate() {
        let b = [11, 22, 33 + i as i64, 44];
        add(
            "big_callee",
            vec![quad(b), i64v(*v)],
            bits(&[v.wrapping_add(44)]),
        );
        add(
            "big_caller",
            vec![quad(b), i64v(*v)],
            bits(&[11, 22, 33 + i as i64, v.wrapping_add(44)]),
        );
        let w = VALUES[(i + 1) % VALUES.len()];
        add("const_twice", vec![i64v(*v), i64v(w)], bits(&[*v, 2, 1, w]));
        add("call_result", vec![i64v(*v)], bits(&[7, 8, *v, 8]));
        let lane = *v as i32;
        add(
            "vec_shape",
            vec![int(Ty::I32, lane.into())],
            bits(&[3, lane.into(), 1, 1]),
        );
    }
    for a in [-0.0f32, 1.5, 1e-40, -3.25e7] {
        let arg = float(Ty::F32, u64::from(a.to_bits()));
        let f = |x: f32| i64::from(x.to_bits());
        add("vec_f32", vec![arg], bits(&[f(2.0), f(a), f(4.0), f(4.0)]));
    }
    for (i, p) in PAIRS.iter().enumerate() {
        for n in TRIPS {
            let (mut acc, mut sum) = (*p, 0i64);
            for k in 0..n {
                let old0 = acc[0];
                acc = [acc[1].wrapping_add(k), old0];
                sum = sum.wrapping_mul(31).wrapping_add(old0);
            }
            add(
                "loop_prev",
                vec![pair(*p), i64v(n)],
                bits(&[acc[0], acc[1], sum, n]),
            );
            let (mut before, mut j) = (*p, 0i64);
            let after = loop {
                let next = [j, before[1]];
                if j + 1 < n {
                    before = next;
                    j += 1;
                } else {
                    break next;
                }
            };
            add(
                "loop_exit_old",
                vec![pair(*p), i64v(n)],
                bits(&[before[0], before[1], after[0], after[1]]),
            );
            let swapped = if n % 2 == 1 { [p[1], p[0]] } else { *p };
            add("loop_swap", vec![pair(*p), i64v(n)], bits(&swapped));
            let (mut a, mut b) = (*p, PAIRS[(i + 1) % PAIRS.len()]);
            for k in 0..n {
                let a2 = [a[0].wrapping_add(k), a[1]];
                a = b;
                b = a2;
            }
            add(
                "loop_rotate",
                vec![pair(*p), pair(PAIRS[(i + 1) % PAIRS.len()]), i64v(n)],
                bits(&[a[0], a[1], b[0], b[1]]),
            );
            let (mut acc, mut sum) = (*p, 0i64);
            for k in 0..n {
                let old0 = acc[0];
                acc = [k, acc[0].wrapping_add(acc[1])];
                sum = sum.wrapping_mul(31).wrapping_add(old0);
            }
            add(
                "loop_const_prev",
                vec![pair(*p), i64v(n)],
                bits(&[acc[0], acc[1], sum, n]),
            );
        }
    }
    cases
}

#[test]
fn corpus_is_canonical_trust_ir_defining_every_shape() {
    let module = corpus();
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "the corpus must validate: {errors:?}");
    for (name, _) in SHAPES {
        assert!(
            module
                .functions
                .iter()
                .any(|f| f.name == *name && !f.blocks.is_empty()),
            "{name} is not defined"
        );
    }
}

/// The reference interpreter gives trust-ir's value semantics; the closed
/// forms are the same model the C oracle implements.
#[test]
fn reference_interpreter_agrees_with_the_value_semantics_model() {
    let module = corpus();
    let cases = model_cases();
    let mut per_shape = BTreeMap::<&str, usize>::new();
    for case in cases {
        let got = interpret(&module, case.name, case.args);
        assert_eq!(got, case.want, "{}", case.name);
        *per_shape.entry(case.name).or_default() += 1;
    }
    assert_eq!(per_shape.len(), 21, "interpreted shapes: {per_shape:?}");
}

// ---------------------------------------------------------------------------
// Lowered LIR: copy versus in place, and block-parameter storage
// ---------------------------------------------------------------------------

fn lowered() -> Vec<LirFunction> {
    permit_translate_module(&corpus())
        .expect("the corpus lowers")
        .into_iter()
        .map(|(function, _)| function)
        .collect()
}

fn function<'a>(functions: &'a [LirFunction], name: &str) -> &'a LirFunction {
    functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no lowered function {name}"))
}

fn instructions(function: &LirFunction) -> Vec<&Instruction> {
    function
        .block_order
        .iter()
        .flat_map(|block| function.blocks[block].instructions.iter())
        .collect()
}

fn count(function: &LirFunction, pred: impl Fn(&Opcode) -> bool) -> usize {
    instructions(function)
        .iter()
        .filter(|i| pred(&i.opcode))
        .count()
}

/// Follow `Copy` definitions from `value` back to the value that defines its
/// storage.
fn root(insts: &[&Instruction], mut value: Value) -> Value {
    while let Some(def) = insts
        .iter()
        .find(|i| matches!(i.opcode, Opcode::Copy) && i.results.contains(&value))
    {
        value = def.args[0];
    }
    value
}

fn is_memcpy(op: &Opcode) -> bool {
    matches!(op, Opcode::Memcpy)
}

fn is_memmove(op: &Opcode) -> bool {
    matches!(op, Opcode::Memmove)
}

fn is_stack_addr(op: &Opcode) -> bool {
    matches!(op, Opcode::StackAddr { .. })
}

/// `(slot addresses, Memcpy, Memmove)` of a lowered function: the storage it
/// addresses and the byte copies it makes. A copy into fresh storage is a
/// `Memcpy`; a copy that may target its own source is a `Memmove`.
fn storage(functions: &[LirFunction], name: &str) -> (usize, usize, usize) {
    let f = function(functions, name);
    (
        count(f, is_stack_addr),
        count(f, is_memcpy),
        count(f, is_memmove),
    )
}

/// Each insert copies its source exactly when the source is still live, is
/// shared, or is not storage the adapter allocated; a dead, unshared source
/// defined in the same block is reused in place.
#[test]
fn inserts_copy_live_sources_and_reuse_dead_owned_ones() {
    let functions = lowered();
    // swap: the first insert copies the parameter (read again afterwards);
    // the second takes over that copy (its source is dead and unshared).
    assert_eq!(storage(&functions, "swap_i64"), (1, 1, 0), "swap_i64");
    let swap = function(&functions, "swap_i64");
    let insts = instructions(swap);
    let slot = insts
        .iter()
        .find(|i| is_stack_addr(&i.opcode))
        .map(|i| i.results[0])
        .unwrap();
    let copy = insts.iter().find(|i| is_memcpy(&i.opcode)).unwrap();
    assert_eq!(copy.args[..2], [slot, Value(0)], "the parameter is copied");
    for store in insts
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Store { .. }))
    {
        let address = store.args[1];
        let gep = insts
            .iter()
            .find(|i| i.results.contains(&address))
            .expect("the store address is computed in the function");
        assert_eq!(
            root(&insts, gep.args[0]),
            slot,
            "every field store targets the copy"
        );
    }
    // old_new: the parameter insert copies; the four-insert result chain is
    // built in place in its constant's slot.
    assert_eq!(storage(&functions, "old_new"), (2, 1, 0), "old_new");
    // const_twice: the constant has two inserts, so both copy it.
    assert_eq!(storage(&functions, "const_twice"), (4, 2, 0), "const_twice");
    // fanout: the parameter, and the first result (three uses), are copied
    // for every insert into them.
    assert_eq!(storage(&functions, "fanout"), (4, 3, 0), "fanout");
    // copy_shape: `Copy` shares the parameter's storage, so it is copied.
    assert_eq!(storage(&functions, "copy_shape"), (2, 1, 0), "copy_shape");
}

/// Aggregate block parameters own their storage and every edge copies the
/// argument's bytes into it. With two parameters, a source that is not
/// storage its own lowering allocated is staged first, because an edge may
/// pass one parameter's storage to the other.
#[test]
fn aggregate_block_parameters_own_their_storage() {
    let functions = lowered();
    let rotate = function(&functions, "loop_rotate");
    let header = rotate
        .block_order
        .iter()
        .filter(|block| **block != rotate.entry_block)
        .map(|block| &rotate.blocks[block])
        .find(|block| block.params.len() == 3)
        .expect("the loop header has three parameters");
    let insts = instructions(rotate);
    let slot_of = |value: Value| {
        insts.iter().find_map(|i| match i.opcode {
            Opcode::StackAddr { slot } if i.results.contains(&value) => Some(slot),
            _ => None,
        })
    };
    let mut slots = Vec::new();
    for (param, _) in header.params.iter().take(2) {
        let defs: Vec<_> = insts
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Copy) && i.results.contains(param))
            .collect();
        assert_eq!(defs.len(), 2, "one copy per incoming edge for {param:?}");
        let param_slots: Vec<_> = defs.iter().map(|i| slot_of(i.args[0])).collect();
        assert!(
            param_slots
                .iter()
                .all(|s| s.is_some() && *s == param_slots[0]),
            "{param:?} is always its own slot: {param_slots:?}"
        );
        slots.push(param_slots[0].unwrap());
    }
    assert_ne!(slots[0], slots[1], "each parameter owns distinct storage");
    // Entry edge: both arguments are parameters, so both are staged (2
    // staging + 2 parameter copies). Back edge: `b` is staged, the insert's
    // result (its own slot) is copied directly (1 + 2). The insert copies the
    // parameter it reads (1). Slot addresses: 3 staging, 4 parameter, the
    // insert's copy and the result constant.
    assert_eq!(storage(&functions, "loop_rotate"), (9, 8, 0), "loop_rotate");
    // A lone aggregate parameter receives an unowned argument by `Memmove` on
    // each edge; the insert then copies the parameter.
    let join = function(&functions, "phi_join");
    assert_eq!(storage(&functions, "phi_join"), (4, 1, 2), "phi_join");
    let join_param = join
        .block_order
        .iter()
        .map(|block| &join.blocks[block])
        .find(|block| block.params.len() == 1)
        .map(|block| block.params[0].0)
        .unwrap();
    let join_insts = instructions(join);
    let join_defs: Vec<_> = join_insts
        .iter()
        .filter(|i| matches!(i.opcode, Opcode::Copy) && i.results.contains(&join_param))
        .collect();
    assert_eq!(join_defs.len(), 2, "one copy per incoming edge");
    assert!(
        join_defs.iter().all(|i| join_insts.iter().any(|d| {
            matches!(d.opcode, Opcode::StackAddr { .. }) && d.results.contains(&i.args[0])
        })),
        "the join parameter always receives its own slot"
    );
}

/// An `InsertField` whose operand is a POINTER to the aggregate (an `Alloca`)
/// is the "store form": trust-ir does not define it (validator
/// `FieldAccessInvalid`, interpreter `TypeError`), and under value semantics
/// its write would land in the result's private copy and be lost while the
/// memory the program reads stays unwritten. It is refused by name (WS7.1
/// (b)); the rustc bridge now spells a field write `GEP` + `Store`.
#[test]
fn insert_through_an_aggregate_pointer_is_refused_by_name() {
    let module = trust_ir::parser::parse_module(
        r#"; TrustIr text format v1
module "insert_through_pointer"
target "aarch64-unknown-linux-gnu" 8 little abi="aapcs64"

struct @PairI64 { m0: i64 @0, m1: i64 @8 } size=16 align=8 repr=c id=0

functy.0 = (i64) -> (i64)

fn @store_through(functy.0) {
bb0(%0: i64):
    %1 = alloca struct.0
    %2 = insertfield struct.0 %1, 1, %0
    %3 = const i64 1
    %4 = gep i64, ptr %1, %3
    %5 = load i64, ptr %4
    ret %5
}
"#,
    )
    .expect("parses");
    let err = permit_translate_module(&module)
        .expect_err("the store form must be refused, never lowered as a store");
    assert!(
        matches!(
            &err,
            trust_cg_lower::adapter::AdapterError::AggregateInsertNotValueForm {
                function,
                op: "insertfield",
                value: 1,
                ..
            } if function == "store_through"
        ),
        "must be the named store-form refusal, got {err:?}"
    );
}

#[test]
fn corpus_compiles_for_linux_and_darwin_o0_through_o3() {
    for (triple, magic) in [
        (LINUX, &b"\x7fELF"[..]),
        (DARWIN, &[0xcf, 0xfa, 0xed, 0xfe][..]),
    ] {
        let module = corpus_for(triple);
        for level in LEVELS {
            let object = compile(&module, triple, level)
                .unwrap_or_else(|e| panic!("{triple} {level:?}: {e}"));
            assert_eq!(&object[..4], magic, "{triple} {level:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// Zero-sized aggregates
// ---------------------------------------------------------------------------

/// The closed-form model of one zero-sized-shape function.
type ShapeModel = fn(i64) -> i64;

/// The zero-sized corpus's functions, each `fn(i64) -> i64`, with the
/// closed-form model the C driver also implements.
const ZERO_SIZED_SHAPES: &[(&str, ShapeModel)] = &[
    ("unit_pair", |x| x.wrapping_mul(3)),
    ("empty_pair", |x| if x != 0 { x } else { 0 } + 1),
    ("empty_loop", |x| x.max(0)),
    ("empty_const_param", |x| x.wrapping_sub(7)),
    ("zero_insert", |x| x ^ 5),
    ("undef_unit_pair", |x| if x != 0 { x } else { 0 }),
    ("empty_field_loop", |x| if x > 0 { 0 } else { x }),
    ("field_insert_twice", |x| x.wrapping_add(10)),
];
const ZERO_SIZED_INPUTS: [i64; 5] = [0, 1, 5, -3, 1000];

fn zero_sized_for(triple: &str) -> Module {
    let mut module =
        trust_ir::parser::parse_module(ZERO_SIZED).expect("the zero-sized corpus parses");
    module
        .target_info
        .as_mut()
        .expect("the zero-sized corpus declares a target")
        .triple = triple.into();
    module
}

/// The `(Memcpy, Memmove)` byte lengths a lowered function copies, each
/// read from the `Iconst` that defines the copy's length operand.
fn copy_lengths(function: &LirFunction) -> (Vec<i64>, Vec<i64>) {
    let insts = instructions(function);
    let length = |value: Value| {
        insts
            .iter()
            .find_map(|i| match i.opcode {
                Opcode::Iconst { imm, .. } if i.results.contains(&value) => Some(imm),
                _ => None,
            })
            .expect("a copy length is a constant")
    };
    let mut memcpy = Vec::new();
    let mut memmove = Vec::new();
    for inst in &insts {
        match inst.opcode {
            Opcode::Memcpy => memcpy.push(length(inst.args[2])),
            Opcode::Memmove => memmove.push(length(inst.args[2])),
            _ => {}
        }
    }
    (memcpy, memmove)
}

/// A zero-sized value has no bytes, so its block-parameter copy, staging
/// copy and insert copy emit no `Memcpy`/`Memmove` at all. The only copies
/// left are the 8-byte copies of `field_insert_twice`'s two-use source
/// (`{i64, {}}`) and the older aggregate-field store that `zero_insert` and
/// `field_insert_twice` reach when they write a zero-sized field: a
/// `Memmove` of the field's extent, 0, which selection lowers to a
/// `memmove` libcall and the integrity gate accepts. The corpus validates and
/// the reference interpreter agrees with the closed-form model on every
/// shape it executes (it refuses `undef ()`, which `unit_pair` and
/// `undef_unit_pair` carry).
#[test]
fn zero_sized_values_lower_without_zero_length_copies() {
    let module = zero_sized_for(LINUX);
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "the zero-sized corpus validates: {errors:?}"
    );
    let interpreted = ZERO_SIZED_SHAPES
        .iter()
        .filter(|(name, _)| !matches!(*name, "unit_pair" | "undef_unit_pair"));
    for (name, model) in interpreted {
        for x in ZERO_SIZED_INPUTS {
            assert_eq!(
                interpret(&module, name, vec![i64v(x)]),
                bits(&[model(x)]),
                "{name}({x})"
            );
        }
    }
    let functions: Vec<LirFunction> = permit_translate_module(&module)
        .expect("the zero-sized corpus lowers")
        .into_iter()
        .map(|(function, _)| function)
        .collect();
    for (name, _) in ZERO_SIZED_SHAPES {
        let (memcpy, memmove) = copy_lengths(function(&functions, name));
        let want: (Vec<i64>, Vec<i64>) = match *name {
            "field_insert_twice" => (vec![8, 8], vec![0, 0]),
            "zero_insert" => (Vec::new(), vec![0, 0]),
            _ => (Vec::new(), Vec::new()),
        };
        assert_eq!((memcpy, memmove), want, "{name}: (Memcpy, Memmove) lengths");
    }
}

/// The reported reproducer, verbatim: two `()` block parameters fed from one
/// `const () { }`. That spelling is not a constant of `()` (trust-ir's one
/// spelling is `phantomdata`), and since every compiler entry consumes
/// TrustIR's typed admission it is refused by name; the test compiles the
/// reproducer with the unit constant spelled canonically.
const UNIT_REPRODUCER: &str = r#"; TrustIr text format v1
module "zst_repro"
target "aarch64-unknown-linux-gnu" 8 little abi="aapcs64"

functy.0 = (i64) -> (i64)

fn @unit_params(functy.0) {
bb0(%0: i64):
    %1 = const () { }
    br bb1(%1, %1, %0)
bb1(%2: (), %3: (), %4: i64):
    ret %4
}
"#;

/// The zero-sized corpus and the reproducer, its unit constant spelled
/// `phantomdata`, compile for Linux and Darwin at O0-O3 (until 2026-09-23 the
/// dataflow-integrity gate refused the dropped zero-length copies). The
/// verbatim reproducer's `const () { }` is not valid trust-ir
/// (`ConstTypeMismatch`), and it is refused by that name.
#[test]
fn zero_sized_values_compile_for_linux_and_darwin_o0_through_o3() {
    for (triple, magic) in [
        (LINUX, &b"\x7fELF"[..]),
        (DARWIN, &[0xcf, 0xfa, 0xed, 0xfe][..]),
    ] {
        let parse = |text: &str| {
            let mut module = trust_ir::parser::parse_module(text).expect("the reproducer parses");
            module.target_info.as_mut().unwrap().triple = triple.into();
            module
        };
        assert_eq!(
            compile(&parse(UNIT_REPRODUCER), triple, LEVELS[0]).expect_err("`{ }` is no `()`"),
            "Adapter(TrustIrAdmissionRefused { error: \"function 'unit_params' bb0: const type \
             mismatch: expected (), got aggregate[0]\" })",
            "{triple}"
        );
        let reproducer = parse(&UNIT_REPRODUCER.replace("const () { }", "const () phantomdata"));
        for (name, module) in [
            ("zero-sized", zero_sized_for(triple)),
            ("reproducer", reproducer),
        ] {
            for level in LEVELS {
                let object = compile(&module, triple, level)
                    .unwrap_or_else(|e| panic!("{name} {triple} {level:?}: {e}"));
                assert_eq!(&object[..4], magic, "{name} {triple} {level:?}");
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::{
        LEVELS, LINUX, SHAPES, ZERO_SIZED_INPUTS, ZERO_SIZED_SHAPES, compile, corpus, process,
        zero_sized_for,
    };
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use trust_cg_codegen::pipeline::OptLevel;

    const DRIVER: &str = include_str!("fixtures/aggregate_insert/driver.c");
    const ZERO_SIZED_DRIVER: &str = include_str!("fixtures/aggregate_insert/zero_sized_driver.c");

    fn scratch() -> crate::fresh_dir::ScratchDir {
        crate::fresh_dir::create("trust-cg-aggregate-insert-")
    }

    /// Link `object` against the C oracle and run it; returns stdout and
    /// whether the driver exited successfully.
    fn run_driver(dir: &Path, level: OptLevel, object: &[u8]) -> (String, bool) {
        run_with(dir, level, object, DRIVER)
    }

    fn run_with(dir: &Path, level: OptLevel, object: &[u8], driver: &str) -> (String, bool) {
        let object_path = dir.join(format!("{level:?}.o"));
        let binary = dir.join(format!("driver-{level:?}"));
        fs::write(&object_path, object).unwrap();
        fs::write(dir.join("driver.c"), driver).unwrap();
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .args(["-O2", "-Wall", "-Werror"])
                .arg(dir.join("driver.c"))
                .arg(&object_path)
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{level:?} link files={dir:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        assert!(!run.timed_out, "{level:?} timed out files={dir:?}");
        (
            String::from_utf8_lossy(&run.output.stdout).into_owned(),
            run.output.status.success(),
        )
    }

    #[test]
    fn native_shapes_match_the_c_oracle_bit_exactly_o0_through_o3() {
        let module = corpus();
        let retain = std::env::var_os("TCG_AGGREGATE_INSERT_RETAIN").map(PathBuf::from);
        let total: u32 = SHAPES.iter().map(|(_, checks)| checks).sum();
        for level in LEVELS {
            let object = compile(&module, LINUX, level).unwrap();
            let dir = scratch();
            let (stdout, success) = run_driver(&dir, level, &object);
            if let Some(retain) = &retain {
                fs::create_dir_all(retain).unwrap();
                fs::write(retain.join(format!("{level:?}.o")), &object).unwrap();
                fs::write(retain.join(format!("{level:?}.stdout")), &stdout).unwrap();
                fs::write(retain.join("driver.c"), DRIVER).unwrap();
            }
            let lines: Vec<&str> = stdout.lines().collect();
            for (name, checks) in SHAPES {
                let want = format!("shape {name} checks={checks} failures=0 ok");
                assert!(
                    lines.contains(&want.as_str()),
                    "{level:?}: missing `{want}` files={dir:?}\n{stdout}"
                );
            }
            let summary = format!("aggregate-insert shapes_failed=0 checks={total} failures=0");
            assert_eq!(
                lines.last().copied(),
                Some(summary.as_str()),
                "{level:?} files={dir:?}\n{stdout}"
            );
            assert!(success, "{level:?}: driver failed files={dir:?}\n{stdout}");
            eprintln!("{level:?}: {summary}");
            fs::remove_dir_all(&dir).unwrap();
        }
    }

    /// The zero-sized shapes run at O0-O3 and return the closed-form model's
    /// value for every input.
    #[test]
    fn native_zero_sized_values_run_o0_through_o3() {
        let checks = ZERO_SIZED_SHAPES.len() * ZERO_SIZED_INPUTS.len();
        for level in LEVELS {
            let object = compile(&zero_sized_for(LINUX), LINUX, level).unwrap();
            let dir = scratch();
            let (stdout, success) = run_with(&dir, level, &object, ZERO_SIZED_DRIVER);
            let lines: Vec<&str> = stdout.lines().collect();
            for (name, _) in ZERO_SIZED_SHAPES {
                let want = format!(
                    "shape {name} checks={} failures=0 ok",
                    ZERO_SIZED_INPUTS.len()
                );
                assert!(
                    lines.contains(&want.as_str()),
                    "{level:?}: missing `{want}` files={dir:?}\n{stdout}"
                );
            }
            let summary = format!("zero-sized shapes_failed=0 checks={checks} failures=0");
            assert_eq!(
                lines.last().copied(),
                Some(summary.as_str()),
                "{level:?} files={dir:?}\n{stdout}"
            );
            assert!(success, "{level:?}: driver failed files={dir:?}\n{stdout}");
            eprintln!("{level:?}: {summary}");
            fs::remove_dir_all(&dir).unwrap();
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

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
