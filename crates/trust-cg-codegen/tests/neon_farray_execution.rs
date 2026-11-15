//! Bounded emitted-machine controls for FP-array vectorization.
//! The test-only counter observes vector-body iterations after the pass runs.
//! This exercises real allocation/frame lowering/encoding, not a frontend or
//! whole-transform equivalence proof. Native execution runs on AArch64 macOS
//! (Mach-O) and Linux GNU (ELF).

mod common;
#[path = "common/native_host.rs"]
mod native_host;

use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::regs::{X0, X1, X2, X3};
use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, InstId, MachFunction, MachInst, MachOperand as Operand, RegClass,
    Signature, Type, VReg,
};
use trust_cg_opt::neon_farray::NeonFArrayPass;
use trust_cg_opt::pass_manager::MachinePass;

fn g(id: u32) -> Operand {
    Operand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn w(id: u32) -> Operand {
    Operand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn s(id: u32) -> Operand {
    Operand::VReg(VReg::new(id, RegClass::Fpr32))
}
fn imm(value: i64) -> Operand {
    Operand::Imm(value)
}
fn block(id: BlockId) -> Operand {
    Operand::Block(id)
}

fn emit(func: &mut MachFunction, at: BlockId, opcode: Op, operands: Vec<Operand>) -> InstId {
    let id = func.try_push_inst(MachInst::new(opcode, operands)).unwrap();
    func.append_inst(at, id);
    id
}

fn insert_before(func: &mut MachFunction, at: BlockId, before: InstId, inst: MachInst) {
    let id = func.try_push_inst(inst).unwrap();
    let body = &mut func.block_mut(at).insts;
    let pos = body.iter().position(|&id| id == before).unwrap();
    body.insert(pos, id);
}

#[derive(Clone, Copy)]
enum Shape {
    TwoStreams,
    Negation,
    RepeatedBase,
    ScalarControl,
}

fn fill(name: &str, shape: Shape) -> MachFunction {
    let mut func = MachFunction::new(
        name.into(),
        Signature::new(
            vec![Type::Ptr, Type::Ptr, Type::I64, Type::I64],
            vec![Type::I64],
        ),
    );
    let pre = func.entry;
    let header = func.try_create_block().unwrap();
    let latch = func.try_create_block().unwrap();
    let exit = func.try_create_block().unwrap();
    for (dest, src) in [(g(1), X0), (g(2), X1), (g(10), X2), (g(13), X3)] {
        emit(&mut func, pre, Op::MovR, vec![dest, Operand::PReg(src)]);
    }
    emit(&mut func, pre, Op::Movz, vec![g(3), imm(4)]);
    for (bits, integer, float) in [(0x3f80, 60, 4), (0x4000, 61, 5)] {
        emit(&mut func, pre, Op::Movz, vec![w(integer), imm(0)]);
        emit(
            &mut func,
            pre,
            Op::Movk,
            vec![w(integer), imm(bits), imm(16)],
        );
        emit(&mut func, pre, Op::FmovGprFpr, vec![s(float), w(integer)]);
    }
    emit(&mut func, pre, Op::B, vec![block(header)]);

    emit(&mut func, header, Op::MovR, vec![w(6), g(10)]);
    emit(&mut func, header, Op::ScvtfRR, vec![s(7), w(6)]);
    if matches!(shape, Shape::Negation) {
        emit(&mut func, header, Op::FnegRR, vec![s(8), s(7)]);
    } else {
        emit(&mut func, header, Op::FaddRR, vec![s(8), s(4), s(7)]);
    }
    emit(&mut func, header, Op::Madd, vec![g(20), g(10), g(3), g(1)]);
    emit(&mut func, header, Op::StrRI, vec![s(8), g(20), imm(0)]);
    if !matches!(shape, Shape::Negation) {
        emit(&mut func, header, Op::FaddRR, vec![s(9), s(5), s(7)]);
        let base = if matches!(shape, Shape::RepeatedBase) {
            g(1)
        } else {
            g(2)
        };
        emit(&mut func, header, Op::Madd, vec![g(24), g(10), g(3), base]);
        emit(&mut func, header, Op::StrRI, vec![s(9), g(24), imm(0)]);
    }
    emit(&mut func, header, Op::AddRI, vec![g(12), g(10), imm(1)]);
    emit(&mut func, header, Op::CmpRR, vec![g(12), g(13)]);
    emit(&mut func, header, Op::BCond, vec![imm(0), block(exit)]); // EQ
    emit(&mut func, header, Op::B, vec![block(latch)]);
    emit(&mut func, latch, Op::MovR, vec![g(10), g(12)]);
    emit(&mut func, latch, Op::B, vec![block(header)]);
    let ret = emit(&mut func, exit, Op::Ret, vec![]);
    func.add_edge(pre, header);
    func.add_edge(header, latch);
    func.add_edge(header, exit);
    func.add_edge(latch, header);
    func.try_sync_vreg_counter().unwrap();

    if !matches!(shape, Shape::ScalarControl) {
        let before = format!("{func:?}");
        let mut pass = NeonFArrayPass::default();
        let expected = matches!(shape, Shape::TwoStreams);
        assert_eq!(pass.run(&mut func), expected, "{name}");
        assert_eq!(pass.fired(), usize::from(expected));
        if !expected {
            assert_eq!(before, format!("{func:?}"));
        }
    }
    let vector_bodies: Vec<_> = func
        .block_order
        .iter()
        .copied()
        .filter(|&id| {
            func.block(id)
                .insts
                .iter()
                .any(|&id| func.inst(id).opcode == Op::NeonStpQPost)
        })
        .collect();
    assert_eq!(
        vector_bodies.len(),
        usize::from(matches!(shape, Shape::TwoStreams))
    );

    // Observe real vector execution without altering its guards or memory ops.
    // This instrumentation is added only after recognition/rewriting.
    let counter = g(func.try_alloc_vreg().unwrap());
    let pre_term = *func.block(pre).insts.last().unwrap();
    insert_before(
        &mut func,
        pre,
        pre_term,
        MachInst::new(Op::Movz, vec![counter.clone(), imm(0)]),
    );
    for body in vector_bodies {
        let term = *func.block(body).insts.last().unwrap();
        insert_before(
            &mut func,
            body,
            term,
            MachInst::new(Op::AddRI, vec![counter.clone(), counter.clone(), imm(1)]),
        );
    }
    insert_before(
        &mut func,
        exit,
        ret,
        MachInst::new(Op::MovR, vec![Operand::PReg(X0), counter]),
    );
    *func.inst_mut(ret) = MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]);
    func
}

/// The Mach-O object the host-independent structure control parses.
fn object() -> Vec<u8> {
    object_for("aarch64-apple-darwin")
}

/// The host's own object (ELF on Linux GNU, Mach-O on macOS) for execution.
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
fn native_object() -> Vec<u8> {
    let object = object_for(native_host::TRIPLE);
    native_host::assert_native_object(&object);
    object
}

fn object_for(triple: &str) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        // Optional allocation-quality search only; mandatory checks stay on.
        env.remove("TCG_AY_REGALLOC");
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            verify: true,
            target_triple: triple.into(),
            ..PipelineConfig::default()
        });
        let mut functions = vec![
            fill("fill_vector", Shape::TwoStreams),
            fill("fill_negation", Shape::Negation),
            fill("fill_repeated", Shape::RepeatedBase),
            fill("fill_scalar", Shape::ScalarControl),
        ];
        for function in &mut functions {
            pipeline
                .prepare_ir_function(function)
                .expect("prepare FP-array machine function");
        }
        pipeline
            .compile_module(&functions)
            .expect("encode FP-array object")
    })
}

/// The Linux GNU native lane's object, checked at object level on every host.
#[test]
fn fp_array_linux_object_is_elf_aarch64() {
    let object = object_for("aarch64-unknown-linux-gnu");
    native_host::assert_elf_aarch64_object(&object);
    assert!(!native_host::text_words(&object).is_empty());
}

#[test]
fn fp_array_object_contains_vector_and_scalar_controls() {
    let parsed = MachOParser::parse(&object()).unwrap();
    for name in [
        "_fill_vector",
        "_fill_negation",
        "_fill_repeated",
        "_fill_scalar",
    ] {
        assert!(
            parsed.symbols.iter().any(|symbol| symbol.name == name),
            "{name}"
        );
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn fp_array_native_fills_match_scalar_memory_and_observed_vector_counts() {
    use std::process::Command;
    use std::time::Duration;

    const CALLER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef long (*fill_fn)(float *, float *, long, long);
extern long fill_vector(float *, float *, long, long);
extern long fill_negation(float *, float *, long, long);
extern long fill_repeated(float *, float *, long, long);
extern long fill_scalar(float *, float *, long, long);

static int check(fill_fn fill, int kind, long start, long bound, long delta) {
    float actual[256], expected[256];
    for (int i = 0; i < 256; ++i) actual[i] = expected[i] = 1000.0f + i;
    float *x = expected + 96, *y = x + delta;
    for (long j = start; j < bound; ++j) {
        if (kind == 1) x[j] = -(float)j;
        else {
            x[j] = 1.0f + (float)j;
            if (kind == 2) x[j] = 2.0f + (float)j;
            else y[j] = 2.0f + (float)j;
        }
    }
    long count = fill(actual + 96, actual + 96 + delta, start, bound);
    int disjoint = bound <= delta + start || delta + bound <= start;
    long expected_count = kind == 0 && bound >= 8 && disjoint ? (bound - start) / 8 : 0;
    if (count != expected_count || memcmp(actual, expected, sizeof actual) != 0) {
        fprintf(stderr, "kind=%d start=%ld bound=%ld delta=%ld count=%ld expected=%ld\n",
                kind, start, bound, delta, count, expected_count);
        for (int i = 0; i < 256; ++i) {
            uint32_t a, b; memcpy(&a, &actual[i], 4); memcpy(&b, &expected[i], 4);
            if (a != b) { fprintf(stderr, "lane=%d actual=%08x expected=%08x\n", i, a, b); break; }
        }
        return 1;
    }
    return 0;
}
int main(void) {
    const long starts[] = {-8, -1, 0, 4};
    const long bounds[] = {1, 7, 8, 12, 17};
    fill_fn functions[] = {fill_vector, fill_negation, fill_repeated, fill_scalar};
    unsigned cases = 0;
    for (int kind = 0; kind < 4; ++kind)
        for (unsigned i = 0; i < sizeof starts / sizeof *starts; ++i)
            for (unsigned n = 0; n < sizeof bounds / sizeof *bounds; ++n) {
                if (starts[i] >= bounds[n]) continue;
                for (long delta = -20; delta <= 20; ++delta) {
                    if (check(functions[kind], kind, starts[i], bounds[n], delta)) return 1;
                    ++cases;
                }
            }
    if (cases != 3116) return 2;
    printf("FP_ARRAY_NATIVE_CASES=%u\n", cases);
    return 0;
}
"#;
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-farray-")
        .tempdir()
        .unwrap();
    let caller = directory.path().join("caller.c");
    let body = directory.path().join("array.o");
    let executable = directory.path().join("array-control");
    std::fs::write(&caller, CALLER).unwrap();
    std::fs::write(&body, native_object()).unwrap();
    let mut command = Command::new(native_host::C_COMPILER);
    command
        .args(["-O0", "-ffp-contract=off"])
        .arg(&caller)
        .arg(&body)
        .arg("-o")
        .arg(&executable);
    let linked =
        common::rosetta::command_output_with_timeout(&mut command, Duration::from_secs(30))
            .expect("native control requires the platform C linker");
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{:?}",
        linked.output
    );
    let result = common::rosetta::run_executable_with_timeout(
        &executable,
        common::rosetta::exec_timeout(Duration::from_secs(5)),
    )
    .unwrap();
    assert!(
        !result.timed_out && result.output.status.success(),
        "{:?}",
        result.output
    );
    let stdout = String::from_utf8(result.output.stdout).unwrap();
    assert_eq!(stdout, "FP_ARRAY_NATIVE_CASES=3116\n");
    print!("{stdout}");
}
