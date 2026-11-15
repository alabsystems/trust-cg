//! Bounded machine-IR/native controls for integer-array vectorization.
//! Scalar and vectorized functions share the input builder; the independent C
//! reference uses wrapping unsigned arithmetic. A post-pass counter observes
//! actual vector execution. This is not frontend or whole-transform proof.

#[path = "neon_array_execution/bounds.rs"]
mod bounds;
mod common;
#[path = "common/native_host.rs"]
mod native_host;

use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::regs::{X0, X1, X2, X3, X4, X5};
use trust_cg_ir::{
    AArch64Opcode as Op, BlockId, InstId, MachFunction, MachInst, MachOperand as Operand, RegClass,
    Signature, Type, VReg,
};
use trust_cg_opt::neon_array::NeonArrayPass;
use trust_cg_opt::pass_manager::MachinePass;

fn g(id: u32) -> Operand {
    Operand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn w(id: u32) -> Operand {
    Operand::VReg(VReg::new(id, RegClass::Gpr32))
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

#[derive(Clone, Copy, Debug)]
enum Shape {
    Sum32,
    Sum64,
    Xor64,
    Dot32,
    DotSigned,
    DotUnsigned,
    ByteUnsigned,
    ByteSigned,
    HalfUnsigned,
    HalfSigned,
    Chain32,
    Chain64,
    Abs,
}

const SHAPES: [Shape; 13] = [
    Shape::Sum32,
    Shape::Sum64,
    Shape::Xor64,
    Shape::Dot32,
    Shape::DotSigned,
    Shape::DotUnsigned,
    Shape::ByteUnsigned,
    Shape::ByteSigned,
    Shape::HalfUnsigned,
    Shape::HalfSigned,
    Shape::Chain32,
    Shape::Chain64,
    Shape::Abs,
];

impl Shape {
    fn wide(self) -> bool {
        matches!(
            self,
            Self::Sum64
                | Self::Xor64
                | Self::DotSigned
                | Self::DotUnsigned
                | Self::Chain64
                | Self::Abs
        )
    }

    fn bytes(self) -> i64 {
        match self {
            Self::Sum64 | Self::Xor64 | Self::Chain64 => 8,
            Self::ByteUnsigned | Self::ByteSigned => 1,
            Self::HalfUnsigned | Self::HalfSigned => 2,
            _ => 4,
        }
    }
}

fn reduction(name: &str, shape: Shape, rotation: u8, vectorize: bool) -> MachFunction {
    let rotated = rotation != 0;
    if matches!(shape, Shape::Chain32 | Shape::Chain64 | Shape::Abs) {
        assert!(!rotated);
        return chain(name, shape, vectorize);
    }
    let mut func = MachFunction::new(
        name.into(),
        Signature::new(
            vec![
                Type::Ptr,
                Type::Ptr,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::Ptr,
            ],
            vec![Type::I64],
        ),
    );
    let pre = func.entry;
    let guard = func.try_create_block().unwrap();
    let header = func.try_create_block().unwrap();
    let latch = func.try_create_block().unwrap();
    let exit = func.try_create_block().unwrap();
    let reg = if shape.wide() { g } else { w };
    for (dest, src) in [
        (g(0), X0),
        (g(2), X1),
        (reg(5), X2),
        (reg(1), X3),
        (reg(6), X4),
        (g(90), X5),
    ] {
        emit(&mut func, pre, Op::MovR, vec![dest, Operand::PReg(src)]);
    }
    emit(&mut func, pre, Op::Movz, vec![reg(4), imm(1)]);
    emit(&mut func, pre, Op::Movz, vec![g(40), imm(shape.bytes())]);
    emit(&mut func, pre, Op::B, vec![block(guard)]);
    if rotated {
        emit(&mut func, guard, Op::B, vec![block(header)]);
    } else {
        emit(&mut func, guard, Op::CmpRR, vec![reg(5), reg(1)]);
        emit(&mut func, guard, Op::BCond, vec![imm(11), block(header)]); // LT
        emit(&mut func, guard, Op::B, vec![block(exit)]);
        func.add_edge(guard, exit);
    }
    let index = if shape.wide() {
        g(5)
    } else {
        emit(&mut func, header, Op::Sxtw, vec![g(10), w(5)]);
        g(10)
    };
    if shape.bytes() == 1 {
        emit(
            &mut func,
            header,
            Op::AddRR,
            vec![g(11), g(0), index.clone()],
        );
    } else {
        emit(
            &mut func,
            header,
            Op::Madd,
            vec![g(11), index.clone(), g(40), g(0)],
        );
    }
    let load = match shape.bytes() {
        1 => Op::LdrbRI,
        2 => Op::LdrhRI,
        _ => Op::LdrRI,
    };
    let value = if shape.bytes() == 8 { g(12) } else { w(12) };
    emit(&mut func, header, load, vec![value.clone(), g(11), imm(0)]);
    let extension = match shape {
        Shape::ByteUnsigned => Some(Op::Uxtb),
        Shape::ByteSigned => Some(Op::Sxtb),
        Shape::HalfUnsigned => Some(Op::Uxth),
        Shape::HalfSigned => Some(Op::Sxth),
        _ => None,
    };
    let term = if let Some(op) = extension {
        emit(&mut func, header, op, vec![w(13), value.clone()]);
        w(13)
    } else {
        value
    };
    if matches!(shape, Shape::Dot32 | Shape::DotSigned | Shape::DotUnsigned) {
        emit(&mut func, header, Op::Madd, vec![g(14), index, g(40), g(2)]);
        emit(&mut func, header, Op::LdrRI, vec![w(15), g(14), imm(0)]);
        let (a, b) = if shape.wide() {
            let op = if matches!(shape, Shape::DotSigned) {
                Op::Sxtw
            } else {
                Op::Uxtw
            };
            emit(&mut func, header, op, vec![g(18), w(12)]);
            emit(&mut func, header, op, vec![g(19), w(15)]);
            (g(18), g(19))
        } else {
            (w(12), w(15))
        };
        emit(&mut func, header, Op::Madd, vec![reg(16), a, b, reg(6)]);
    } else {
        let op = if matches!(shape, Shape::Xor64) {
            Op::EorRR
        } else {
            Op::AddRR
        };
        emit(&mut func, header, op, vec![reg(16), reg(6), term]);
    }
    emit(&mut func, header, Op::AddRR, vec![reg(17), reg(5), reg(4)]);
    if rotated {
        emit(&mut func, header, Op::CmpRR, vec![reg(17), reg(1)]);
        emit(
            &mut func,
            header,
            Op::BCond,
            vec![imm(if rotation == 2 { 10 } else { 0 }), block(exit)],
        ); // GE/EQ
        func.add_edge(header, exit);
    }
    emit(&mut func, header, Op::B, vec![block(latch)]);
    emit(&mut func, latch, Op::MovR, vec![reg(5), reg(17)]);
    emit(&mut func, latch, Op::MovR, vec![reg(6), reg(16)]);
    if rotated {
        emit(&mut func, latch, Op::B, vec![block(header)]);
    } else {
        emit(&mut func, latch, Op::CmpRR, vec![reg(5), reg(1)]);
        emit(&mut func, latch, Op::BCond, vec![imm(11), block(header)]);
        func.add_edge(latch, exit);
    }
    let result = reg(if rotated { 16 } else { 6 });
    let op = if shape.wide() { Op::MovR } else { Op::Uxtw };
    emit(&mut func, exit, op, vec![Operand::PReg(X0), result]);
    let ret = emit(&mut func, exit, Op::Ret, vec![]);
    *func.inst_mut(ret) = MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]);
    func.add_edge(pre, guard);
    func.add_edge(guard, header);
    func.add_edge(header, latch);
    func.add_edge(latch, header);
    observe(func, name, pre, exit, ret, vectorize)
}

fn observe(
    mut func: MachFunction,
    name: &str,
    pre: BlockId,
    exit: BlockId,
    ret: InstId,
    vectorize: bool,
) -> MachFunction {
    func.try_sync_vreg_counter().unwrap();
    if vectorize {
        let mut pass = NeonArrayPass::default();
        assert!(pass.run(&mut func), "{name}");
        assert_eq!(pass.fired(), 1);
    }

    // Added after the pass: observe its original vector body, not a scalar tail.
    let bodies: Vec<_> = func
        .block_order
        .iter()
        .copied()
        .filter(|&b| {
            func.block(b)
                .insts
                .iter()
                .any(|&id| func.inst(id).opcode == Op::NeonLdpQPost)
        })
        .collect();
    assert_eq!(bodies.len(), usize::from(vectorize), "{name}");
    let counter = g(func.try_alloc_vreg().unwrap());
    let pre_term = *func.block(pre).insts.last().unwrap();
    insert_before(
        &mut func,
        pre,
        pre_term,
        MachInst::new(Op::Movz, vec![counter.clone(), imm(0)]),
    );
    for body in bodies {
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
        MachInst::new(Op::StrRI, vec![counter, g(90), imm(0)]),
    );
    func
}

fn chain(name: &str, shape: Shape, vectorize: bool) -> MachFunction {
    let mut func = MachFunction::new(
        name.into(),
        Signature::new(
            vec![
                Type::Ptr,
                Type::Ptr,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::Ptr,
            ],
            vec![Type::I64],
        ),
    );
    let pre = func.entry;
    let header = func.try_create_block().unwrap();
    let body = func.try_create_block().unwrap();
    let split = func.try_create_block().unwrap();
    let abs = matches!(shape, Shape::Abs);
    let neg = abs.then(|| func.try_create_block().unwrap());
    let pos = abs.then(|| func.try_create_block().unwrap());
    let latch = func.try_create_block().unwrap();
    let exit = func.try_create_block().unwrap();
    let reg = if shape.wide() { g } else { w };
    for (dest, src) in [
        (g(0), X0),
        (g(5), X2),
        (reg(1), X3),
        (reg(6), X4),
        (g(90), X5),
    ] {
        emit(&mut func, pre, Op::MovR, vec![dest, Operand::PReg(src)]);
    }
    emit(&mut func, pre, Op::Movz, vec![g(40), imm(shape.bytes())]);
    emit(&mut func, pre, Op::Movz, vec![w(50), imm(0)]);
    // CMP registers must share one width (the encoder refuses a mixed pair by
    // name). The narrow chain's W bound is widened explicitly; a W write
    // already zeroes the upper half, so this is the value an X comparison of
    // that register observes and the C reference's unsigned 64-bit bound.
    let bound = if shape.wide() {
        reg(1)
    } else {
        emit(&mut func, pre, Op::Uxtw, vec![g(91), w(1)]);
        g(91)
    };
    emit(&mut func, pre, Op::B, vec![block(header)]);
    emit(&mut func, header, Op::MovR, vec![g(63), g(5)]);
    emit(&mut func, header, Op::CmpRR, vec![g(63), bound]);
    emit(&mut func, header, Op::BCond, vec![imm(3), block(body)]); // LO
    emit(&mut func, header, Op::B, vec![block(exit)]);
    emit(&mut func, body, Op::MovR, vec![g(76), g(5)]);
    emit(&mut func, body, Op::B, vec![block(split)]);
    emit(&mut func, split, Op::Madd, vec![g(66), g(76), g(40), g(0)]);
    let value = if matches!(shape, Shape::Chain64) {
        g(67)
    } else {
        w(67)
    };
    emit(
        &mut func,
        split,
        Op::LdrRI,
        vec![value.clone(), g(66), imm(0)],
    );
    let term = if abs {
        emit(&mut func, split, Op::CmpRI, vec![w(67), imm(0)]);
        emit(
            &mut func,
            split,
            Op::BCond,
            vec![imm(11), block(neg.unwrap())],
        );
        emit(&mut func, split, Op::B, vec![block(pos.unwrap())]);
        emit(
            &mut func,
            neg.unwrap(),
            Op::SubRR,
            vec![w(69), w(50), w(67)],
        );
        emit(&mut func, neg.unwrap(), Op::MovR, vec![w(70), w(69)]);
        emit(&mut func, neg.unwrap(), Op::B, vec![block(latch)]);
        emit(&mut func, pos.unwrap(), Op::MovR, vec![w(70), w(67)]);
        emit(&mut func, pos.unwrap(), Op::B, vec![block(latch)]);
        emit(&mut func, latch, Op::MovR, vec![w(71), w(70)]);
        emit(&mut func, latch, Op::Uxtw, vec![g(72), w(71)]);
        func.add_edge(split, neg.unwrap());
        func.add_edge(split, pos.unwrap());
        func.add_edge(neg.unwrap(), latch);
        func.add_edge(pos.unwrap(), latch);
        g(72)
    } else {
        emit(&mut func, split, Op::B, vec![block(latch)]);
        func.add_edge(split, latch);
        value
    };
    emit(&mut func, latch, Op::AddRR, vec![reg(73), reg(6), term]);
    emit(&mut func, latch, Op::AddRI, vec![g(74), g(5), imm(1)]);
    emit(&mut func, latch, Op::MovR, vec![reg(6), reg(73)]);
    emit(&mut func, latch, Op::MovR, vec![g(5), g(74)]);
    emit(&mut func, latch, Op::B, vec![block(header)]);
    emit(
        &mut func,
        exit,
        if shape.wide() { Op::MovR } else { Op::Uxtw },
        vec![Operand::PReg(X0), reg(6)],
    );
    let ret = emit(&mut func, exit, Op::Ret, vec![]);
    *func.inst_mut(ret) = MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]);
    func.add_edge(pre, header);
    func.add_edge(header, body);
    func.add_edge(header, exit);
    func.add_edge(body, split);
    func.add_edge(latch, header);
    observe(func, name, pre, exit, ret, vectorize)
}

fn object() -> Vec<u8> {
    object_from(functions)
}

#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
fn native_object() -> Vec<u8> {
    native_object_from(functions)
}

fn functions() -> Vec<MachFunction> {
    {
        let mut functions = Vec::new();
        for (kind, shape) in SHAPES.into_iter().enumerate() {
            for rotation in 0..3 {
                if kind >= 10 && rotation != 0 {
                    continue;
                }
                for vectorize in [false, true] {
                    let name = format!("array_{kind}_{rotation}_{}", usize::from(vectorize));
                    functions.push(reduction(&name, shape, rotation, vectorize));
                }
            }
        }
        functions
    }
}

/// The Mach-O object the host-independent structure controls parse.
fn object_from(build: impl FnOnce() -> Vec<MachFunction>) -> Vec<u8> {
    object_for("aarch64-apple-darwin", build)
}

/// The host's own object (ELF on Linux GNU, Mach-O on macOS) for execution.
#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
fn native_object_from(build: impl FnOnce() -> Vec<MachFunction>) -> Vec<u8> {
    let object = object_for(native_host::TRIPLE, build);
    native_host::assert_native_object(&object);
    object
}

fn object_for(triple: &str, build: impl FnOnce() -> Vec<MachFunction>) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC"); // Optional allocation search only.
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            verify: true,
            target_triple: triple.into(),
            ..PipelineConfig::default()
        });
        let mut functions = build();
        for func in &mut functions {
            pipeline
                .prepare_ir_function(func)
                .expect("prepare integer-array IR");
        }
        pipeline
            .compile_module(&functions)
            .expect("integer-array object")
    })
}

/// The Linux GNU native lane's object, checked at object level on every host.
#[test]
fn integer_array_linux_objects_are_elf_aarch64() {
    for object in [
        object_for("aarch64-unknown-linux-gnu", functions),
        object_for("aarch64-unknown-linux-gnu", bounds::bound_functions),
    ] {
        native_host::assert_elf_aarch64_object(&object);
        assert!(!native_host::text_words(&object).is_empty());
    }
}

#[test]
fn integer_array_object_contains_scalar_and_vector_controls() {
    let parsed = MachOParser::parse(&object()).unwrap();
    for kind in 0..SHAPES.len() {
        for rotated in 0..3 {
            if kind >= 10 && rotated != 0 {
                continue;
            }
            for vectorize in 0..2 {
                let name = format!("_array_{kind}_{rotated}_{vectorize}");
                assert!(parsed.symbols.iter().any(|s| s.name == name), "{name}");
            }
        }
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[test]
fn integer_array_native_results_match_reference_and_vector_counts() {
    const CALLER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef uint64_t (*array_fn)(const void *, const void *, long, long, uint64_t, uint64_t *);
#define DECL(K,R,V) extern uint64_t array_##K##_##R##_##V(const void*,const void*,long,long,uint64_t,uint64_t*);
#define SIX(K) DECL(K,0,0) DECL(K,0,1) DECL(K,1,0) DECL(K,1,1) DECL(K,2,0) DECL(K,2,1)
SIX(0) SIX(1) SIX(2) SIX(3) SIX(4) SIX(5) SIX(6) SIX(7) SIX(8) SIX(9)
DECL(10,0,0) DECL(10,0,1) DECL(11,0,0) DECL(11,0,1) DECL(12,0,0) DECL(12,0,1)
#define ROW(K) {{array_##K##_0_0,array_##K##_0_1},{array_##K##_1_0,array_##K##_1_1},{array_##K##_2_0,array_##K##_2_1}}
#define CHAIN(K) {{array_##K##_0_0,array_##K##_0_1},{0,0},{0,0}}
static array_fn functions[13][3][2] = {ROW(0),ROW(1),ROW(2),ROW(3),ROW(4),ROW(5),ROW(6),ROW(7),ROW(8),ROW(9),CHAIN(10),CHAIN(11),CHAIN(12)};
static uint64_t read_value(const unsigned char *p, long i, int bytes) {
    uint64_t v=0; memcpy(&v,p+i*bytes,bytes); return v;
}
int main(void) {
    unsigned char a[4096], b[4096], saved_a[4096], saved_b[4096];
    const long starts[] = {-33,-8,-1,0,1,7,16,32,64,96};
    const long bounds[] = {-1,0,1,7,8,15,16,17,31,32,33,63,64,65,96};
    const uint64_t seeds[] = {0,5,UINT64_MAX,UINT64_C(0x8000000000000000)};
    unsigned cases=0, errors=0;
    int reported[13][3][2]={0};
    for (int pattern=0;pattern<3;++pattern) {
        for (unsigned i=0;i<sizeof a;++i) {
            a[i] = pattern==0 ? (unsigned char)(i*73+131) : pattern==1 ? 255 : (i%4==3 ? 128 : 0);
            b[i] = pattern==0 ? (unsigned char)(i*19+7) : pattern==1 ? 255 : (i%4==3 ? 127 : 255);
        }
        memcpy(saved_a,a,sizeof a); memcpy(saved_b,b,sizeof b);
        for (int kind=0;kind<13;++kind) for (int rotated=0;rotated<3;++rotated)
        for (int vector=0;vector<2;++vector)
        for (unsigned si=0;si<sizeof starts/sizeof *starts;++si)
        for (unsigned ni=0;ni<sizeof bounds/sizeof *bounds;++ni)
        for (unsigned seed=0;seed<sizeof seeds/sizeof *seeds;++seed) {
            long start=starts[si], bound=bounds[ni];
            if (kind>=10 && rotated) continue;
            if (kind>=10 && bound<0) continue; // Avoid huge unsigned nonempty ranges.
            if (rotated==1 && start>=bound) continue; // Equality-tested finite range only.
            int wide=kind==1 || kind==2 || kind==4 || kind==5 || kind==11 || kind==12;
            int bytes=kind==1 || kind==2 || kind==11 ? 8 : kind==6 || kind==7 ? 1 : kind==8 || kind==9 ? 2 : 4;
            int width=kind==1 || kind==2 || kind==11 ? 8 : kind==4 || kind==5 ? 32 : 64/bytes;
            const unsigned char *x=a+1024, *y=b+1024;
            uint64_t expected=wide ? seeds[seed] : (uint32_t)seeds[seed];
            for (long i=start;kind>=10 ? (uint64_t)i<(uint64_t)bound : i<bound || (rotated==2 && i==start);++i) {
                uint64_t v=read_value(x,i,bytes), q=read_value(y,i,bytes);
                if (kind==3) v=(uint32_t)((uint32_t)v*(uint32_t)q);
                if (kind==4) v=(uint64_t)(int64_t)(int32_t)v*(uint64_t)(int64_t)(int32_t)q;
                if (kind==5) v=(uint64_t)(uint32_t)v*(uint32_t)q;
                if (kind==7) v=(uint32_t)(int32_t)(int8_t)v;
                if (kind==9) v=(uint32_t)(int32_t)(int16_t)v;
                if (kind==12) v=(int32_t)v<0 ? (uint32_t)(0-(uint32_t)v) : (uint32_t)v;
                expected=kind==2 ? expected^v : expected+v;
                if (!wide) expected=(uint32_t)expected;
            }
            uint64_t count=UINT64_MAX;
            uint64_t got=functions[kind][rotated][vector](x,y,start,bound,seeds[seed],&count);
            long trips=(kind>=10 && start<0) ? 0 : bound>start ? bound-start : 0;
            if (rotated==2 && !trips) trips=1;
            uint64_t expected_count=vector && (!wide || (bound>=width && (kind<10 || start>=0))) ? trips/width : 0;
            if (got!=expected || count!=expected_count || memcmp(a,saved_a,sizeof a) || memcmp(b,saved_b,sizeof b)) {
                if (!reported[kind][rotated][vector]++) fprintf(stderr,"pattern=%d kind=%d rotated=%d vector=%d start=%ld bound=%ld seed=%llu got=%016llx expected=%016llx vectors=%llu expected_vectors=%llu\n",
                    pattern,kind,rotated,vector,start,bound,(unsigned long long)seeds[seed],(unsigned long long)got,(unsigned long long)expected,(unsigned long long)count,(unsigned long long)expected_count);
                ++errors;
            }
            ++cases;
        }
        for (unsigned seed=0;seed<sizeof seeds/sizeof *seeds;++seed) {
            uint64_t count=UINT64_MAX;
            uint64_t got=array_10_0_1(a+1024,b+1024,INT64_C(0x100000000),33,seeds[seed],&count);
            if (got!=(uint32_t)seeds[seed] || count!=0) {
                if (!reported[10][1][1]++) fprintf(stderr,"mixed-width chain high start: got=%llx expected=%x count=%llu\n",(unsigned long long)got,(unsigned)seeds[seed],(unsigned long long)count);
                ++errors;
            }
            ++cases;
        }
    }
    printf("INTEGER_ARRAY_NATIVE_CASES=%u\n",cases);
    return errors ? 1 : cases ? 0 : 2;
}
"#;
    execute_object(
        native_object(),
        CALLER,
        "INTEGER_ARRAY_NATIVE_CASES=104892\n",
    );
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn execute_object(bytes: Vec<u8>, source: &str, expected: &str) {
    use std::process::Command;
    use std::time::Duration;

    let directory = tempfile::Builder::new()
        .prefix("trust-cg-array-")
        .tempdir()
        .unwrap();
    let caller = directory.path().join("caller.c");
    let body = directory.path().join("array.o");
    let executable = directory.path().join("array-control");
    std::fs::write(&caller, source).unwrap();
    std::fs::write(&body, bytes).unwrap();
    let mut command = Command::new(native_host::C_COMPILER);
    command
        .arg("-O0")
        .arg(&caller)
        .arg(&body)
        .arg("-o")
        .arg(&executable);
    let linked =
        common::rosetta::command_output_with_timeout(&mut command, Duration::from_secs(30))
            .unwrap();
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
    assert_eq!(stdout, expected);
    print!("{stdout}");
}
