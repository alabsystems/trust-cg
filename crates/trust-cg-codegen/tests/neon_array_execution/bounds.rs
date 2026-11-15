//! Mixed-width bounds are values, not aliases of their widening sources.

use super::*;

// Sxtw, Uxtw, reassigned Sxtw source, raw X argument, W bound in an X
// comparison, two i64 sums with extended bounds, W comparison of an X
// argument, and byte/halfword widening reductions with extended bounds.
// CMP registers must share one width (the encoder refuses a mixed pair by
// name), so each mixed-width comparison spells the conversion the machine
// comparison performs at the induction variable's width: a W bound in an X
// comparison is zero-extended (a W write zeroes the upper half), and an X
// bound in a W comparison is compared through its low 32 bits.
const KINDS: usize = 10;

fn reduction_with_bound(name: &str, kind: usize, rotation: u8, vectorize: bool) -> MachFunction {
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
    let acc = if matches!(kind, 5 | 6) { g } else { w };
    let iv = if kind >= 7 { w } else { g };
    let input = if matches!(kind, 3 | 7) { g } else { w };
    let bytes = match kind {
        5 | 6 => 8,
        8 => 1,
        9 => 2,
        _ => 4,
    };
    for (dest, src) in [
        (g(0), X0),
        (iv(5), X2),
        (input(1), X3),
        (acc(6), X4),
        (g(90), X5),
    ] {
        emit(&mut func, pre, Op::MovR, vec![dest, Operand::PReg(src)]);
    }
    let bound = if matches!(kind, 3 | 4 | 7) {
        input(1)
    } else {
        emit(
            &mut func,
            pre,
            if matches!(kind, 1 | 6 | 9) {
                Op::Uxtw
            } else {
                Op::Sxtw
            },
            vec![g(41), w(1)],
        );
        g(41)
    };
    let bound = match (kind >= 7, kind == 4) {
        // X induction variable, W bound: the comparison saw it zero-extended.
        (false, true) => {
            emit(&mut func, pre, Op::Uxtw, vec![g(42), bound]);
            g(42)
        }
        // W induction variable, X bound: the comparison read its low half.
        (true, _) => {
            emit(&mut func, pre, Op::MovR, vec![w(42), bound]);
            w(42)
        }
        (false, false) => bound,
    };
    if kind == 2 {
        // The captured X value still holds the original limit. This W source
        // is mutable machine IR, not an interchangeable name for that value.
        emit(&mut func, pre, Op::Movz, vec![w(1), imm(32)]);
    }
    emit(&mut func, pre, Op::Movz, vec![iv(4), imm(1)]);
    emit(&mut func, pre, Op::Movz, vec![g(40), imm(bytes)]);
    emit(&mut func, pre, Op::B, vec![block(guard)]);
    if rotation == 0 {
        emit(&mut func, guard, Op::CmpRR, vec![iv(5), bound.clone()]);
        emit(&mut func, guard, Op::BCond, vec![imm(11), block(header)]);
        emit(&mut func, guard, Op::B, vec![block(exit)]);
        func.add_edge(guard, exit);
    } else {
        emit(&mut func, guard, Op::B, vec![block(header)]);
    }
    let index = if kind >= 7 {
        emit(&mut func, header, Op::Sxtw, vec![g(10), w(5)]);
        g(10)
    } else {
        g(5)
    };
    if bytes == 1 {
        emit(&mut func, header, Op::AddRR, vec![g(11), g(0), index]);
    } else {
        emit(&mut func, header, Op::Madd, vec![g(11), index, g(40), g(0)]);
    }
    emit(
        &mut func,
        header,
        match bytes {
            1 => Op::LdrbRI,
            2 => Op::LdrhRI,
            _ => Op::LdrRI,
        },
        vec![acc(12), g(11), imm(0)],
    );
    let term = if bytes < 4 {
        emit(
            &mut func,
            header,
            if bytes == 1 { Op::Uxtb } else { Op::Uxth },
            vec![w(13), w(12)],
        );
        w(13)
    } else {
        acc(12)
    };
    emit(&mut func, header, Op::AddRR, vec![acc(16), acc(6), term]);
    emit(&mut func, header, Op::AddRR, vec![iv(17), iv(5), iv(4)]);
    if rotation != 0 {
        emit(&mut func, header, Op::CmpRR, vec![iv(17), bound.clone()]);
        emit(
            &mut func,
            header,
            Op::BCond,
            vec![imm(if rotation == 2 { 10 } else { 0 }), block(exit)],
        );
        func.add_edge(header, exit);
    }
    emit(&mut func, header, Op::B, vec![block(latch)]);
    emit(&mut func, latch, Op::MovR, vec![iv(5), iv(17)]);
    emit(&mut func, latch, Op::MovR, vec![acc(6), acc(16)]);
    if rotation == 0 {
        emit(&mut func, latch, Op::CmpRR, vec![iv(5), bound]);
        emit(&mut func, latch, Op::BCond, vec![imm(11), block(header)]);
        func.add_edge(latch, exit);
    } else {
        emit(&mut func, latch, Op::B, vec![block(header)]);
    }
    emit(
        &mut func,
        exit,
        if bytes == 8 { Op::MovR } else { Op::Uxtw },
        vec![Operand::PReg(X0), acc(if rotation == 0 { 6 } else { 16 })],
    );
    let ret = emit(&mut func, exit, Op::Ret, vec![]);
    *func.inst_mut(ret) = MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]);
    for (a, b) in [
        (pre, guard),
        (guard, header),
        (header, latch),
        (latch, header),
    ] {
        func.add_edge(a, b);
    }
    observe(func, name, pre, exit, ret, vectorize)
}

fn bounds_object() -> Vec<u8> {
    object_from(bound_functions)
}

#[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
fn native_bounds_object() -> Vec<u8> {
    native_object_from(bound_functions)
}

pub(super) fn bound_functions() -> Vec<MachFunction> {
    {
        let mut functions = Vec::new();
        for kind in 0..KINDS {
            for rotation in 0..3 {
                for vectorize in [false, true] {
                    let name = format!("bound_{kind}_{rotation}_{}", usize::from(vectorize));
                    functions.push(reduction_with_bound(&name, kind, rotation, vectorize));
                }
            }
        }
        functions
    }
}

#[test]
fn bound_object_contains_scalar_and_vector_controls() {
    let parsed = MachOParser::parse(&bounds_object()).unwrap();
    for kind in 0..KINDS {
        for rotation in 0..3 {
            for vector in 0..2 {
                let name = format!("_bound_{kind}_{rotation}_{vector}");
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
fn native_bounds_preserve_captured_value_and_projection_domain() {
    const CALLER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef uint64_t (*array_fn)(const void*,const void*,long,long,uint64_t,uint64_t*);
#define DECL(K,R,V) extern uint64_t bound_##K##_##R##_##V(const void*,const void*,long,long,uint64_t,uint64_t*);
#define SIX(K) DECL(K,0,0) DECL(K,0,1) DECL(K,1,0) DECL(K,1,1) DECL(K,2,0) DECL(K,2,1)
SIX(0) SIX(1) SIX(2) SIX(3) SIX(4) SIX(5) SIX(6) SIX(7) SIX(8) SIX(9)
#define ROW(K) {{bound_##K##_0_0,bound_##K##_0_1},{bound_##K##_1_0,bound_##K##_1_1},{bound_##K##_2_0,bound_##K##_2_1}}
static array_fn functions[10][3][2]={ROW(0),ROW(1),ROW(2),ROW(3),ROW(4),ROW(5),ROW(6),ROW(7),ROW(8),ROW(9)};
int main(void) {
    unsigned char values[1024], saved[1024];
    const long starts[]={-2147483664L,-2147483648L,-33,-1,0,1,16,32,2147483615L,2147483647L,2147483648L,4294967263L,4294967295L,4294967296L};
    const long inputs[]={-4294967328L,-4294967264L,-2147483664L,-2147483648L,-2147483632L,-1,0,1,8,16,24,32,33,48,63,64,65,80,96,2147483647L,2147483648L,2147483680L,4294967295L,4294967296L,4294967328L};
    const uint64_t seeds[]={0,5,UINT64_MAX};
    unsigned cases=0, errors=0;
    int reported[10][3][2]={0};
    unsigned vector_calls[10][3]={0};
    for (unsigned p=0;p<2;++p) {
        for (unsigned i=0;i<sizeof values;++i) values[i]=p ? 255 : i*73+17;
        memcpy(saved,values,sizeof values);
        for (int k=0;k<10;++k) for (int r=0;r<3;++r) for (int v=0;v<2;++v)
        for (unsigned si=0;si<sizeof starts/sizeof *starts;++si)
        for (unsigned ni=0;ni<sizeof inputs/sizeof *inputs;++ni)
        for (unsigned s=0;s<sizeof seeds/sizeof *seeds;++s) {
            long start=starts[si], input=inputs[ni];
            long bound=k==3 ? input : k==1 || k==4 || k==6 ? (long)(uint32_t)input : (long)(int32_t)input;
            int wide=k==5 || k==6;
            int bytes=wide ? 8 : k==8 ? 1 : k==9 ? 2 : 4;
            int width=64/bytes;
            if (k==2 && start!=0 && start!=16 && start!=32) continue;
            if (k>=7 && (start<INT32_MIN || start>=INT32_MAX)) continue;
            if (r==1 && start>=bound) continue; // Only finite increasing EQ loops.
            if (bound>start && bound-start>64) continue;
            long trips=bound>start ? bound-start : r==2 ? 1 : 0;
            uint64_t expected=wide ? seeds[s] : (uint32_t)seeds[s];
            for (long i=0;i<trips;++i) {
                uint64_t value=0; memcpy(&value,values+128+i*bytes,bytes);
                expected+=value;
                if (!wide) expected=(uint32_t)expected;
            }
            // Integer address arithmetic intentionally models machine-IR Madd
            // wrapping. Every effective load is within values; the C reference
            // never performs out-of-object pointer arithmetic at a logical index.
            uintptr_t base=(uintptr_t)(values+128)-(uint64_t)start*bytes;
            uint64_t count=UINT64_MAX;
            uint64_t got=functions[k][r][v]((void*)base,0,start,input,seeds[s],&count);
            if (v && count) ++vector_calls[k][r];
            int domain=wide ? bound>=width : start>=INT32_MIN && start<=INT32_MAX && bound>=INT32_MIN && bound<=INT32_MAX;
            uint64_t expected_count=v && domain && start<bound ? trips/width : 0;
            if (got!=expected || count!=expected_count || memcmp(values,saved,sizeof values)) {
                if (!reported[k][r][v]++) fprintf(stderr,"kind=%d rotation=%d vector=%d start=%ld input=%ld bound=%ld got=%llx expected=%llx vectors=%llu expected_vectors=%llu\n",k,r,v,start,input,bound,(unsigned long long)got,(unsigned long long)expected,(unsigned long long)count,(unsigned long long)expected_count);
                ++errors;
            }
            ++cases;
        }
    }
    for (int k=0;k<10;++k) for (int r=0;r<3;++r) {
        if (!vector_calls[k][r]) { fprintf(stderr,"no vector execution: kind=%d rotation=%d\n",k,r); ++errors; }
    }
    printf("INTEGER_ARRAY_BOUND_CASES=%u\n",cases);
    return errors ? 1 : cases ? 0 : 2;
}
"#;
    execute_object(
        native_bounds_object(),
        CALLER,
        "INTEGER_ARRAY_BOUND_CASES=54384\n",
    );
}
