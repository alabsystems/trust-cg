// Copyright 2026 Andrew Yates | Apache-2.0
//! Native integer short-vector carrier ABI and unsigned constant regression.
//! Operation support is pinned separately: `trust-cg-lower`'s
//! `vector_type_admission` (the exact partition, L04-P6) and
//! `e2e_aarch64_neon_admission` (the admitted unsigned-lane operations against
//! NEON intrinsics); vector conversions stay refused.

// The native helpers are only CALLED under the native-host cfg below; on any other
// host they are dead code, and the workspace denies warnings.
#[allow(dead_code)]
#[path = "common/aarch64_native.rs"]
mod native;
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_ir::{
    Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

fn function(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    result: Option<Ty>,
    body: Vec<InstrNode>,
) -> FuncId {
    let signature = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: result.into_iter().collect(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, signature, BlockId::new(0));
    if body.is_empty() {
        function.linkage = Linkage::External;
    } else {
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: params
                .into_iter()
                .enumerate()
                .map(|(i, ty)| (ValueId::new(i as u32), ty))
                .collect(),
            body,
        }];
    }
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

fn corpus(lane: Ty, bits: u32, bytes: u64) -> (Module, String) {
    let unsigned = matches!(lane, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64);
    let lanes = bytes as u32 * 8 / bits;
    let ty = Ty::Vector(Box::new(lane), lanes);
    let mut module = Module::new("integer_short_vector_types");
    let load = |ptr, result| {
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: ValueId::new(ptr),
            volatile: true,
            align: Some(bytes),
        })
        .with_result(ValueId::new(result))
    };
    let store = |ptr, value| {
        InstrNode::new(Inst::Store {
            ty: ty.clone(),
            ptr: ValueId::new(ptr),
            value: ValueId::new(value),
            volatile: true,
            align: Some(bytes),
        })
    };
    let ret = || InstrNode::new(Inst::Return { values: vec![] });
    function(
        &mut module,
        "cg_copy",
        vec![Ty::Ptr, Ty::Ptr],
        None,
        vec![
            load(0, 2),
            InstrNode::new(Inst::Copy {
                ty: ty.clone(),
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            store(1, 3),
            ret(),
        ],
    );
    function(
        &mut module,
        "cg_identity",
        vec![ty.clone()],
        Some(ty.clone()),
        vec![
            InstrNode::new(Inst::Copy {
                ty: ty.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
    let callee = function(
        &mut module,
        "c_identity",
        vec![ty.clone()],
        Some(ty.clone()),
        vec![],
    );
    function(
        &mut module,
        "cg_call",
        vec![Ty::Ptr, Ty::Ptr],
        None,
        vec![
            load(0, 2),
            InstrNode::new(Inst::Call {
                callee,
                args: vec![ValueId::new(2)],
            })
            .with_result(ValueId::new(3)),
            store(1, 3),
            ret(),
        ],
    );

    // New unsigned V128 constants use the generic scalar-lane materializer.
    // Include max, sign bit, zero, and a near-max value in every lane position.
    let max = u64::MAX >> (64 - bits);
    let patterns = [0, max, 1u64 << (bits - 1), max - 7];
    let constants = unsigned && bytes == 16;
    if constants {
        for pattern in 0..4 {
            let values = (0..lanes)
                .map(|lane| Constant::Int(i128::from(patterns[(lane as usize + pattern) % 4])))
                .collect();
            function(
                &mut module,
                &format!("cg_constant_{pattern}"),
                vec![Ty::Ptr],
                None,
                vec![
                    InstrNode::new(Inst::Const {
                        ty: ty.clone(),
                        value: Constant::Vector(values),
                    })
                    .with_result(ValueId::new(1)),
                    store(0, 1),
                    ret(),
                ],
            );
        }
    }
    let constant_declarations = if constants {
        (0..4)
            .map(|p| format!("extern void cg_constant_{p}(V*);\n"))
            .collect::<String>()
    } else {
        String::new()
    };
    let constant_checks = if constants {
        (0..4).map(|p|format!(r#"
    memset(&actual,0x3c,sizeof(actual));
    for(unsigned lane=0;lane<{lanes};lane++) {{ uint64_t value=patterns[(lane+{p})%4]; memcpy((unsigned char*)&expected+lane*{lane_bytes},&value,{lane_bytes}); }}
    cg_constant_{p}(&actual.value);
    if(check(&actual,&expected,"constant",{p})) return 4;
"#,lane_bytes=bits/8)).collect::<String>()
    } else {
        String::new()
    };
    let c = format!(
        r#"#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef {sign}int{bits}_t V __attribute__((vector_size({bytes})));
_Static_assert(sizeof(V)=={bytes} && _Alignof(V)=={bytes},"native vector layout");
struct output {{ V value; unsigned char canary[16]; }};
__attribute__((noinline)) V c_identity(V a) {{ __asm__ volatile("" : "+w"(a)); return a; }}
extern V cg_identity(V);
extern void cg_copy(const V*,V*);
extern void cg_call(const V*,V*);
{constant_declarations}
static int check(const struct output*actual,const V*expected,const char*mode,int seed) {{
    if(memcmp(&actual->value,expected,sizeof(V))) {{
        const unsigned char*a=(const unsigned char*)&actual->value,*e=(const unsigned char*)expected;
        for(unsigned i=0;i<sizeof(V);i++) if(a[i]!=e[i]) {{ printf("FAIL %s seed=%d byte=%u expected=%02x actual=%02x\n",mode,seed,i,e[i],a[i]);break; }}
        return 1;
    }}
    for(unsigned i=0;i<sizeof(actual->canary);i++) if(actual->canary[i]!=0x3c) {{printf("FAIL output overrun %s byte=%u\n",mode,i);return 1;}}
    return 0;
}}
int main(void) {{
    V input,expected;
    struct output actual;
    for(int seed=0;seed<4;seed++) {{
        for(unsigned i=0;i<sizeof(V);i++) ((unsigned char*)&input)[i]=(unsigned char)(0x81+i*37+seed*17);
        expected=c_identity(input);
        if(memcmp(&input,&expected,sizeof(V))) return 90;
        memset(&actual,0x3c,sizeof(actual));actual.value=cg_identity(input);if(check(&actual,&expected,"identity",seed))return 1;
        memset(&actual,0x3c,sizeof(actual));cg_copy(&input,&actual.value);if(check(&actual,&expected,"copy",seed))return 2;
        memset(&actual,0x3c,sizeof(actual));cg_call(&input,&actual.value);if(check(&actual,&expected,"call",seed))return 3;
    }}
    uint64_t patterns[4]={{0,UINT64_C({max}),UINT64_C({high}),UINT64_C({near_max})}};
    (void)patterns;
    {constant_checks}
    return 0;
}}
"#,
        sign = if unsigned { "u" } else { "" },
        high = patterns[2],
        near_max = patterns[3]
    );
    (module, c)
}

fn lanes() -> [(Ty, u32); 8] {
    [
        (Ty::I8, 8),
        (Ty::U8, 8),
        (Ty::I16, 16),
        (Ty::U16, 16),
        (Ty::I32, 32),
        (Ty::U32, 32),
        (Ty::I64, 64),
        (Ty::U64, 64),
    ]
}

#[test]
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn native_integer_vector_carriers_and_unsigned_constants_o0_through_o3() {
    let mut checks = 0;
    for (lane, bits) in lanes() {
        for bytes in [8, 16] {
            let (module, driver) = corpus(lane.clone(), bits, bytes);
            for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let object = native::compile(&module, opt);
                assert_eq!(
                    native::link_run(
                        &format!("{lane:?}x{} {opt:?}", bytes * 8 / u64::from(bits)),
                        &object,
                        &driver
                    ),
                    Some(0)
                );
                checks += 12
                    + if bytes == 16 && matches!(lane, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64) {
                        4
                    } else {
                        0
                    };
            }
        }
    }
    assert_eq!(checks, 832);
    eprintln!("PASS {checks} native CG copy/ABI/constant checks across64 linked programs");
}

#[test]
fn integer_vector_carriers_preserve_explicit_darwin_object_compilation() {
    for (lane, bits) in lanes() {
        for bytes in [8, 16] {
            let (mut module, _) = corpus(lane.clone(), bits, bytes);
            module.target_info = Some(TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: Some("aapcs64".into()),
                struct_passing: StructPassingPolicy::NativeC,
            });
            let output = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: OptLevel::O2,
                    ..Default::default()
                },
                TargetSpec::parse("aarch64-apple-darwin").unwrap(),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap();
            assert_eq!(&output.object_code[..4], &[0xcf, 0xfa, 0xed, 0xfe]);
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
