// Copyright 2026 Andrew Yates | Apache-2.0
//! Native C interoperability at the target-dependent i128 register boundary.

#[path = "common/aarch64_native.rs"]
mod native;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn fixture() -> Module {
    let mut module = Module::new("i128_narrow_call");
    for (name, narrow) in [
        ("i8", Ty::I8),
        ("u8", Ty::U8),
        ("i16", Ty::I16),
        ("u16", Ty::U16),
    ] {
        let mut params = vec![Ty::I64, Ty::I128, Ty::I64, Ty::I64, Ty::I64, Ty::I64];
        params.extend([narrow.clone(), narrow]);
        let signature = module
            .add_func_type(FuncTy {
                params: params.clone(),
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let callee_id = FuncId::new(module.functions.len() as u32);
        let mut callee = Function::new(
            callee_id,
            format!("observe_{name}"),
            signature,
            BlockId::new(0),
        );
        callee.blocks.clear();
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");
        for indirect in [false, true] {
            let mut parameters = params.clone();
            if indirect {
                parameters.insert(0, Ty::Func(signature));
            }
            let caller_signature = module
                .add_func_type(FuncTy {
                    params: parameters.clone(),
                    returns: vec![Ty::I64],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let id = FuncId::new(module.functions.len() as u32);
            let mut function = Function::new(
                id,
                format!("{}_{}", if indirect { "indirect" } else { "direct" }, name),
                caller_signature,
                BlockId::new(0),
            );
            let arguments = (usize::from(indirect)..parameters.len())
                .map(|i| ValueId::new(i as u32))
                .collect();
            let call = if indirect {
                Inst::CallIndirect {
                    callee: ValueId::new(0),
                    sig: signature,
                    args: arguments,
                    calling_conv: CallingConv::C,
                }
            } else {
                Inst::Call {
                    callee: callee_id,
                    args: arguments,
                }
            };
            let result = ValueId::new(parameters.len() as u32);
            function.blocks = vec![Block {
                id: BlockId::new(0),
                params: parameters
                    .into_iter()
                    .enumerate()
                    .map(|(i, ty)| (ValueId::new(i as u32), ty))
                    .collect(),
                body: vec![
                    InstrNode::new(call).with_result(result),
                    InstrNode::new(Inst::Return {
                        values: vec![result],
                    }),
                ],
            }];
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
        }
    }
    // The shared native compiler helper supplies target_info before validation.
    module
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#define WIDE int64_t a, __int128 b, int64_t c, int64_t d, int64_t e, int64_t f
#define DECL(N,T) \
  typedef int64_t (*fn_##N)(WIDE,T,T); \
  int64_t observe_##N(WIDE, T g, T h) { \
    return a + (int64_t)b + (int64_t)((unsigned __int128)b >> 64) * 3 + c*5 + d*7 + e*11 + f*13 + (int64_t)g*17 + (int64_t)h*19; \
  } \
  extern int64_t direct_##N(WIDE,T,T); \
  extern int64_t indirect_##N(fn_##N,WIDE,T,T);
DECL(i8,int8_t)
DECL(u8,uint8_t)
DECL(i16,int16_t)
DECL(u16,uint16_t)
#define CHECK(N,T) do { \
  T g = (T)values[i], h = (T)values[(i+3)%12]; \
  int64_t want = observe_##N(a,b,c,d,e,f,g,h); \
  int64_t direct = direct_##N(a,b,c,d,e,f,g,h); \
  int64_t indirect = indirect_##N(observe_##N,a,b,c,d,e,f,g,h); \
  if (want != direct || want != indirect) { \
    printf("%s case %u: want %lld direct %lld indirect %lld\n", #N, i, (long long)want, (long long)direct, (long long)indirect); return 1; \
  } \
} while(0)
int main(void) {
  int values[12] = {0,1,-1,127,128,255,256,-128,-32768,32767,32768,65535};
  for (unsigned i=0;i<12;i++) {
    int64_t a=23+i, c=31+i, d=-37-(int64_t)i, e=41+i, f=-43-(int64_t)i;
    __int128 b=((__int128)(101+i)<<64) | (uint64_t)(103+i);
    CHECK(i8,int8_t); CHECK(u8,uint8_t); CHECK(i16,int16_t); CHECK(u16,uint16_t);
  }
  puts("I128_NARROW_ABI direct_calls=48 indirect_calls=48");
  return 0;
}
"#;

#[test]
fn i128_and_adjacent_narrow_arguments_round_trip_through_native_c() {
    let module = fixture();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = native::compile(&module, opt);
        let Some(code) = native::link_run("i128_narrow_call", &object, DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "{opt:?}");
    }
    eprintln!("I128_NARROW_ABI opt_levels=4 native_calls=384");
}
