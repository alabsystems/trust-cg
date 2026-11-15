// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Shared actual TrustIR inputs; no source-fidelity or panic-runtime authority.
use trust_ir::value::GlobalId;
use trust_ir::{
    AssertKind, Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Global, Inst,
    InstrNode, Linkage, Module, PanicLocation, PanicSite, Ty, ValueId, Visibility,
};

pub fn v(n: u32) -> ValueId {
    ValueId::new(n)
}
pub fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

pub fn module(kind: AssertKind, invoke: bool, global: bool) -> Module {
    let mut m = Module::new("panic_delivery_fixture");
    let ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::Usize, Ty::Usize, Ty::Ptr],
            returns: vec![Ty::Usize],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId::new(0), "tc_check", ty, b(0));
    let params = vec![
        (v(0), Ty::Bool),
        (v(1), Ty::Usize),
        (v(2), Ty::Usize),
        (v(3), Ty::Ptr),
    ];
    let entry_ty = m
        .add_func_type(FuncTy {
            params: if kind.operand_count() == 0 {
                vec![Ty::Ptr]
            } else {
                vec![Ty::Usize, Ty::Usize, Ty::Ptr]
            },
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(1), "panic_delivery_entry", entry_ty, b(0));
    entry.calling_conv = CallingConv::Rust;
    m.functions.push(entry);
    let site = PanicSite {
        entry: FuncId::new(1),
        location: if global {
            m.globals.push(Global {
                name: "panic_delivery_location".into(),
                ty: Ty::U64,
                mutable: false,
                initializer: Some(Constant::Int(0x1234_5678)),
                linkage: Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
            PanicLocation::Global(GlobalId::new(0))
        } else {
            PanicLocation::Value(v(3))
        },
    };
    if invoke {
        caller.blocks = vec![
            Block {
                id: b(0),
                params,
                body: vec![InstrNode::new(Inst::AssertInvoke {
                    cond: v(0),
                    kind,
                    site,
                    normal_dest: b(1),
                    normal_args: vec![v(2)],
                    unwind_dest: b(2),
                })],
            },
            Block {
                id: b(1),
                params: vec![(v(10), Ty::Usize)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                })],
            },
            Block {
                id: b(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    })
                    .with_results([v(20), v(21)]),
                    InstrNode::new(Inst::Resume { exn: v(20) }),
                ],
            },
        ];
    } else {
        caller.blocks = vec![Block {
            id: b(0),
            params,
            body: vec![
                InstrNode::new(Inst::Assert {
                    cond: v(0),
                    kind,
                    site: Some(site),
                }),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }];
    }
    m.functions.insert(0, caller);
    m
}
