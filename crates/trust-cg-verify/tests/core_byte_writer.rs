// Copyright 2026 Andrew Yates | Apache-2.0

//! Whole execution of the actual captured writer, with an independent output
//! contract. This is an IR invocation claim, not Rust or native-code authority.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use std::sync::OnceLock;
use trust_cg_verify::core_byte_store::ByteAllocation;
use trust_ir::{FuncId, Inst, Module, Ty, ValueId};
use trust_ir_build::{
    core_execution::{MachineModel, NatTerm},
    core_reflection::reflect_core_module_v1,
    translation::{SourceTranslationModel, TranslationRechecker},
};

#[path = "core_byte_writer/symbolic.rs"]
mod symbolic;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn list(ty: &str, values: &[Expr]) -> Expr {
    values
        .iter()
        .rev()
        .fold(app("IRList.nil", [c(ty)]), |tail, head| {
            app("IRList.cons", [c(ty), head.clone(), tail])
        })
}
fn bytes_type() -> Expr {
    Expr::pi(BinderInfo::Default, c("Nat"), app("IROption", [c("Nat")]))
}
fn providers() -> Expr {
    let body = app(
        "IRByteImportResultV1.mk",
        [
            c("Nat"),
            app("IROutcome.stuck", [c("IRFault.no_func")]),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    [
        c("Nat"),
        app("IRList", [c("IRScalar")]),
        c("IRByteMemoryV1"),
        c("Nat"),
    ]
    .into_iter()
    .rev()
    .fold(body, |body, ty| Expr::lam(BinderInfo::Default, ty, body))
}

#[derive(Clone)]
struct WriterCall {
    address: u64,
    words: [u64; 5],
    allocations: Vec<ByteAllocation>,
    cursor: u64,
    host: u64,
}
fn allocation_rows(source: &WriterCall) -> Expr {
    list(
        "IRByteAllocationV1",
        &source
            .allocations
            .iter()
            .map(|row| {
                app(
                    "IRByteAllocationV1.mk",
                    [
                        nat(row.base),
                        nat(row.size),
                        nat(u64::from(row.owner)),
                        c(if row.live { "Bool.true" } else { "Bool.false" }),
                    ],
                )
            })
            .collect::<Vec<_>>(),
    )
}
fn memory(source: &WriterCall, bytes: Expr) -> Expr {
    app(
        "IRByteMemoryV1.mk",
        [allocation_rows(source), bytes, nat(source.cursor)],
    )
}
#[derive(Clone, Copy, Debug)]
enum Corruption {
    None,
    WrongWord,
    EraseLastStore,
    UnwrittenByte,
    Host,
    Cursor,
    DropHistory,
    ActiveOwner,
    OwnerCounter,
}
fn expected(source: &WriterCall, mut bytes: Expr, corruption: Corruption) -> Expr {
    // Independent output contract: five stores and otherwise the entire original
    // world. The module is executed separately by the canonical byte machine.
    for (index, word) in source.words.iter().enumerate() {
        if matches!(corruption, Corruption::EraseLastStore) && index == 4 {
            continue;
        }
        let word = if matches!(corruption, Corruption::WrongWord) && index == 2 {
            word ^ 1
        } else {
            *word
        };
        bytes = app(
            "ir_byte_write_word_v1",
            [
                bytes,
                nat(source.address + 8 * index as u64),
                nat(8),
                nat(word),
            ],
        );
    }
    if matches!(corruption, Corruption::UnwrittenByte) {
        bytes = app("ir_byte_write_word_v1", [bytes, nat(200), nat(1), nat(9)]);
    }
    let next = source
        .allocations
        .iter()
        .map(|row| u64::from(row.owner))
        .max()
        .unwrap_or(0)
        + 2;
    let mut terminal = source.clone();
    if matches!(corruption, Corruption::Host) {
        terminal.host ^= 1;
    }
    if matches!(corruption, Corruption::Cursor) {
        terminal.cursor += 8;
    }
    if matches!(corruption, Corruption::DropHistory) {
        terminal.allocations.remove(1);
    }
    let owners = if matches!(corruption, Corruption::ActiveOwner) {
        vec![nat(next - 1)]
    } else {
        vec![]
    };
    let world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            memory(&terminal, bytes),
            nat(terminal.host),
            list("Nat", &owners),
            nat(if matches!(corruption, Corruption::OwnerCounter) {
                next - 1
            } else {
                next
            }),
        ],
    );
    app(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            app("IROutcome.ret", [list("IRScalar", &[])]),
            world,
        ],
    )
}

struct WriterModel;
impl SourceTranslationModel for WriterModel {
    type Source = WriterCall;
    fn build_environment() -> Result<Environment, String> {
        Ok(shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|error| error.to_string())?
            .env()
            .clone())
    }
    fn reconstruct(source: &WriterCall, target: &Module) -> Result<Expr, String> {
        if source.address.checked_add(39).is_none() || source.allocations.len() > 8 {
            return Err("bounded writer invocation required".into());
        }
        if target.functions.len() != 1 || target.functions[0].blocks.len() != 1 {
            return Err("one writer function/block required".into());
        }
        let function = &target.functions[0];
        if function.id != FuncId::new(0) || function.blocks[0].body.len() > 128 {
            return Err("writer profile size or entry mismatch".into());
        }
        let mut params = vec![Ty::RefMut(Box::new(Ty::Tuple(vec![Ty::U64; 5])))];
        params.extend(vec![Ty::U64; 5]);
        let signature = target.func_type(function.ty).ok_or("missing signature")?;
        if signature.params != params || !signature.returns.is_empty() {
            return Err("expected reference and five words, returning unit".into());
        }
        let reflected = reflect_core_module_v1(target, &[(function.id, 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let mut args = vec![app("IRScalar.ptr_", [nat(source.address)])];
        args.extend(
            source
                .words
                .iter()
                .map(|word| app("IRScalar.int_", [nat(*word)])),
        );
        let initial = app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(0),
                list("IRScalar", &args),
                memory(source, Expr::bvar(0)),
                nat(source.host),
            ],
        );
        let claim = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                model.config_type(),
                model.run(
                    &NatTerm::literal(function.blocks[0].body.len() as u64),
                    initial,
                ),
                expected(source, Expr::bvar(0), Corruption::None),
            ],
        );
        Ok(Expr::pi(BinderInfo::Default, bytes_type(), claim))
    }
}

fn module() -> Module {
    let module: Module = serde_json::from_str(include_str!(
        "fixtures/output_memory_writer-layout-O1.trust-ir.json"
    ))
    .unwrap();
    assert_eq!(module.functions[0].blocks[0].body.len(), 51);
    assert_eq!(
        module.functions[0].blocks[0]
            .body
            .iter()
            .filter(|node| matches!(node.inst, Inst::Store { .. }))
            .count(),
        5
    );
    module
}
fn invocation() -> WriterCall {
    WriterCall {
        address: 80,
        words: [0, 1, 0x0123_4567_89ab_cdef, 1_u64 << 63, u64::MAX],
        allocations: vec![
            ByteAllocation {
                base: 80,
                size: 48,
                owner: 0,
                live: true,
            },
            ByteAllocation {
                base: 16,
                size: 16,
                owner: 7,
                live: false,
            },
            ByteAllocation {
                base: 160,
                size: 8,
                owner: 0,
                live: true,
            },
        ],
        cursor: 512,
        host: 37,
    }
}
fn checker() -> &'static TranslationRechecker<WriterModel> {
    static CHECKER: OnceLock<TranslationRechecker<WriterModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}
fn candidate(source: &WriterCall, corruption: Corruption) -> Vec<u8> {
    // This supplies only reflexivity of the claimed endpoint. The checker must
    // independently reduce actual init, all 51 fetched steps and root return.
    let term = Expr::lam(
        BinderInfo::Default,
        bytes_type(),
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [
                app("IRByteConfigV1", [c("Nat")]),
                expected(source, Expr::bvar(0), corruption),
            ],
        ),
    );
    trust_ir::proof::encode_clean_expr_dag_v2(&term).unwrap()
}
fn reject(label: &str, source: &WriterCall, module: &Module, proof: &[u8], stage: &str) {
    let error = checker()
        .recheck_dag_v2(source, module, proof)
        .expect_err(label);
    assert_eq!(error.stage(), stage, "{label}: {error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{label}: {error}"
        );
    }
    if stage == "kernel audit" {
        assert!(error.reason().contains("TypeMismatch"), "{label}: {error}");
    }
    if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
        let record =
            serde_json::json!({"label":label,"stage":error.stage(),"reason":error.reason()});
        std::fs::write(
            std::path::Path::new(&directory).join(format!("reject-{label}.json")),
            serde_json::to_vec_pretty(&record).unwrap(),
        )
        .unwrap();
    }
}

#[test]
fn writer_replays_complete_captured_module() {
    let module = module();
    for address in [80, 88] {
        let mut source = invocation();
        source.address = address;
        let proof = candidate(&source, Corruption::None);
        let checked = checker().recheck_dag_v2(&source, &module, &proof).unwrap();
        assert!(std::ptr::eq(checked.target(), &module));
        assert!(std::ptr::eq(checked.source(), &source));
        assert_eq!(checked.proof_term(), proof);
        if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
            let dir = std::path::Path::new(&directory);
            std::fs::write(dir.join(format!("writer-{address}.dag")), &proof).unwrap();
            std::fs::write(
                dir.join(format!("writer-{address}.json")),
                serde_json::to_vec_pretty(&serde_json::json!({
                    "address":address,"words":source.words,"proof_bytes":proof.len(),
                    "instructions":51,"stores":5,"quantified":"all initial byte maps"
                }))
                .unwrap(),
            )
            .unwrap();
        }
    }
}

#[test]
fn writer_rejects_changed_fetched_stores() {
    let source = invocation();
    let original = module();
    let proof = candidate(&source, Corruption::None);
    for index in 0..5 {
        let mut changed = original.clone();
        let Inst::Store { value, .. } =
            &mut changed.functions[0].blocks[0].body[10 * index + 9].inst
        else {
            panic!("captured store")
        };
        *value = ValueId::new(2 + ((index + 1) % 5) as u32);
        reject(
            &format!("store-{index}-value"),
            &source,
            &changed,
            &proof,
            "kernel audit",
        );
    }
    let mut changed = original.clone();
    let Inst::Store { ptr, .. } = &mut changed.functions[0].blocks[0].body[29].inst else {
        panic!("captured store")
    };
    *ptr = ValueId::new(14);
    reject("store-2-address", &source, &changed, &proof, "kernel audit");
}

#[test]
fn writer_rejects_false_terminal_world() {
    let source = invocation();
    let module = module();
    for corruption in [
        Corruption::WrongWord,
        Corruption::EraseLastStore,
        Corruption::UnwrittenByte,
        Corruption::Host,
        Corruption::Cursor,
        Corruption::DropHistory,
        Corruption::ActiveOwner,
        Corruption::OwnerCounter,
    ] {
        reject(
            &format!("terminal-{corruption:?}"),
            &source,
            &module,
            &candidate(&source, corruption),
            "kernel audit",
        );
    }
}

#[test]
fn writer_rejects_invalid_caller_memory() {
    let module = module();
    for case in [
        "inactive-owner",
        "retired-output",
        "short-output",
        "overlapping-output",
    ] {
        let mut source = invocation();
        match case {
            "inactive-owner" => source.allocations[0].owner = 3,
            "retired-output" => source.allocations[0].live = false,
            "short-output" => source.allocations[0].size = 39,
            "overlapping-output" => {
                let duplicate = source.allocations[0].clone();
                source.allocations.push(duplicate);
            }
            _ => unreachable!(),
        }
        reject(
            case,
            &source,
            &module,
            &candidate(&source, Corruption::None),
            "kernel audit",
        );
    }
}

#[test]
fn writer_retained_proof_binds_inputs_and_decodes_exactly() {
    let module = module();
    let source = invocation();
    let proof = candidate(&source, Corruption::None);
    let mut changed = source.clone();
    changed.words[4] ^= 1;
    reject(
        "reused-different-word",
        &changed,
        &module,
        &proof,
        "kernel audit",
    );
    changed = source.clone();
    changed.address = 88;
    reject(
        "reused-different-address",
        &changed,
        &module,
        &proof,
        "kernel audit",
    );
    let mut malformed = proof.clone();
    malformed.push(0);
    reject(
        "trailing-proof-byte",
        &source,
        &module,
        &malformed,
        "decode",
    );
    reject(
        "truncated-proof",
        &source,
        &module,
        &proof[..proof.len() - 1],
        "decode",
    );
    changed.address = u64::MAX - 38;
    reject("wrapping-output", &changed, &module, &proof, "reconstruct");
}
