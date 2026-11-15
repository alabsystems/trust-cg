// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Kernel replay of a two-step Store/Return invocation in canonical ByteV1.
//!
//! The independently reconstructed claim quantifies over ALL initial byte
//! maps and preserves the complete final allocation history, cursor, host
//! state and owner counter. Addresses, the stored word and allocation rows are
//! concrete invocation inputs. The retained signature and Store select the
//! exact I32/U32 four-byte or I64 eight-byte lane; I32 also uses its canonical
//! unsigned 32-bit bit pattern. This is not a universal function certificate,
//! native-memory/ABI refinement, or permission to publish machine code. In
//! particular, reference types and proof annotations confer no storage rights.

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{FuncId, Inst, Module, Ty};
use trust_ir_build::{
    core_execution::{MachineModel, NatTerm},
    core_reflection::reflect_core_module_v1,
    translation::{
        KernelCheckedTranslationTerm, SourceTranslationModel, TranslationRecheckError,
        TranslationRechecker,
    },
};

/// An actual ByteV1 allocation record, including retired history.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteAllocation {
    pub base: u64,
    pub size: u64,
    pub owner: u32,
    pub live: bool,
}

/// Explicit caller state for one typed integer store. No access fact is inferred
/// from these fields: initialization and the fetched store must kernel-check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteStoreInvocation {
    pub function: FuncId,
    pub address: u64,
    pub word: u64,
    pub allocations: Vec<ByteAllocation>,
    pub allocation_cursor: u64,
    pub host_state: u64,
}

/// Fixed-vocabulary consumer. Certificates contain only a lossless DAG proof
/// term; neither the vocabulary, expected endpoint nor limits come from them.
#[derive(Debug)]
pub struct ByteStoreRechecker {
    inner: TranslationRechecker<StoreModel>,
}

/// Evidence only for the retained invocation/module in the documented model.
/// There is deliberately no conversion to native compilation authority.
#[derive(Debug)]
pub struct KernelCheckedByteStore<'a> {
    checked: KernelCheckedTranslationTerm<'a, StoreModel>,
}

impl KernelCheckedByteStore<'_> {
    pub fn invocation(&self) -> &ByteStoreInvocation {
        self.checked.source()
    }
    pub fn module(&self) -> &Module {
        self.checked.target()
    }
    pub fn proof_bytes(&self) -> &[u8] {
        self.checked.proof_term()
    }
}

impl ByteStoreRechecker {
    pub fn new() -> Result<Self, TranslationRecheckError> {
        Ok(Self {
            inner: TranslationRechecker::new(Default::default())?,
        })
    }

    pub fn recheck<'a>(
        &'a self,
        invocation: &'a ByteStoreInvocation,
        module: &'a Module,
        proof_dag: &'a [u8],
    ) -> Result<KernelCheckedByteStore<'a>, TranslationRecheckError> {
        Ok(KernelCheckedByteStore {
            checked: self.inner.recheck_dag_v2(invocation, module, proof_dag)?,
        })
    }
}

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
        .fold(app("IRList.nil", [c(ty)]), |tail, value| {
            app("IRList.cons", [c(ty), value.clone(), tail])
        })
}
fn byte_map_type() -> Expr {
    Expr::pi(BinderInfo::Default, c("Nat"), app("IROption", [c("Nat")]))
}
fn providers() -> Expr {
    // Total failing provider. The admitted module has no imports or calls.
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

impl ByteStoreInvocation {
    fn rows(&self) -> Expr {
        list(
            "IRByteAllocationV1",
            &self
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
    fn memory(&self, bytes: Expr) -> Expr {
        app(
            "IRByteMemoryV1.mk",
            [self.rows(), bytes, nat(self.allocation_cursor)],
        )
    }
    fn arguments(&self) -> Expr {
        list(
            "IRScalar",
            &[
                app("IRScalar.ptr_", [nat(self.address)]),
                app("IRScalar.int_", [nat(self.word)]),
            ],
        )
    }
    fn initial(&self, model: &MachineModel, bytes: Expr) -> Expr {
        app(
            "ir_byte_init_v1",
            [
                c("Nat"),
                model.context().clone(),
                nat(u64::from(self.function.index())),
                self.arguments(),
                self.memory(bytes),
                nat(self.host_state),
            ],
        )
    }
    fn terminal(&self, bytes: Expr, byte_width: u64) -> Expr {
        // Independent specification, not an assembler endpoint. ByteV1 chooses
        // a fresh activation above ALL owners, including retired rows, then
        // advances its counter. The admitted body allocates no activation data.
        let fresh = self
            .allocations
            .iter()
            .map(|row| u64::from(row.owner) + 1)
            .max()
            .unwrap_or(1)
            .max(1);
        let memory = self.memory(app(
            "ir_byte_write_word_v1",
            [bytes, nat(self.address), nat(byte_width), nat(self.word)],
        ));
        let world = app(
            "IRByteWorldV1.mk",
            [
                c("Nat"),
                memory,
                nat(self.host_state),
                list("Nat", &[]),
                nat(fresh + 1),
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
}

struct StoreModel;

impl SourceTranslationModel for StoreModel {
    type Source = ByteStoreInvocation;

    fn build_environment() -> Result<Environment, String> {
        Ok(shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|error| error.to_string())?
            .env()
            .clone())
    }

    fn reconstruct(source: &ByteStoreInvocation, target: &Module) -> Result<Expr, String> {
        if source.allocations.len() > 64 || target.functions.len() != 1 {
            return Err(
                "byte-store replay requires one function and at most 64 allocation rows".into(),
            );
        }
        let function = &target.functions[0];
        if function.id != source.function
            || function.blocks.len() != 1
            || function.blocks[0].body.len() != 2
        {
            return Err("byte-store replay requires one two-instruction block".into());
        }
        let signature = target
            .func_type(function.ty)
            .ok_or("missing store signature")?;
        let (word_ty, byte_width) = match signature.params.as_slice() {
            [Ty::Ptr, ty @ (Ty::I32 | Ty::U32)] => (ty, 4),
            [Ty::Ptr, ty @ Ty::I64] => (ty, 8),
            _ => return Err("byte-store replay requires (Ptr, I32/U32/I64) -> ()".into()),
        };
        if !signature.returns.is_empty() {
            return Err("byte-store replay requires an empty return signature".into());
        }
        if byte_width == 4 && source.word > u64::from(u32::MAX) {
            return Err("byte-store replay requires a canonical 32-bit word".into());
        }
        let nodes = &function.blocks[0].body;
        if !matches!(
            &nodes[0].inst,
            Inst::Store {
                ty,
                volatile: false,
                ..
            } if ty == word_ty
        ) || !matches!(&nodes[1].inst, Inst::Return { values } if values.is_empty())
        {
            return Err(
                "byte-store replay requires a signature-matched nonvolatile integer Store then empty Return".into(),
            );
        }
        // Reflection validates the ORIGINAL module and preserves operands,
        // alignment, site metadata, target layout and unsupported annotations.
        let reflected = reflect_core_module_v1(target, &[(source.function, 4096)])
            .map_err(|error| error.to_string())?;
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        let bytes = Expr::bvar(0);
        let claim = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                model.config_type(),
                model.run(&NatTerm::literal(2), source.initial(&model, bytes.clone())),
                source.terminal(bytes, byte_width),
            ],
        );
        Ok(Expr::pi(BinderInfo::Default, byte_map_type(), claim))
    }
}

#[cfg(test)]
#[path = "core_byte_store_four_tests.rs"]
mod four_tests;
