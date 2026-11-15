// Copyright 2026 Andrew Yates | Apache-2.0
//! Ordinary source/Core consumer for the complete original defined call.
//! This owner is a canonical logical entry theorem, never a machine, stack,
//! ABI, provider, final-link or installation capability.
use clean_kernel::{BinderInfo, Environment, Expr};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::proof::{IslandEnvironment, SourceDefinitionRef};
use trust_ir::{FuncId, Module};
use trust_ir_build::source_call_operational::{
    check_source_bound_defined_constant_call_entry, reflect_source_call_core_module_v1,
};
use trust_ir_build::{
    ModuleValidationReport,
    core_execution::{Assembler, Catalog, EntryTarget, Limits, MachineModel},
    scoped_local::LocalScope,
};

/// Independent source inputs, not a proposed machine result or callee summary.
pub struct DefinedCallSourceSelection {
    pub caller: FuncId,
    pub callee: FuncId,
    pub island: IslandEnvironment,
    pub caller_source: SourceDefinitionRef,
    pub callee_source: SourceDefinitionRef,
}
/// Exact source-named Core theorem retained against its ORIGINAL module.
/// This is deliberately not SourceBoundReplay or native emission authority.
pub struct CheckedCoreDefinedCallSource<'module> {
    module: &'module Module,
    caller: FuncId,
    callee: FuncId,
    judgment: Expr,
    proof: Expr,
    environment: Environment,
}
impl CheckedCoreDefinedCallSource<'_> {
    pub fn functions_in(&self, module: &Module) -> Result<(FuncId, FuncId), String> {
        if !std::ptr::eq(module, self.module) {
            return Err("Core defined-call theorem belongs to another original module".into());
        }
        Ok((self.caller, self.callee))
    }
    pub fn judgment(&self) -> &Expr {
        &self.judgment
    }
    pub fn proof(&self) -> &Expr {
        &self.proof
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }
}
fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn n(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn app(name: &str, values: impl IntoIterator<Item = Expr>) -> Expr {
    values.into_iter().fold(c(name), Expr::app)
}
fn nil(name: &str) -> Expr {
    app("IRList.nil", [c(name)])
}
fn limits() -> Limits {
    Limits {
        max_operations: 100_000,
        max_locals: 10_000,
        max_list_items: 1_000,
        max_lookup_candidates: 1_000,
        lookup_heartbeats: 2_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn providers() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        Expr::lam(
            BinderInfo::Default,
            app("IRList", [c("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                c("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            app("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}

/// Derive and strictly check the existing shared four-step proof for the
/// original module. The named first model world has empty abstract byte
/// memory, Nat HOST0, no imports and fresh root/leaf owners; it grants no fact
/// about native memory. Logical function addresses are distinct nonzero IDs,
/// not native pointers. Source selection remains independent of module data.
/// No caller/leaf body is replaced and no result is compared to a Rust number.
pub fn derive_core_defined_call_source<'module>(
    report: &ModuleValidationReport<'module>,
    source: &DefinedCallSourceSelection,
) -> Result<CheckedCoreDefinedCallSource<'module>, String> {
    let module: &'module Module = report
        .validated_module()
        .ok_or("defined-call source needs a successful original-module report")?;
    let specification = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
        .map_err(|error| error.to_string())?;
    let addresses = module
        .functions
        .iter()
        .map(|function| (function.id, u64::from(function.id.index()) + 1))
        .collect::<Vec<_>>();
    let reflected = reflect_source_call_core_module_v1(report, &addresses)
        .map_err(|error| error.to_string())?;
    let mut catalog = Catalog::new(specification.env(), &reflected, limits())?;
    let owner = catalog.defined_constant_call(source.caller, source.callee)?;
    let model = MachineModel::new(c("Nat"), &reflected, providers());
    let memory = app(
        "IRByteMemoryV1.mk",
        [
            nil("IRByteAllocationV1"),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                app("IROption.none", [c("Nat")]),
            ),
            n(1),
        ],
    );
    let root = owner.entry_root(memory.clone(), n(0));
    let mut scope = LocalScope::new();
    let mut assembler = Assembler::new(&mut scope, limits())?;
    // These are proof candidates, not assumptions. The existing whole-entry
    // checker must establish actual initialization/admission and retirement.
    let ready = assembler.conversion(
        c("Bool"),
        EntryTarget::memory_admission(memory.clone()),
        c("Bool.true"),
    )?;
    let admitted =
        assembler.conversion(c("Bool"), owner.entry_admission(&model)?, c("Bool.true"))?;
    let leaf = assembler.conversion(
        c("IRByteMemoryV1"),
        app("ir_byte_retire_v1", [root.next.clone(), memory.clone()]),
        memory.clone(),
    )?;
    let caller = assembler.conversion(
        c("IRByteMemoryV1"),
        app("ir_byte_retire_v1", [root.owner.clone(), memory.clone()]),
        memory.clone(),
    )?;
    let candidate = owner.execute_entry(
        &mut assembler,
        &model,
        memory.clone(),
        n(0),
        ready,
        admitted,
        leaf,
        caller,
    )?;
    let proof = scope
        .close(candidate.run.equality().term())
        .map_err(|error| error.to_string())?;
    let encoded =
        trust_ir::proof::encode_clean_expr_dag_v2(&proof).map_err(|error| error.to_string())?;
    let core = owner.check_entry_proof(c("Nat"), providers(), memory, n(0), &encoded)?;
    let joined = check_source_bound_defined_constant_call_entry(
        report,
        &core,
        &source.island,
        &source.caller_source,
        &source.callee_source,
    )
    .map_err(|error| error.to_string())?;
    let (caller, callee) = joined
        .functions_in(module)
        .map_err(|error| error.to_string())?;
    // Retain owned checked terms, not a borrowed reflector, and keep the exact
    // report's original module borrow. A cloned module cannot inherit custody.
    Ok(CheckedCoreDefinedCallSource {
        module,
        caller,
        callee,
        judgment: joined.judgment().clone(),
        proof: joined.proof().clone(),
        environment: joined.environment().clone(),
    })
}
