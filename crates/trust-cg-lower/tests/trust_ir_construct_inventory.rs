// trust_ir_construct_inventory.rs - versioned trust-ir source-construct
// inventory gate (ledger L05-P2).
//
// Every variant of the pinned trust-ir's `Ty`, `Inst`, `Constant` and `CastOp`
// enums and every `Module` table is enumerated BY NAME from the crate itself
// (an exhaustive `match` / struct pattern, so a new upstream variant or field
// fails this build) and bound to exactly one disposition row:
//
// * `Executed`  - a native Darwin test (a `scripts/check_darwin_aarch64.py`
//                 floor target) links or JIT-executes code that carries the
//                 construct on this host;
// * `ModelOnly` - an adapter/lowering test drives the construct through
//                 `trust_cg_lower` but no native Darwin execution exists;
// * `Refused`   - the adapter refuses a minimal module carrying the construct
//                 with a named diagnostic, driven here and pinned elsewhere.
//
// The gate fails when a variant lacks a row, a refused construct is not
// refused with its diagnostic, a positive probe fails or a negative twin is
// not refused. A row's evidence file, test and needle are curated pointers for
// readers; they are not checked here. It runs against the trust-ir revision
// `Cargo.lock` resolves; `scripts/bump_trust_ir_pin.py` runs it as a guard of
// every pin move, so a move that changes the construct set fails until the
// rows follow.
//
// Rows are curated, not inferred: an `Executed` claim names the test whose
// native run carries the construct; when that is in doubt the row is
// `ModelOnly`. Nothing here is a proof of correctness; it is the coverage
// ledger that says which constructs have which strength of evidence.

use std::collections::BTreeSet;

#[path = "common/canonical_constant_inventory.rs"]
mod canonical_constants;
#[path = "common/runtime_closure.rs"]
mod runtime_closure;

use trust_cg_lower::adapter::translate_type;
use trust_cg_lower::function::Function as LirFunction;
use trust_ir::dialect::DialectInst;
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::pred::{Space, Universe};
use trust_ir::proof::{
    DiagnosticSeverity, ObligationDiagnostic, ObligationKind, ProofDigest, ProofObligation,
    ProofStatus,
};
use trust_ir::spec::SpecModule;
use trust_ir::value::{BindingFrameId, SourceSpan};
use trust_ir::{
    Block as TrustIrBlock, BlockId, CastOp, ClosureTyId, Constant, DialectTy, Endianness, EnumDef,
    EnumId, EnumVariant, FieldDef, FuncId, FuncTy, FuncTyId, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, ModuleImport, Ordering, Pred, ProofId, RecordDef, RecordId,
    SetRepr, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    TupleLayoutDescriptor, Ty, TyId, ValueId,
};

const CG: &str = "crates/trust-cg-codegen/tests/";
const LW: &str = "crates/trust-cg-lower/tests/";
const MANIFEST: &str = "crates/trust-cg-lower/tests/trust_ir_conformance_manifest.rs";
const PIN_MOVE: &str = "crates/trust-cg-lower/tests/pin_move_floor.rs";
const HANDLE: &str = "crates/trust-cg-lower/tests/v43_opaque_handle.rs";
const SELF_FILE: &str = "crates/trust-cg-lower/tests/trust_ir_construct_inventory.rs";
const LW_DEALLOC: &str = "crates/trust-cg-lower/tests/trust_ir_dealloc_refusal.rs";
/// The test in this file that drives every `Refused` row; rows with no other
/// pin name it.
const REFUSAL_GATE: &str = "refused_rows_are_refused_by_the_adapter_by_name";

// ---------------------------------------------------------------------------
// Exhaustive enumerations, derived from the pinned crate.
//
// Each `match` has no wildcard arm, so an added upstream variant is a compile
// error here, and the name list is generated from the same arms, so it cannot
// drift from the match. A removed or renamed variant fails to compile too.
// ---------------------------------------------------------------------------

macro_rules! variant_inventory {
    (
        $name_fn:ident, $all:ident, $enum:ty, [ $( $pat:pat => $name:literal ),+ $(,)? ]
        $(, uninhabited: [ $( $upat:pat => $never:expr ),+ $(,)? ] )?
    ) => {
        /// Name of the variant `value` inhabits. Its exhaustive `match` is
        /// what makes an upstream variant change a build failure; the row
        /// tables consume the derived name list. An `uninhabited` arm names a
        /// variant no level-R value can take (trust-ir amendment S's `Ext`),
        /// so it gets no name and no row.
        fn $name_fn(value: &$enum) -> &'static str {
            match value {
                $( $pat => $name, )+
                $( $( $upat => $never, )+ )?
            }
        }
        const $all: &[&str] = &[ $( $name ),+ ];
    };
}

variant_inventory!(ty_variant_name, TY_VARIANTS, Ty, [
    Ty::I8 => "I8",
    Ty::I16 => "I16",
    Ty::I32 => "I32",
    Ty::I64 => "I64",
    Ty::I128 => "I128",
    Ty::U8 => "U8",
    Ty::U16 => "U16",
    Ty::U32 => "U32",
    Ty::U64 => "U64",
    Ty::U128 => "U128",
    Ty::Isize => "Isize",
    Ty::Usize => "Usize",
    Ty::Char => "Char",
    Ty::Error => "Error",
    Ty::F16 => "F16",
    Ty::F32 => "F32",
    Ty::F64 => "F64",
    Ty::Bool => "Bool",
    Ty::Vector(..) => "Vector",
    Ty::Ptr => "Ptr",
    Ty::FatPtr(..) => "FatPtr",
    Ty::Unit => "Unit",
    Ty::Storage(..) => "Storage",
    Ty::Never => "Never",
    Ty::Struct(..) => "Struct",
    Ty::Array(..) => "Array",
    Ty::Tuple(..) => "Tuple",
    Ty::Enum(..) => "Enum",
    Ty::Func(..) => "Func",
    Ty::Ref(..) => "Ref",
    Ty::RefMut(..) => "RefMut",
    Ty::PtrConst(..) => "PtrConst",
    Ty::PtrMut(..) => "PtrMut",
    Ty::Rc(..) => "Rc",
    Ty::Set(..) => "Set",
    Ty::Sequence(..) => "Sequence",
    Ty::Record(..) => "Record",
    Ty::Closure(..) => "Closure",
    Ty::Refine(..) => "Refine",
    Ty::Dialect(..) => "Dialect",
    Ty::Handle(..) => "Handle",
    Ty::Tensor(..) => "Tensor",
], uninhabited: [
    Ty::Ext(e) => e.unreachable(),
]);

variant_inventory!(inst_variant_name, INST_VARIANTS, Inst, [
    Inst::BinOp { .. } => "BinOp",
    Inst::UnOp { .. } => "UnOp",
    Inst::Overflow { .. } => "Overflow",
    Inst::ICmp { .. } => "ICmp",
    Inst::FCmp { .. } => "FCmp",
    Inst::Cast { .. } => "Cast",
    Inst::Load { .. } => "Load",
    Inst::Store { .. } => "Store",
    Inst::MemCopy { .. } => "MemCopy",
    Inst::MemSet { .. } => "MemSet",
    Inst::Alloca { .. } => "Alloca",
    Inst::HeapAlloc { .. } => "HeapAlloc",
    Inst::GEP { .. } => "GEP",
    Inst::PtrData { .. } => "PtrData",
    Inst::PtrMetadata { .. } => "PtrMetadata",
    Inst::PtrFromParts { .. } => "PtrFromParts",
    Inst::AtomicLoad { .. } => "AtomicLoad",
    Inst::AtomicStore { .. } => "AtomicStore",
    Inst::AtomicRMW { .. } => "AtomicRMW",
    Inst::CmpXchg { .. } => "CmpXchg",
    Inst::Fence { .. } => "Fence",
    Inst::Br { .. } => "Br",
    Inst::CondBr { .. } => "CondBr",
    Inst::Switch { .. } => "Switch",
    Inst::Call { .. } => "Call",
    Inst::CallIndirect { .. } => "CallIndirect",
    Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
    Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
    Inst::AssertInvoke { .. } => "AssertInvoke",
    Inst::DropInvoke { .. } => "DropInvoke",
    Inst::InvokeIndirect { .. } => "InvokeIndirect",
    Inst::Return { .. } => "Return",
    Inst::ExtractField { .. } => "ExtractField",
    Inst::InsertField { .. } => "InsertField",
    Inst::ExtractElement { .. } => "ExtractElement",
    Inst::InsertElement { .. } => "InsertElement",
    Inst::Const { .. } => "Const",
    Inst::NullPtr => "NullPtr",
    Inst::GlobalAddr { .. } => "GlobalAddr",
    Inst::Undef { .. } => "Undef",
    Inst::Assume { .. } => "Assume",
    Inst::Assert { .. } => "Assert",
    Inst::Unreachable => "Unreachable",
    Inst::Copy { .. } => "Copy",
    Inst::Select { .. } => "Select",
    Inst::SeqMapAddK { .. } => "SeqMapAddK",
    Inst::SeqMapNot { .. } => "SeqMapNot",
    Inst::SeqMap { .. } => "SeqMap",
    Inst::Borrow { .. } => "Borrow",
    Inst::BorrowMut { .. } => "BorrowMut",
    Inst::EndBorrow { .. } => "EndBorrow",
    Inst::Retain { .. } => "Retain",
    Inst::Release { .. } => "Release",
    Inst::IsUnique { .. } => "IsUnique",
    Inst::Dealloc { .. } => "Dealloc",
    Inst::OpenFrame { .. } => "OpenFrame",
    Inst::BindSlot { .. } => "BindSlot",
    Inst::LoadSlot { .. } => "LoadSlot",
    Inst::CloseFrame { .. } => "CloseFrame",
    Inst::CoroSuspend { .. } => "CoroSuspend",
    Inst::Invoke { .. } => "Invoke",
    Inst::LandingPad { .. } => "LandingPad",
    Inst::Resume { .. } => "Resume",
    Inst::DialectOp(..) => "DialectOp",
    Inst::MakeAggregate { .. } => "MakeAggregate",
    Inst::MakeClosure { .. } => "MakeClosure",
    Inst::Drop { .. } => "Drop",
    Inst::ArraySplat { .. } => "ArraySplat",
    Inst::TensorContract { .. } => "TensorContract",
    Inst::TensorMap { .. } => "TensorMap",
    Inst::TensorReduce { .. } => "TensorReduce",
    Inst::TensorView { .. } => "TensorView",
    Inst::TensorGather { .. } => "TensorGather",
    Inst::TensorScatter { .. } => "TensorScatter",
]);

variant_inventory!(constant_variant_name, CONSTANT_VARIANTS, Constant, [
    Constant::Int(..) => "Int",
    Constant::U128(..) => "U128",
    Constant::Bytes { .. } => "Bytes",
    Constant::Float(..) => "Float",
    Constant::Bool(..) => "Bool",
    Constant::Aggregate(..) => "Aggregate",
    Constant::Array(..) => "Array",
    Constant::Vector(..) => "Vector",
    Constant::Sequence(..) => "Sequence",
    Constant::Set(..) => "Set",
    Constant::Record(..) => "Record",
    Constant::Closure { .. } => "Closure",
    Constant::FnDef(..) => "FnDef",
    Constant::SymbolAddr { .. } => "SymbolAddr",
    Constant::PhantomData => "PhantomData",
    Constant::Uninit => "Uninit",
    Constant::Splat { .. } => "Splat",
    Constant::TensorBlob { .. } => "TensorBlob",
], uninhabited: [
    Constant::Ext(e) => e.unreachable(),
]);

variant_inventory!(cast_op_variant_name, CAST_OP_VARIANTS, CastOp, [
    CastOp::Trunc => "Trunc",
    CastOp::ZExt => "ZExt",
    CastOp::SExt => "SExt",
    CastOp::FPTrunc => "FPTrunc",
    CastOp::FPExt => "FPExt",
    CastOp::FPToUI => "FPToUI",
    CastOp::FPToSI => "FPToSI",
    CastOp::UIToFP => "UIToFP",
    CastOp::SIToFP => "SIToFP",
    CastOp::PtrToInt => "PtrToInt",
    CastOp::IntToPtr => "IntToPtr",
    CastOp::PtrToPtr => "PtrToPtr",
    CastOp::Bitcast => "Bitcast",
    CastOp::Transmute => "Transmute",
    CastOp::ReifyFnPointer => "ReifyFnPointer",
    CastOp::FPToSISat => "FPToSISat",
    CastOp::FPToUISat => "FPToUISat",
]);

/// The `Module` tables, enumerated by an exhaustive struct pattern (no `..`),
/// so an added, removed or renamed field is a compile error here.
macro_rules! module_tables {
    ($($field:ident),+ $(,)?) => {
        fn module_table_names(module: &TrustIrModule) -> Vec<&'static str> {
            let TrustIrModule { $($field),+ } = module;
            $( let _ = $field; )+
            vec![$( stringify!($field) ),+]
        }
    };
}

module_tables!(
    name,
    functions,
    structs,
    enums,
    records,
    closure_types,
    globals,
    func_types,
    types,
    proof_obligations,
    proof_certificates,
    target_info,
    files,
    obligation_diagnostics,
    spec_modules,
    universes,
    predicates,
    global_asm,
    imports,
    tuple_layouts,
    completeness,
    drop_glue,
    closure_layouts,
    blobs,
);

/// Named sub-surfaces of a table that carry their own lowering path. The
/// pinned `Module` has no dialect registry table: the dialect surface is
/// inventoried through `Ty::Dialect` and `Inst::DialectOp`.
const MODULE_SUBTABLES: &[&str] = &["globals.tls"];

// ---------------------------------------------------------------------------
// Rows.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Family {
    Ty,
    Inst,
    Constant,
    CastOp,
    ModuleTable,
}

impl Family {
    fn label(self) -> &'static str {
        match self {
            Family::Ty => "Ty",
            Family::Inst => "Inst",
            Family::Constant => "Constant",
            Family::CastOp => "CastOp",
            Family::ModuleTable => "ModuleTable",
        }
    }
}

/// An adapter probe. `Ok` carries a short description of what lowered; `Err`
/// carries the adapter diagnostic (its `Display` text) or a probe-internal
/// mismatch.
type Probe = fn() -> Result<String, String>;

enum Disposition {
    Executed {
        file: &'static str,
        test: &'static str,
    },
    ModelOnly {
        file: &'static str,
        test: &'static str,
    },
    Refused {
        /// Every needle must appear in the adapter's diagnostic text.
        diagnostic: &'static [&'static str],
        pin_file: &'static str,
        pin_test: &'static str,
    },
}

struct Row {
    family: Family,
    construct: &'static str,
    disposition: Disposition,
    /// Spelling of the construct in the named evidence or pin file
    /// (repo-relative); a pointer for readers, not checked.
    needle: &'static str,
    /// `Refused` rows: the adapter drive that must fail with `diagnostic`.
    /// Other rows: optional positive evidence that must lower; mandatory when
    /// the evidence file is this file.
    probe: Option<Probe>,
    /// Negative twin of a supported construct: needles and the drive that must
    /// fail with them.
    negative: Option<(&'static [&'static str], Probe)>,
    note: &'static str,
}

fn executed(file: &'static str, test: &'static str) -> Disposition {
    Disposition::Executed { file, test }
}

fn model_only(file: &'static str, test: &'static str) -> Disposition {
    Disposition::ModelOnly { file, test }
}

fn refused(
    diagnostic: &'static [&'static str],
    pin_file: &'static str,
    pin_test: &'static str,
) -> Disposition {
    Disposition::Refused {
        diagnostic,
        pin_file,
        pin_test,
    }
}

fn row(
    family: Family,
    construct: &'static str,
    disposition: Disposition,
    needle: &'static str,
    note: &'static str,
) -> Row {
    Row {
        family,
        construct,
        disposition,
        needle,
        probe: None,
        negative: None,
        note,
    }
}

impl Row {
    fn probe(mut self, probe: Probe) -> Self {
        self.probe = Some(probe);
        self
    }

    fn negative(mut self, needles: &'static [&'static str], probe: Probe) -> Self {
        self.negative = Some((needles, probe));
        self
    }
}

macro_rules! cg {
    ($file:literal) => {
        concat!("crates/trust-cg-codegen/tests/", $file, ".rs")
    };
}

fn ty_rows() -> Vec<Row> {
    use Family::Ty as T;
    vec![
        row(T, "I8", executed(cg!("e2e_aarch64_narrow_int_diff"), "e2e_aarch64_narrow_int_matches_llvm"), "Ty::I8", "narrow integer arithmetic against an LLVM-compiled twin"),
        row(T, "I16", executed(cg!("e2e_aarch64_narrow_int_diff"), "e2e_aarch64_narrow_int_matches_llvm"), "Ty::I16", "narrow integer arithmetic against an LLVM-compiled twin"),
        row(T, "I32", executed(cg!("e2e_aarch64_fptosi_sat"), "e2e_aarch64_narrow_saturating_casts_exhaustive"), "Ty::I32", "narrow saturating cast destination (F32 -> I32) clamped and truncated natively"),
        row(T, "I64", executed(cg!("e2e_aarch64_switch"), "e2e_aarch64_switch_matches_clang"), "Ty::I64", "switch selectors and results"),
        row(T, "I128", executed(cg!("e2e_aarch64_i128_icmp"), "e2e_aarch64_i128_icmp_matches_clang"), "Ty::I128", "128-bit comparisons in register pairs"),
        row(T, "U8", executed(cg!("e2e_aarch64_narrow_signed_cmp"), "e2e_aarch64_narrow_signed_compare"), "Ty::U8", "narrow unsigned operands with dirty high bits"),
        row(T, "U16", executed(cg!("e2e_aarch64_narrow_signed_cmp"), "e2e_aarch64_narrow_signed_compare"), "Ty::U16", "narrow unsigned operands with dirty high bits"),
        row(T, "U32", executed(cg!("e2e_aarch64_sitofp_signext"), "e2e_aarch64_sitofp_sign_extends_negatives"), "Ty::U32", "unsigned 32-bit sources of integer-to-float casts"),
        row(T, "U64", executed(cg!("e2e_aarch64_fptosi_sat"), "e2e_aarch64_register_width_saturating_casts"), "Ty::U64", "saturating cast destinations at register width"),
        row(T, "U128", executed(cg!("e2e_aarch64_u128_checked_mul"), "e2e_aarch64_u128_checked_multiply"), "Ty::U128", "checked 128-bit multiply against clang"),
        row(T, "Isize", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_isize_usize_and_char_match_the_interpreter_and_c_o0_through_o3"), "Ty::Isize", "pointer-width signed arithmetic against the interpreter and `intptr_t`"),
        row(T, "Usize", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_isize_usize_and_char_match_the_interpreter_and_c_o0_through_o3"), "Ty::Usize", "pointer-width unsigned division against the interpreter and `uintptr_t`"),
        row(T, "Char", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_isize_usize_and_char_match_the_interpreter_and_c_o0_through_o3"), "Ty::Char", "a `ZExt` origin, a `Char` switch selector, the largest scalar constant and a `Bitcast` to `u32` against the interpreter and C"),
        row(T, "Error", refused(&["Ty::Error", "producer-internal", "fail-closed"], MANIFEST, "check_error_type_fail_closed"), "Ty::Error", "producer-internal bottom type; never wire-legal")
            .probe(probe_error_type),
        row(T, "F16", executed(cg!("e2e_aarch64_f16_scalar"), "e2e_aarch64_scalar_f16_arith"), "Ty::F16", "scalar half-precision arithmetic on the FP16 host profile"),
        row(T, "F32", executed(cg!("e2e_aarch64_fp_minmax"), "e2e_aarch64_fp_minmax"), "Ty::F32", "single-precision min/max against clang"),
        row(T, "F64", executed(cg!("e2e_aarch64_fcmp_nan"), "e2e_aarch64_fcmp_all_predicates_nan_aware"), "Ty::F64", "double-precision comparisons with NaN operands"),
        row(T, "Bool", executed(cg!("e2e_aarch64_i128_icmp"), "e2e_aarch64_i128_icmp_matches_clang"), "Ty::Bool", "comparison results returned to a C driver"),
        row(T, "Vector", executed(cg!("e2e_aarch64_vector_binop"), "e2e_aarch64_v2i64_bitwise"), "Ty::Vector", "<2 x i64> bitwise operations through NEON"),
        row(T, "Ptr", executed(cg!("e2e_aarch64_indirect_call"), "e2e_aarch64_indirect_call_matches_clang"), "Ty::Ptr", "opaque pointers as indirect callees"),
        row(T, "FatPtr", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_fat_pointers_round_trip_their_parts_o0_through_o3"), "Ty::FatPtr", "`&[u64]` slices passed by value across calls and from a C array, against the interpreter and C"),
        row(T, "Storage", executed(cg!("storage_geometry"), "storage_and_parent_allocation_stride_execute_without_by_value_carriers"), "Ty::Storage", "address-only geometry, including declared parent aggregates; no LIR/SSA/ABI value representation")
            .negative(&["Ty::Storage", "no LIR value representation"], probe_storage_value),
        row(T, "Unit", executed(cg!("e2e_aarch64_unit_return"), "e2e_aarch64_unit_returning_functions"), "Ty::Unit", "unit-returning functions called from C"),
        row(T, "Never", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_never_callee_and_unreachable_trap_where_the_interpreter_refuses_o0_through_o3"), "Ty::Never", "a `-> !` function the C driver calls traps natively where the interpreter refuses; `Never` in a value slot (a call result included) is refused as a void value")
            .probe(probe_never_return_signature)
            .negative(&["void type used as value"], probe_never_value_slot),
        row(T, "Struct", executed(cg!("e2e_aarch64_struct_byval"), "e2e_aarch64_struct_byval_args"), "Ty::Struct", "by-value struct arguments against clang"),
        row(T, "Array", executed(cg!("e2e_aarch64_nested_bytes"), "native_nested_array_bytes_o0_through_o3"), "Ty::Array", "nested byte arrays materialized and read back natively"),
        row(T, "Tuple", executed(cg!("e2e_aarch64_nested_bytes"), "native_nested_tuple_bytes_and_empty_leaf_o0_through_o3"), "Ty::Tuple", "nested tuples with an empty leaf"),
        row(T, "Enum", executed(cg!("e2e_aarch64_direct_enums"), "native_direct_enums_agree_with_the_c_oracle_and_the_interpreter_o0_through_o3"), "Ty::Enum", "direct-tag enums against a C oracle and the reference interpreter"),
        row(T, "Func", executed(cg!("e2e_aarch64_closures"), "nested_closure_fndef_and_symbol_addr_constants_materialize_at_every_level"), "Ty::Func", "function-typed constants reified and called"),
        row(T, "Ref", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_reference_carriers_load_and_store_through_ptr_to_ptr_o0_through_o3"), "Ty::Ref(", "shared reference parameter loaded through, from `PtrToPtr` and from C, against the interpreter and C")
            .probe(probe_reference_pointer_carriers),
        row(T, "RefMut", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_reference_carriers_load_and_store_through_ptr_to_ptr_o0_through_o3"), "Ty::RefMut", "unique reference parameter stored and reloaded through, against the interpreter and C")
            .probe(probe_reference_pointer_carriers),
        row(T, "PtrConst", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_reference_carriers_load_and_store_through_ptr_to_ptr_o0_through_o3"), "Ty::PtrConst", "typed const pointer parameter loaded through, against the interpreter and C")
            .probe(probe_reference_pointer_carriers),
        row(T, "PtrMut", executed(cg!("e2e_aarch64_atomics"), "e2e_aarch64_atomicrmw_and_cmpxchg"), "Ty::PtrMut", "typed mutable pointers to atomic cells"),
        row(T, "Rc", refused(&["Ty::Rc", "refcount ownership"], MANIFEST, "check_rc_type_fail_closed"), "Ty::Rc", "reference-counted ownership has no modelled CPU ABI")
            .probe(probe_rc_type),
        row(T, "Set", executed(cg!("e2e_aarch64_sequences"), "boxed_sets_move_as_constants_parameters_and_results_o0_through_o3"), "Ty::Set", "a boxed set moves as the `sequence_layout` image (constructor order) through constants, parameters, results and selects; `SetRepr::Bitset` states no universe and is refused by name")
            .probe(probe_set_type)
            .negative(&["[TCG-SEQ]", "SetRepr::Bitset"], probe_set_bitset_type),
        row(T, "Sequence", executed(cg!("e2e_aarch64_sequences"), "sequences_flow_through_parameters_results_calls_selects_and_loops_o0_through_o3"), "Ty::Sequence", "the `sequence_layout` image pointer in parameters, block parameters and results (trailing result buffer sized from the callee's published length); nested in another type it is refused by name")
            .probe(probe_sequence_type)
            .negative(&["[TCG-SEQ]", "nested inside another type"], probe_nested_sequence_type),
        row(T, "Tensor", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Ty::Tensor", "runtime tensor shape has no machine layout or value ABI")
            .probe(probe_tensor_type),
        row(T, "Record", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_records_over_the_records_table_match_the_interpreter_o0_through_o3"), "Ty::Record", "a record value passed by value and projected by declaration index, against the interpreter; table-less resolution is refused")
            .probe(probe_record_type)
            .negative(&["not yet lowered"], probe_record_type_without_def),
        row(T, "Closure", executed(cg!("e2e_aarch64_closures"), "closure_with_one_capture_applies_by_value_at_every_level"), "Ty::Closure", "closure literals applied through `CallIndirect` with captures spread")
            .negative(&["not yet lowered"], probe_closure_type_without_table),
        row(T, "Refine", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_refinement_carrier_crosses_calls_unchanged_o0_through_o3"), "Ty::Refine", "a `Refine<i64, NonZero>` carrier across a call and the C boundary, unchanged, against the interpreter"),
        row(T, "Dialect", executed(cg!("dialect_legalization_corpus"), "ty_dialect_v39_legalizes_to_its_carrier_and_compiles_exactly_like_core"), "Ty::Dialect", "the corpus row `ty_dialect_v39` at O0-O3, AOT and JIT, after the codegen's registry-driven legalization substitutes the carrier a registration declares (the object is byte-identical to the core twin); an unregistered nominal type is refused by name there, and the adapter alone still refuses every nominal type as the backstop")
            .negative(&["semantic legalization"], probe_dialect_type),
        row(T, "Handle", model_only(HANDLE, "a_pinned_runtime_call_over_a_handle_lowers_on_every_native_entry"), "Ty::handle", "one pointer word in a value slot over a pinned runtime; interiors are refused; no native row: a handle exists only through a pinned runtime's entry points, which no Darwin floor target links, and the reference interpreter mints one only under a host model (a host-assisted run is not in-format evidence)"),
    ]
}

fn inst_rows() -> Vec<Row> {
    use Family::Inst as I;
    vec![
        row(I, "TensorContract", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Inst::TensorContract", "tensor contractions have no native carrier, layout or lowering")
            .probe(probe_tensor_contract),
        row(I, "TensorMap", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Inst::TensorMap", "v68 elementwise tensor maps have no native carrier, layout or lowering")
            .probe(probe_tensor_map),
        row(I, "TensorReduce", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Inst::TensorReduce", "v68 tensor reductions have no native carrier, layout or lowering")
            .probe(probe_tensor_reduce),
        row(I, "TensorView", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Inst::TensorView", "v68 tensor views have no native carrier, layout or lowering")
            .probe(probe_tensor_view),
        row(I, "TensorGather", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Inst::TensorGather", "v69 tensor gathers have no native carrier, layout or lowering, and their bounds precondition has no native check")
            .probe(probe_tensor_gather),
        row(I, "TensorScatter", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Inst::TensorScatter", "v69 tensor scatters have no native carrier, layout or lowering, and their bounds precondition has no native check")
            .probe(probe_tensor_scatter),
        row(I, "BinOp", executed(cg!("e2e_aarch64_narrow_int_diff"), "e2e_aarch64_narrow_int_matches_llvm"), "Inst::BinOp", "integer arithmetic against an LLVM-compiled twin"),
        row(I, "UnOp", executed(cg!("e2e_aarch64_ctpop"), "e2e_aarch64_ctpop_matches_clang"), "Inst::UnOp", "population count against clang"),
        row(I, "Overflow", executed(cg!("e2e_aarch64_i128_overflow"), "e2e_aarch64_i128_u128_checked_overflow_add_sub"), "Inst::Overflow", "checked 128-bit add/sub flags"),
        row(I, "ICmp", executed(cg!("e2e_aarch64_i128_icmp"), "e2e_aarch64_i128_icmp_matches_clang"), "Inst::ICmp", "every predicate at 128 bits"),
        row(I, "FCmp", executed(cg!("e2e_aarch64_fcmp_nan"), "e2e_aarch64_fcmp_all_predicates_nan_aware"), "Inst::FCmp", "every predicate with NaN operands"),
        row(I, "Cast", executed(cg!("e2e_aarch64_fptosi_sat"), "e2e_aarch64_register_width_saturating_casts"), "Inst::Cast", "saturating float-to-int casts"),
        row(I, "Load", executed(cg!("e2e_aarch64_global_var"), "e2e_aarch64_global_var_matches_clang"), "Inst::Load", "loads through global addresses"),
        row(I, "Store", executed(cg!("e2e_aarch64_global_var"), "e2e_aarch64_global_var_matches_clang"), "Inst::Store", "stores through global addresses"),
        row(I, "MemCopy", executed(cg!("e2e_aarch64_bit_intrinsics_bulk_memory"), "e2e_aarch64_ws320_bit_intrinsics_and_bulk_memory_match_c_reference"), "f.memcopy(", "memcpy and overlapping memmove with dynamic, constant and zero counts against libc"),
        row(I, "MemSet", executed(cg!("e2e_aarch64_bit_intrinsics_bulk_memory"), "e2e_aarch64_ws320_bit_intrinsics_and_bulk_memory_match_c_reference"), "f.memset(", "dynamic and constant fills with dynamic and zero counts against libc"),
        row(I, "Alloca", executed(cg!("e2e_aarch64_link"), "e2e_aarch64_tla_record_cross_call_link_and_run"), "Inst::Alloca", "fixed and counted stack slots stored, reloaded and passed to a callee natively"),
        row(I, "HeapAlloc", executed(cg!("e2e_aarch64_heap_dealloc"), "native_heap_dealloc_balances_rust_and_libc_allocators_o0_through_o3"), ".heap_alloc(", "Rust-heap and libc allocations balanced natively; spelled through the `trust_ir_build` builder in the shared `common/heap_dealloc_corpus.rs`"),
        row(I, "GEP", executed(cg!("e2e_aarch64_byte_gather_ro"), "e2e_aarch64_byte_gather_ro_bit_exact_and_no_overread"), ".gep(", "byte-addressed gather indexing against native values and a guard-page overread control"),
        row(I, "PtrData", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_fat_pointers_round_trip_their_parts_o0_through_o3"), "Inst::PtrData", "the data lane of a by-value slice, indexed natively, against the interpreter and C"),
        row(I, "PtrMetadata", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_fat_pointers_round_trip_their_parts_o0_through_o3"), "Inst::PtrMetadata", "the length lane of a by-value slice, against the interpreter and C"),
        row(I, "PtrFromParts", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_fat_pointers_round_trip_their_parts_o0_through_o3"), "Inst::PtrFromParts", "a slice assembled from a stack or C pointer and a length, against the interpreter and C"),
        row(I, "AtomicLoad", executed(cg!("e2e_aarch64_concurrency"), "contended_rmw_cas_and_litmus_agree_with_c11_and_rust_oracles"), "Inst::AtomicLoad", "acquire/relaxed loads in the litmus programs"),
        row(I, "AtomicStore", executed(cg!("e2e_aarch64_concurrency"), "contended_rmw_cas_and_litmus_agree_with_c11_and_rust_oracles"), "Inst::AtomicStore", "release/relaxed stores in the litmus programs"),
        row(I, "AtomicRMW", executed(cg!("e2e_aarch64_llsc_atomics"), "baseline_llsc_rmw_matches_c11_for_every_op_width_and_ordering_o0_through_o3"), "Inst::AtomicRMW", "every op, width and ordering against C11"),
        row(I, "CmpXchg", executed(cg!("e2e_aarch64_llsc_atomics"), "baseline_llsc_cmpxchg_matches_c11_for_every_width_and_ordering_pair_o0_through_o3"), "Inst::CmpXchg", "every width and ordering pair against C11 (strong); a v48 WEAK compare-exchange is refused")
            .negative(&["Inst::CmpXchg { weak: true }", "does not model"], probe_weak_cmpxchg),
        row(I, "Fence", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_fence_null_copy_and_bool_constants_match_the_interpreter_o0_through_o3"), "Inst::Fence", "Release/Acquire/AcqRel/SeqCst fences around a stack round trip, with `dmb ish` read back from the object")
            .probe(probe_fence_orderings),
        row(I, "Br", executed(cg!("e2e_full_pipeline"), "test_full_pipeline_fibonacci_run"), "Inst::Br {", "loop back-edges with block arguments"),
        row(I, "CondBr", executed(cg!("e2e_full_pipeline"), "test_full_pipeline_fibonacci_run"), "Inst::CondBr", "loop exits with block arguments"),
        row(I, "Switch", executed(cg!("e2e_aarch64_switch"), "e2e_aarch64_switch_matches_clang"), "Inst::Switch", "dense and sparse case tables against clang"),
        row(I, "Call", executed(cg!("e2e_aarch64_variadic_call"), "e2e_aarch64_variadic_call_matches_clang"), "Inst::Call {", "direct calls including the Apple variadic tail"),
        row(I, "CallIndirect", executed(cg!("e2e_aarch64_indirect_call"), "e2e_aarch64_indirect_call_matches_clang"), "Inst::CallIndirect", "calls through function pointers"),
        row(I, "Return", executed(cg!("e2e_aarch64_switch"), "e2e_aarch64_switch_matches_clang"), "Inst::Return", "scalar returns to a C driver"),
        row(I, "ExtractField", executed(cg!("e2e_aarch64_struct_byval"), "e2e_aarch64_struct_byval_args"), "Inst::ExtractField", "field reads of by-value structs"),
        row(I, "InsertField", executed(cg!("e2e_aarch64_p1_p2_gaps"), "g7_insertfield_aggregate_field_nonpacked_matches_clang"), "Inst::InsertField", "field writes into an aggregate value"),
        row(I, "ExtractElement", executed(cg!("e2e_aarch64_vector_lane"), "e2e_aarch64_narrow_vector_extract_insert"), "Inst::ExtractElement", "vector lane reads; over a `Ty::Sequence` it is trust-ir's own `UnlowerableForCodegen` and refused by name")
            .negative(&["[TCG-SEQ]", "UnlowerableForCodegen"], probe_sequence_extract_element),
        row(I, "InsertElement", executed(cg!("e2e_aarch64_vector_lane"), "e2e_aarch64_narrow_vector_extract_insert"), "Inst::InsertElement", "vector lane writes; over a `Ty::Sequence` it is trust-ir's own `UnlowerableForCodegen` and refused by name")
            .negative(&["[TCG-SEQ]", "UnlowerableForCodegen"], probe_sequence_insert_element),
        row(I, "Const", executed(cg!("e2e_aarch64_switch"), "e2e_aarch64_switch_matches_clang"), "Inst::Const", "integer constants in every switch arm"),
        row(I, "NullPtr", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_fence_null_copy_and_bool_constants_match_the_interpreter_o0_through_o3"), "Inst::NullPtr", "returned to C as `NULL` and compared by address, against the interpreter")
            .probe(probe_null_ptr),
        row(I, "GlobalAddr", executed(cg!("e2e_aarch64_read_global"), "aarch64_read_global_links_runs_and_reads_correct_value"), "Inst::GlobalAddr", "global addresses through Mach-O relocations"),
        row(I, "Undef", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".undef(", "scalar poison materialized under the NoUndef zero model and only transported, against the reference interpreter at O0-O3: U64 poison through a plain store, copy, select arm, rebound frame slot and block argument, and nine carriers (Bool, I8, U16, I32, U64, I128, F32, F64, Ptr) through a copy and a plain store; no admitted program observes the zero natively, so the zero of every carrier is pinned at LIR level by the conformance manifest; poison reaching an inspecting use (including a volatile store), aggregate undef and a FreshSymbolicHavoc marker are refused by name")
            .probe(probe_undef_transported)
            .negative(&["[TCG-BFU]", "reaches an inspecting use in Inst::Return"], probe_undef_scalar),
        row(I, "Assume", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_assume_and_assert_pass_in_domain_and_trap_outside_it_o0_through_o3"), "Inst::Assume", "a checked runtime assertion: passes in domain, traps natively where the interpreter answers `AssumeViolated`"),
        row(I, "Assert", refused(&["unspecified panic kind", "require_assert_panic_kinds"], SELF_FILE, "refused_rows_are_refused_by_the_adapter_by_name"), "Inst::Assert", "v52 unknown panic identity is refused; stated kinds also refuse until faithful runtime payload/location/hook/cleanup lowering exists. Historical trap-only native evidence is not v52 panic execution")
            .probe(probe_assert_panic),
        row(I, "Unreachable", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_never_callee_and_unreachable_trap_where_the_interpreter_refuses_o0_through_o3"), "Inst::Unreachable", "a reached `Unreachable` traps natively where the interpreter answers undefined behaviour"),
        row(I, "Copy", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_fence_null_copy_and_bool_constants_match_the_interpreter_o0_through_o3"), "Inst::Copy", "chained SSA copies, against the interpreter and C"),
        row(I, "Select", executed(cg!("e2e_aarch64_p0_miscompiles"), "g2_float_select_matches_clang"), "Inst::Select", "float select against clang"),
        row(I, "SeqMapAddK", executed(cg!("e2e_aarch64_sequences"), "seq_map_family_matches_the_interpreter_and_a_c_model_o0_through_o3"), "Inst::SeqMapAddK", "a counted loop into a fresh image, wrapping at every integer width; non-integer elements are refused by name")
            .probe(probe_seq_map_add_k)
            .negative(&["[TCG-SEQ]", "integer elements"], probe_seq_map_add_k_float),
        row(I, "SeqMapNot", executed(cg!("e2e_aarch64_sequences"), "seq_map_family_matches_the_interpreter_and_a_c_model_o0_through_o3"), "Inst::SeqMapNot", "a counted loop negating Bool elements; other elements are refused by name")
            .probe(probe_seq_map_not)
            .negative(&["[TCG-SEQ]", "Bool elements"], probe_seq_map_not_int),
        row(I, "SeqMap", executed(cg!("e2e_aarch64_sequences"), "seq_map_family_matches_the_interpreter_and_a_c_model_o0_through_o3"), "Inst::SeqMap {", "a counted loop calling `fwd(&mut element)` through a fresh cell per element that stays allocated for the frame; an element function that is not `fn(&mut elem)` is refused by name")
            .probe(probe_seq_map)
            .negative(&["[TCG-SEQ]", "SeqMapFwdSignatureMismatch"], probe_seq_map_bad_fwd),
        row(I, "Borrow", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".borrow(", "shared borrows and reborrows of stack and global cells, and of fat slice pointers to a stack and a global array, lowered as value-preserving copies with their root recorded, read through natively; a borrow of a non-pointer is refused")
            .probe(probe_borrow)
            .negative(&["[TCG-BFU]", "non-addressable"], probe_borrow_non_pointer),
        row(I, "BorrowMut", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".borrow_mut(", "unique borrows and unique reborrows (thin, and of a fat slice pointer) written through natively; a unique reborrow of a shared borrow is refused (BorrowMutThroughSharedRef)")
            .probe(probe_borrow_mut)
            .negative(&["[TCG-BFU]", "BorrowMutThroughSharedRef"], probe_borrow_mut_of_shared),
        row(I, "EndBorrow", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".end_borrow(", "borrow retirement emits nothing and is recorded; an EndBorrow of a non-borrow is refused")
            .probe(probe_end_borrow_of_borrow)
            .negative(&["[TCG-BFU]", "EndBorrowOfNonBorrow"], probe_end_borrow),
        row(I, "Retain", model_only(MANIFEST, "check_retain_lowered_via_clean_rc_triple"), "Inst::Retain", "lowers to the module-declared Clean RC runtime; refused without one; no native Darwin execution; natively executed only on Linux AArch64 by `e2e_aarch64_arc_ops_linux` (`native_arc_ops_match_the_interpreter_and_balance_the_counting_runtime_o0_through_o3`, compiled out on Darwin) against a C counting runtime standing in for Clean's; those cells are CMalloc/RustHeap, on which trust-ir calls the op undefined, so that row tests the lowering, and the interpreter oracle runs the corpus's CleanHeap twin")
            .negative(&["declares no RC runtime"], probe_retain_without_runtime),
        row(I, "Release", model_only(MANIFEST, "check_release_lowered_via_clean_rc_triple"), "Inst::Release", "lowers to the module-declared Clean RC runtime; refused without one; no native Darwin execution; natively executed only on Linux AArch64 by `e2e_aarch64_arc_ops_linux` (`native_arc_ops_match_the_interpreter_and_balance_the_counting_runtime_o0_through_o3`, compiled out on Darwin) against a C counting runtime standing in for Clean's; those cells are CMalloc/RustHeap, on which trust-ir calls the op undefined, so that row tests the lowering, and the interpreter oracle runs the corpus's CleanHeap twin")
            .negative(&["declares no RC runtime"], probe_release_without_runtime),
        row(I, "IsUnique", model_only(MANIFEST, "check_is_unique_lowered_via_clean_rc_triple"), "Inst::IsUnique", "lowers to the module-declared Clean RC runtime; refused without one; no native Darwin execution; natively executed only on Linux AArch64 by `e2e_aarch64_arc_ops_linux` (`native_arc_ops_match_the_interpreter_and_balance_the_counting_runtime_o0_through_o3`, compiled out on Darwin) against a C counting runtime standing in for Clean's; those cells are CMalloc/RustHeap, on which trust-ir calls the op undefined, so that row tests the lowering, and the interpreter oracle runs the corpus's CleanHeap twin")
            .negative(&["declares no RC runtime"], probe_is_unique_without_runtime),
        row(I, "Dealloc", refused(&["[TCG-DEALLOC]", "UnlowerableForCodegen"], LW_DEALLOC, "every_formerly_lowered_dealloc_shape_is_refused"), "Inst::Dealloc", "G18-1 (re-decided 2026-09-27): names only a pointer, neither the owning runtime nor the layout; trust-ir refuses every one for codegen in every body and so does this backend, which recovers neither from dataflow (the provenance lowering, 2887cbf01, is retired)")
            .probe(probe_dealloc_of_a_same_function_heap_alloc),
        row(I, "OpenFrame", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".open_frame(", "one zero-filled stack slot per frame laid out from its scalar slot carriers, including two frames live at once and a loop-carried frame; an escaping handle, a handle reaching an entry-block parameter, a non-scalar slot or an unclosed frame is refused")
            .probe(probe_frame_program)
            .negative(&["[TCG-BFU]", "escapes into Inst::Return"], probe_open_frame),
        row(I, "BindSlot", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".bind_slot(", "in-place slot stores of mixed-width values across blocks, admitted only where no superseded handle stays live; a bind through a value no OpenFrame produced is refused")
            .probe(probe_frame_program)
            .negative(&["[TCG-BFU]", "BindingFrameNotOpen"], probe_bind_slot),
        row(I, "LoadSlot", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".load_slot(", "typed slot loads through block-parameter handles; a load through a value no OpenFrame produced is refused")
            .probe(probe_frame_program)
            .negative(&["[TCG-BFU]", "BindingFrameNotOpen"], probe_load_slot),
        row(I, "CloseFrame", executed(cg!("e2e_aarch64_borrows_frames"), "native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3"), ".close_frame(", "lifetime marker with no runtime effect on every exit path; a close of a value no OpenFrame produced is refused")
            .probe(probe_frame_program)
            .negative(&["[TCG-BFU]", "BindingFrameUnopened"], probe_close_frame_non_frame),
        row(I, "CoroSuspend", executed(cg!("e2e_aarch64_coroutine"), "coroutine_generator_links_runs_and_yields_sequence"), "Inst::CoroSuspend", "generator yields through the state-machine expansion"),
        row(I, "Invoke", executed(cg!("e2e_aarch64_eh_invoke_trust_ir"), "eh_invoke_trust_ir_link_and_run_catches"), "Inst::Invoke", "throwing call with a landing pad, caught natively"),
        row(I, "LandingPad", executed(cg!("e2e_aarch64_eh_invoke_trust_ir"), "eh_invoke_trust_ir_link_and_run_catches"), "Inst::LandingPad", "handler entry reading the unwinder registers"),
        row(I, "Resume", executed(cg!("e2e_aarch64_eh_resume_trust_ir"), "eh_resume_trust_ir_link_and_run_propagates_to_enclosing_catch"), "Inst::Resume", "re-raise from a cleanup pad to an enclosing catch"),
        row(I, "DialectOp", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_vector_dialect_ops_match_the_interpreter_o0_through_o3"), "Inst::DialectOp", "the vector dialect's `pack_lanes`/`insert_lane`/`extract_lane` on `<4 x i32>`, against the interpreter and C; the adapter refuses `shuffle`/`reduce`/`fma` and unknown namespaces, which the codegen's dialect legalization rewrites (`dialect_legalization_corpus`) or refuses by name before the adapter")
            .negative(&["DialectOp reached"], probe_unknown_dialect_op),
        row(I, "MakeClosure", executed(cg!("e2e_aarch64_make_closure"), "runtime_captures_execute_with_pointer_identity_and_value_semantics"), "Inst::MakeClosure", "runtime pointer capture construction, copied and updated environments, aliasing stores and native calls at O0-O3; proof-subset admission remains separate")
            .negative(&["Inst::MakeClosure", "does not model", "runtime closure ABI"], probe_make_closure),
        row(I, "MakeAggregate", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_make_aggregate_builds_structs_tuples_arrays_and_nests_o0_through_o3"), "Inst::MakeAggregate", "natural, declared-reordered, packed and typed-reference-lane structs, records, tuples, arrays and nests, read back, passed by value, returned and stored for C, against the interpreter and C; typed direct/niche enum variants execute in result_aggregate_native; unknown raw-pointer niche validity stays refused")
            .probe(probe_make_aggregate)
            .negative(&["Inst::MakeAggregate", "no typed nonreserved"], probe_make_aggregate_enum),
        row(I, "Drop", refused(&["Inst::Drop", "does not model", "destructor"], SELF_FILE, REFUSAL_GATE), "Inst::Drop", "v47: runs the dropped type's destructor; no lane models one, and a no-op would compile a different program")
            .probe(probe_drop),
        row(I, "CallCannotUnwind", refused(&["Inst::CallCannotUnwind", "does not model", "unwind"], SELF_FILE, REFUSAL_GATE), "Inst::CallCannotUnwind", "v53 direct call with a non-propagating unwind boundary, enforce-or-refuse: no lane emits the abort-on-unwind call-site range, and an ordinary call would let an unwind cross it")
            .probe(probe_call_cannot_unwind),
        row(I, "CallIndirectCannotUnwind", refused(&["Inst::CallIndirectCannotUnwind", "does not model", "unwind"], SELF_FILE, REFUSAL_GATE), "Inst::CallIndirectCannotUnwind", "v53 indirect twin of CallCannotUnwind, refused for the same reason")
            .probe(probe_call_indirect_cannot_unwind),
        row(I, "AssertInvoke", model_only(SELF_FILE, "positive_probes_lower_through_the_adapter"), "Inst::AssertInvoke", "v54 real native entry/payload/location call and original unwind pad; Core/JIT and WASM source authority remain refused; new native runtime controls are UNRUN")
            .probe(probe_assert_invoke),
        row(I, "DropInvoke", refused(&["Inst::DropInvoke", "does not model", "drop glue"], SELF_FILE, REFUSAL_GATE), "Inst::DropInvoke", "v55 drop with an unwind edge (amendment D): resolved through the drop-glue table it IS an Invoke of the type's glue; no lane lowers a drop, and a branch to its normal edge would compile a different program")
            .probe(probe_drop_invoke),
        row(I, "InvokeIndirect", refused(&["Inst::InvokeIndirect", "does not model", "landing pad"], SELF_FILE, REFUSAL_GATE), "Inst::InvokeIndirect", "v56 indirect call with an unwind edge (amendment D Part 2): no lane emits the call-site range that routes an indirect callee's unwind to its pad, and an ordinary indirect call would let an unwind skip it")
            .probe(probe_invoke_indirect),
        row(I, "ArraySplat", executed(cg!("e2e_aarch64_construct_sweep_insts"), "native_array_splat_and_splat_constants_fill_every_lane_o0_through_o3"), "Inst::ArraySplat", "v50 `[v; n]` from a register: a mixed-byte lane stored once then doubled, a byte-uniform constant register as one memset, a tuple lane copied then doubled, each read back by a runtime index against the interpreter and C; the lowering is constant-size in n (`array_splat_lowering`); a non-array type is refused")
            .probe(probe_array_splat)
            .negative(&["Inst::ArraySplat", "not an array"], probe_array_splat_non_array),
    ]
}

fn constant_rows() -> Vec<Row> {
    use Family::Constant as C;
    vec![
        row(
            C,
            "Int",
            executed(
                cg!("e2e_aarch64_switch"),
                "e2e_aarch64_switch_matches_clang",
            ),
            "Constant::Int",
            "integer literals in every arm",
        ),
        row(
            C,
            "U128",
            executed(
                cg!("e2e_aarch64_i128_switch"),
                "e2e_aarch64_i128_switch_and_checked_mul_match_clang",
            ),
            "Constant::U128",
            "canonical upper-half u128 case constants",
        ),
        row(
            C,
            "Bytes",
            executed(
                cg!("e2e_aarch64_nested_bytes"),
                "native_direct_tag_enum_nested_utf8_bytes_o0_through_o3",
            ),
            "Constant::Bytes",
            "UTF-8 byte payloads nested in an enum",
        ),
        row(
            C,
            "Float",
            executed(
                cg!("e2e_aarch64_global_var"),
                "e2e_aarch64_global_var_matches_clang",
            ),
            "Constant::Float",
            "a double global initializer read natively",
        ),
        row(
            C,
            "Bool",
            executed(
                cg!("e2e_aarch64_construct_sweep_insts"),
                "native_fence_null_copy_and_bool_constants_match_the_interpreter_o0_through_o3",
            ),
            "Constant::Bool",
            "true/false constants steering selects and returned as C `bool`",
        ),
        row(
            C,
            "Aggregate",
            executed(
                cg!("e2e_aarch64_read_global"),
                "aarch64_read_global_links_runs_and_reads_correct_value",
            ),
            "Constant::Aggregate",
            "aggregate global initializer read natively",
        ),
        row(
            C,
            "Array",
            executed(
                cg!("e2e_aarch64_nested_bytes"),
                "native_nested_array_bytes_o0_through_o3",
            ),
            "Constant::Array",
            "array literals nested in tuples",
        ),
        row(
            C,
            "Vector",
            executed(
                cg!("e2e_aarch64_vector_types_linux"),
                "native_integer_vector_carriers_and_unsigned_constants_o0_through_o3",
            ),
            "Constant::Vector",
            "vector literals at every lane width through the shared native harness",
        ),
        row(
            C,
            "Sequence",
            executed(
                cg!("e2e_aarch64_sequences"),
                "sequence_constants_of_every_element_type_return_through_the_abi_o0_through_o3",
            ),
            "Constant::Sequence",
            "the length-prefixed `sequence_layout` image of every admitted element type, returned through the result-buffer ABI",
        ),
        row(
            C,
            "Set",
            executed(
                cg!("e2e_aarch64_sequences"),
                "boxed_sets_move_as_constants_parameters_and_results_o0_through_o3",
            ),
            "Constant::Set",
            "the constructor-ordered image of a boxed set; two elements that store one image are refused by name",
        )
        .probe(probe_set_constant)
        .negative(
            &["[TCG-SEQ]", "repeats an element"],
            probe_set_constant_repeated,
        ),
        row(
            C,
            "Record",
            executed(
                cg!("e2e_aarch64_construct_sweep_types"),
                "native_records_over_the_records_table_match_the_interpreter_o0_through_o3",
            ),
            "Constant::Record",
            "materialized through its `RecordDef`, passed by value and projected, against the interpreter",
        ),
        row(
            C,
            "Closure",
            executed(
                cg!("e2e_aarch64_closures"),
                "closure_with_one_capture_applies_by_value_at_every_level",
            ),
            "Constant::Closure",
            "closure literal with a captured value applied natively",
        ),
        row(
            C,
            "FnDef",
            executed(
                cg!("e2e_aarch64_closures"),
                "nested_closure_fndef_and_symbol_addr_constants_materialize_at_every_level",
            ),
            "Constant::FnDef",
            "bare function items reified and called",
        )
        .negative(
            &["const type mismatch: expected a unique module-owned function item, got missing or ambiguous func.99"],
            probe_fndef_unregistered,
        ),
        row(
            C,
            "SymbolAddr",
            executed(
                cg!("e2e_aarch64_data_reloc"),
                "aarch64_data_reloc_links_runs_and_calls_through_pointer",
            ),
            "Constant::SymbolAddr",
            "data-section relocation to a function address, called natively",
        ),
        row(
            C,
            "PhantomData",
            model_only(MANIFEST, "check_phantom_unit_constant_supported"),
            "Constant::PhantomData",
            "trust-ir's one spelling of `()`'s value, lowered as the zero-sized `()` the empty aggregate was before typed admission refused `{ }` there; no native Darwin execution (`e2e_aarch64_aggregate_insert_linux` and `e2e_aarch64_closures` compile it at every level)",
        )
        .probe(probe_phantom_constant)
        .negative(
            &["const type mismatch: expected i64, got phantomdata"],
            probe_phantom_non_unit,
        ),
        row(
            C,
            "Uninit",
            refused(
                &["Constant::Uninit", "does not model", "unwritten"],
                SELF_FILE,
                REFUSAL_GATE,
            ),
            "Constant::Uninit",
            "v49 unwritten aggregate lane: holds no value, so no bytes may stand for it",
        )
        .probe(probe_uninit_lane),
        row(C, "TensorBlob", refused(&["Ty::Tensor", "no native layout"], SELF_FILE, REFUSAL_GATE), "Constant::TensorBlob", "content-addressed tensor input lacks native input/provider semantics").probe(probe_tensor_blob_constant),
        row(
            C,
            "Splat",
            executed(
                cg!("e2e_aarch64_construct_sweep_insts"),
                "native_array_splat_and_splat_constants_fill_every_lane_o0_through_o3",
            ),
            "Constant::Splat",
            "v50 uniform array constant: byte-uniform (one memset), mixed-byte, float, a splat of splats, a tuple field and two global tables, each read back by a runtime index against the interpreter and C; the lowering is constant-size in n (`array_splat_lowering`); a non-array type is refused",
        )
        .probe(probe_splat_constant)
        .negative(
            &["const type mismatch: expected u32, got splat[2]"],
            probe_splat_constant_non_array,
        ),
    ]
}

fn cast_op_rows() -> Vec<Row> {
    use Family::CastOp as O;
    vec![
        row(
            O,
            "Trunc",
            executed(
                cg!("e2e_aarch64_narrow_signed_cmp"),
                "e2e_aarch64_narrow_signed_compare",
            ),
            "CastOp::Trunc",
            "narrowing before signed compares",
        ),
        row(
            O,
            "ZExt",
            executed(
                cg!("e2e_aarch64_i128_icmp"),
                "e2e_aarch64_i128_icmp_matches_clang",
            ),
            "CastOp::ZExt",
            "Bool results widened for the C driver",
        ),
        row(
            O,
            "SExt",
            executed(
                cg!("e2e_aarch64_struct_byval"),
                "e2e_aarch64_struct_byval_args",
            ),
            "CastOp::SExt",
            "sign extension of narrow struct fields",
        ),
        row(
            O,
            "FPTrunc",
            executed(
                cg!("e2e_aarch64_f16_fcvt"),
                "cg_compiled_fcvt_matches_the_hardware_instruction_bit_for_bit",
            ),
            "CastOp::FPTrunc",
            "each fcvt narrowing form against the hardware instruction",
        ),
        row(
            O,
            "FPExt",
            executed(
                cg!("e2e_aarch64_f16_fcvt"),
                "cg_compiled_fcvt_matches_the_hardware_instruction_bit_for_bit",
            ),
            "CastOp::FPExt",
            "each fcvt widening form against the hardware instruction",
        ),
        row(
            O,
            "FPToUI",
            executed(cg!("e2e_aarch64_f16_to_i128"), "e2e_aarch64_f16_to_i128"),
            "CastOp::FPToUI",
            "half to u128 through the libcall path",
        ),
        row(
            O,
            "FPToSI",
            executed(
                cg!("e2e_aarch64_fp_to_int"),
                "e2e_aarch64_fptosi_fptoui_in_range",
            ),
            "FPToSI",
            "in-range float-to-int at every width",
        ),
        row(
            O,
            "UIToFP",
            executed(
                cg!("e2e_aarch64_p0_miscompiles"),
                "g4_uitofp_narrow_u16_matches_clang",
            ),
            "CastOp::UIToFP",
            "narrow unsigned source with dirty high bits",
        ),
        row(
            O,
            "SIToFP",
            executed(
                cg!("e2e_aarch64_struct_byval"),
                "e2e_aarch64_struct_byval_args",
            ),
            "CastOp::SIToFP",
            "signed field converted to double",
        ),
        row(
            O,
            "PtrToInt",
            executed(cg!("e2e_full_pipeline"), "test_full_pipeline_sum_array_run"),
            "CastOp::PtrToInt",
            "pointer arithmetic through an integer carrier",
        ),
        row(
            O,
            "IntToPtr",
            executed(cg!("e2e_full_pipeline"), "test_full_pipeline_sum_array_run"),
            "CastOp::IntToPtr",
            "pointer arithmetic through an integer carrier",
        ),
        row(
            O,
            "PtrToPtr",
            executed(
                cg!("e2e_aarch64_construct_sweep_casts"),
                "native_ptr_to_ptr_and_bitcast_match_the_interpreter_and_c_o0_through_o3",
            ),
            "CastOp::PtrToPtr",
            "`Ptr` -> `*mut u64` -> `&u64` -> `Ptr` retypes stored and loaded through",
        ),
        row(
            O,
            "Bitcast",
            executed(
                cg!("e2e_aarch64_construct_sweep_casts"),
                "native_ptr_to_ptr_and_bitcast_match_the_interpreter_and_c_o0_through_o3",
            ),
            "CastOp::Bitcast",
            "integer/float reinterpretations (with a NaN payload and a sign flip) against the interpreter and C",
        ),
        row(
            O,
            "Transmute",
            executed(
                cg!("e2e_aarch64_construct_sweep_casts"),
                "native_transmute_reinterprets_scalars_vectors_and_structs_o0_through_o3",
            ),
            "CastOp::Transmute",
            "equal-size reinterpretation under trust-ir's layouts: integer/pointer scalars against the interpreter; integer/float, integer/vector and struct/byte shapes against the interpreter's Bitcast or store/load twin (it refuses those Transmute spellings) and C memcpy; unequal sizes, validity-carrying leaves and source padding are refused",
        )
        .probe(probe_transmute)
        .negative(
            &["CastOp::Transmute", "layout sizes differ"],
            probe_transmute_size_mismatch,
        ),
        row(
            O,
            "ReifyFnPointer",
            executed(
                cg!("e2e_aarch64_macho_dylib"),
                "dlopen_sees_exports_not_hidden_coalesces_weak_and_write_protects_data_const",
            ),
            "CastOp::ReifyFnPointer",
            "reified weak function address exported from a dylib and called by the dlopen driver",
        ),
        row(
            O,
            "FPToSISat",
            executed(
                cg!("e2e_aarch64_fptosi_sat"),
                "e2e_aarch64_register_width_saturating_casts",
            ),
            "CastOp::FPToSISat",
            "saturating signed casts against Rust `as`",
        ),
        row(
            O,
            "FPToUISat",
            executed(
                cg!("e2e_aarch64_fptosi_sat"),
                "e2e_aarch64_register_width_saturating_casts",
            ),
            "CastOp::FPToUISat",
            "saturating unsigned casts against Rust `as`",
        ),
    ]
}

fn module_table_rows() -> Vec<Row> {
    use Family::ModuleTable as M;
    vec![
        row(M, "name", executed(cg!("e2e_aarch64_switch"), "e2e_aarch64_switch_matches_clang"), "Module::new(", "module identity carried into the object"),
        row(M, "functions", executed(cg!("e2e_aarch64_switch"), "e2e_aarch64_switch_matches_clang"), "add_function", "function definitions"),
        row(M, "structs", executed(cg!("e2e_aarch64_struct_byval"), "e2e_aarch64_struct_byval_args"), "structs", "struct definitions with producer layouts"),
        row(M, "enums", executed(cg!("e2e_aarch64_direct_enums"), "native_direct_enums_agree_with_the_c_oracle_and_the_interpreter_o0_through_o3"), "enums", "enum definitions with explicit discriminants and layouts"),
        row(M, "records", executed(cg!("e2e_aarch64_construct_sweep_types"), "native_records_over_the_records_table_match_the_interpreter_o0_through_o3"), "add_record", "record definitions lay out a record constant, a by-value record argument and its field projections natively"),
        row(M, "closure_types", executed(cg!("e2e_aarch64_closures"), "closure_with_one_capture_applies_by_value_at_every_level"), "add_closure_type", "closure type table with typed captures"),
        row(M, "globals", executed(cg!("e2e_aarch64_read_global"), "aarch64_read_global_links_runs_and_reads_correct_value"), "globals", "data globals with initializers"),
        row(M, "globals.tls", executed(cg!("e2e_aarch64_concurrency"), "thread_locals_initialize_per_thread_across_waves_and_match_the_c_view"), "tls: Some(", "thread-local globals through Mach-O TLV across threads"),
        row(M, "func_types", executed(cg!("e2e_aarch64_indirect_call"), "e2e_aarch64_indirect_call_matches_clang"), "add_func_type", "function signatures for definitions and indirect edges"),
        row(M, "types", executed(cg!("e2e_aarch64_nested_bytes"), "native_nested_array_bytes_o0_through_o3"), "add_type", "type table behind `Ty::Array`"),
        row(M, "proof_obligations", model_only(cg!("e2e_aarch64_construct_sweep_tables"), "inert_tables_leave_the_native_artifact_byte_identical_o0_through_o3"), "proof_obligations", "carried and claims nothing; no native row because it has no artifact effect: a module carrying pending and discharged rows emits the byte-identical object of the same module without them, and runs"),
        row(M, "proof_certificates", model_only(cg!("e2e_aarch64_construct_sweep_tables"), "inert_tables_leave_the_native_artifact_byte_identical_o0_through_o3"), "proof_certificates", "carried; a `Trusted` certificate draws no codegen decision (the object is byte-identical without it); external inheritance is refused (pin_move_floor)")
            .probe(probe_proof_tables),
        row(M, "target_info", executed(cg!("e2e_aarch64_direct_enums"), "native_direct_enums_agree_with_the_c_oracle_and_the_interpreter_o0_through_o3"), "target_info", "producer target stamp preserved to the Darwin backend"),
        row(M, "files", executed(cg!("e2e_aarch64_construct_sweep_tables"), "native_files_table_names_the_dwarf_source_of_a_running_program_o0_through_o3"), "intern_file", "the interned path is the source the object's DWARF line program and compile unit name (dwarfdump), absent without the table, for a program that runs")
            .probe(probe_source_file_table),
        row(M, "obligation_diagnostics", model_only(cg!("e2e_aarch64_construct_sweep_tables"), "inert_tables_leave_the_native_artifact_byte_identical_o0_through_o3"), "obligation_diagnostics", "verifier sidecar carried inert, no authority drawn; no native row because it has no artifact effect (byte-identical object)")
            .probe(probe_inert_sidecar_tables),
        row(M, "spec_modules", model_only(cg!("e2e_aarch64_construct_sweep_tables"), "inert_tables_leave_the_native_artifact_byte_identical_o0_through_o3"), "spec_modules", "spec cross-reference objects carried inert, no authority drawn; no native row because they have no artifact effect (byte-identical object)")
            .probe(probe_inert_sidecar_tables),
        row(M, "universes", model_only(SELF_FILE, "probe_universe_refinement"), ".universes", "content-interned universes behind `Pred::InUniverse` on a refined carrier; no native row: the refined carrier executes natively (`Ty::Refine`), but no floor test observes an artifact decision drawn from a universe")
            .probe(probe_universe_refinement),
        row(M, "predicates", model_only(MANIFEST, "check_refine_type_supported"), "intern_pred", "content-interned predicates behind `Ty::Refine`; no native row: the refined carrier executes natively (`Ty::Refine`), but no floor test observes an artifact decision drawn from a predicate"),
        row(M, "global_asm", refused(&["global_asm!", "cannot assemble"], PIN_MOVE, "every_refused_field_is_refused_by_its_own_name"), "global_asm", "opaque module-level assembly is refused rather than dropped")
            .probe(probe_global_asm),
        row(M, "imports", model_only(cg!("e2e_aarch64_construct_sweep_tables"), "inert_tables_leave_the_native_artifact_byte_identical_o0_through_o3"), "intern_import", "dependency table carried inert (byte-identical object); external proof inheritance through it is refused (pin_move_floor)")
            .probe(probe_inert_sidecar_tables),
        row(M, "tuple_layouts", executed(cg!("declared_tuple_layout"), "verify_c13_l1_rust_tuple_module_with_declared_layout_runs_to_1002"), "tuple_layouts", "declared tuple layouts admitted in the flat pointer-transport profile (no offset consulted) and, by value, when each row EQUALS the declaration-order layout the byte path emits (WS7.7); a disagreeing row is refused, never substituted. Executed: the producer's c13 tuple module JIT-runs at O0-O3 against the interpreter in the Darwin floor target `declared_tuple_layout`")
            .probe(probe_tuple_layouts_by_value_agreeing)
            .negative(&["declared layout of tuple", "disagrees with the declaration-order layout"], probe_tuple_layouts_by_value_reordered),
        row(M, "completeness", refused(&["Module.completeness", "no binary format version"], PIN_MOVE, "completeness_claims_are_refused_even_when_well_formed"), "completeness", "every complete or partial claim is refused until native binary identity can represent it; None remains no claim")
            .probe(probe_completeness_claim),
        row(M, "drop_glue", model_only(SELF_FILE, "probe_drop_glue_table"), "drop_glue", "v55 drop-glue table (amendment D) carried inert: it resolves only Drop / DropInvoke sites, every one refused by name, and a registered glue is an ordinary function reached through its address; a drop at a registered type is still refused")
            .probe(probe_drop_glue_table)
            .negative(&["Inst::Drop", "does not model", "destructor"], probe_drop_at_a_registered_type),
        row(M, "closure_layouts", executed(cg!("e2e_aarch64_make_closure"), "declared_constant_closure_offsets_execute_natively_and_match_c_bytes"), "closure_layouts", "v58 declared reordered capture offsets drive native reads and writes; alignment/extent/nonoverlap and native carrier ABI totals remain checked, with unsupported totals refused")
            .probe(probe_declared_closure_layouts),
        row(M, "blobs", refused(&["Module::blobs", "does not model"], SELF_FILE, REFUSAL_GATE), "blobs", "v70 weight blob table: the bytes a `Constant::TensorBlob` names; no lane places tensor elements, so a non-empty table is refused, referenced or not")
            .probe(probe_blob_table),
    ]
}

fn all_rows() -> Vec<Row> {
    let mut rows = ty_rows();
    rows.extend(inst_rows());
    rows.extend(constant_rows());
    rows.extend(cast_op_rows());
    rows.extend(module_table_rows());
    rows
}

// ---------------------------------------------------------------------------
// Minimal-module builders and probes.
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn module_with_blocks(
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    blocks: Vec<TrustIrBlock>,
) -> TrustIrModule {
    let entry = blocks.first().map(|block| block.id).unwrap_or_else(|| b(0));
    let mut module = TrustIrModule::new(name);
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), name, ty, entry);
    func.blocks = blocks;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn single_inst_module(
    name: &str,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    inst: InstrNode,
    return_values: Vec<ValueId>,
) -> TrustIrModule {
    module_with_blocks(
        name,
        params.iter().map(|(_, ty)| ty.clone()).collect(),
        returns,
        vec![TrustIrBlock {
            id: b(0),
            params,
            body: vec![
                inst,
                InstrNode::new(Inst::Return {
                    values: return_values,
                }),
            ],
        }],
    )
}

fn const_module(name: &str, ty: Ty, value: Constant) -> TrustIrModule {
    single_inst_module(
        name,
        vec![],
        vec![ty.clone()],
        InstrNode::new(Inst::Const { ty, value }).with_result(v(0)),
        vec![v(0)],
    )
}

fn translate_single(module: &TrustIrModule) -> Result<LirFunction, String> {
    let func = module
        .functions
        .first()
        .ok_or_else(|| "probe module has no function".to_string())?;
    trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
        .map(|(func, _proofs)| func)
        .map_err(|err| err.to_string())
}

fn lowered(module: &TrustIrModule, what: &str) -> Result<String, String> {
    translate_single(module).map(|func| format!("{what}: {} LIR block(s)", func.blocks.len()))
}

fn lowered_module(module: &TrustIrModule, what: &str) -> Result<String, String> {
    permit_translate_module(module)
        .map(|funcs| format!("{what}: {} function(s)", funcs.len()))
        .map_err(|err| err.to_string())
}

fn type_lowers(ty: &Ty, what: &str) -> Result<String, String> {
    translate_type(ty)
        .map(|lir| format!("{what}: {lir:?}"))
        .map_err(|err| err.to_string())
}

fn probe_storage_value() -> Result<String, String> {
    type_lowers(
        &Ty::Storage(trust_ir::StorageLayout::new(80, 8)),
        "Ty::Storage",
    )
}

fn probe_error_type() -> Result<String, String> {
    type_lowers(&Ty::Error, "Ty::Error")
}

fn probe_tensor_type() -> Result<String, String> {
    let mut module = TrustIrModule::new("inventory_unused_tensor_signature");
    module.func_types.push(FuncTy {
        params: vec![Ty::Tensor(Box::new(Ty::I32), 2)],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    lowered_module(&module, "unused Ty::Tensor signature")
}

fn probe_tensor_contract() -> Result<String, String> {
    let tensor = Ty::Tensor(Box::new(Ty::I32), 2);
    lowered(
        &single_inst_module(
            "inventory_tensor_contract",
            vec![(v(0), tensor.clone()), (v(1), tensor.clone())],
            vec![tensor.clone()],
            InstrNode::new(Inst::TensorContract {
                ty: tensor,
                lhs: v(0),
                rhs: v(1),
                batch: vec![],
                contract: vec![(1, 0)],
            })
            .with_result(v(2)),
            vec![v(2)],
        ),
        "Inst::TensorContract",
    )
}

fn tensor_probe(
    name: &str,
    params: Vec<(ValueId, Ty)>,
    result: Ty,
    inst: Inst,
    what: &str,
) -> Result<String, String> {
    let result_value = v(u32::try_from(params.len()).expect("probe arity"));
    lowered(
        &single_inst_module(
            name,
            params,
            vec![result],
            InstrNode::new(inst).with_result(result_value),
            vec![result_value],
        ),
        what,
    )
}

fn probe_tensor_map() -> Result<String, String> {
    let tensor = Ty::Tensor(Box::new(Ty::I32), 1);
    tensor_probe(
        "inventory_tensor_map",
        vec![(v(0), tensor.clone()), (v(1), tensor.clone())],
        tensor.clone(),
        Inst::TensorMap {
            ty: tensor,
            args: vec![v(0), v(1)],
            body: vec![trust_ir::TensorMapNode::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I32,
                lhs: 0,
                rhs: 1,
            }],
        },
        "Inst::TensorMap",
    )
}

fn probe_tensor_reduce() -> Result<String, String> {
    let result = Ty::Tensor(Box::new(Ty::I32), 1);
    tensor_probe(
        "inventory_tensor_reduce",
        vec![(v(0), Ty::Tensor(Box::new(Ty::I32), 2))],
        result.clone(),
        Inst::TensorReduce {
            ty: result,
            src: v(0),
            op: trust_ir::TensorReduceOp::Add,
            axes: vec![1],
            order: trust_ir::TensorReduceOrder::RowMajor,
        },
        "Inst::TensorReduce",
    )
}

fn probe_tensor_view() -> Result<String, String> {
    use trust_ir::TensorIndexExpr as X;
    let tensor = Ty::Tensor(Box::new(Ty::I32), 2);
    tensor_probe(
        "inventory_tensor_view",
        vec![(v(0), tensor.clone())],
        tensor.clone(),
        // A transpose: the result's extents are the source's swapped, and
        // result coordinate (i, j) reads source coordinate (j, i).
        Inst::TensorView {
            ty: tensor,
            src: v(0),
            params: vec![],
            exprs: vec![X::SrcExtent(1), X::SrcExtent(0), X::Coord(1), X::Coord(0)],
            shape: vec![0, 1],
            index: vec![2, 3],
            fill: None,
        },
        "Inst::TensorView",
    )
}

fn probe_tensor_gather() -> Result<String, String> {
    let tensor = Ty::Tensor(Box::new(Ty::I32), 1);
    tensor_probe(
        "inventory_tensor_gather",
        vec![
            (v(0), tensor.clone()),
            (v(1), Ty::Tensor(Box::new(Ty::I64), 1)),
        ],
        tensor.clone(),
        Inst::TensorGather {
            ty: tensor,
            data: v(0),
            coords: vec![v(1)],
        },
        "Inst::TensorGather",
    )
}

fn probe_tensor_scatter() -> Result<String, String> {
    let tensor = Ty::Tensor(Box::new(Ty::I32), 1);
    tensor_probe(
        "inventory_tensor_scatter",
        vec![
            (v(0), tensor.clone()),
            (v(1), tensor.clone()),
            (v(2), Ty::Tensor(Box::new(Ty::I64), 1)),
        ],
        tensor.clone(),
        Inst::TensorScatter {
            ty: tensor,
            init: v(0),
            src: v(1),
            coords: vec![v(2)],
        },
        "Inst::TensorScatter",
    )
}

fn probe_rc_type() -> Result<String, String> {
    type_lowers(&Ty::Rc(Box::new(Ty::I64)), "Ty::Rc")
}

fn probe_dialect_type() -> Result<String, String> {
    type_lowers(
        &Ty::Dialect(Box::new(DialectTy::new("tla", "Value", 1))),
        "Ty::Dialect",
    )
}

fn probe_never_value_slot() -> Result<String, String> {
    type_lowers(&Ty::Never, "Ty::Never")
}

fn identity_module(name: &str, ty: Ty) -> TrustIrModule {
    let mut module = module_with_blocks(
        name,
        vec![ty.clone()],
        vec![ty.clone()],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), ty)],
            body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
        }],
    );
    module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    module
}

fn probe_set_type() -> Result<String, String> {
    lowered(
        &identity_module("inventory_set_type", Ty::Set(TyId::new(0), SetRepr::Boxed)),
        "Ty::Set value slot",
    )
}

fn probe_sequence_type() -> Result<String, String> {
    lowered(
        &identity_module("inventory_sequence_type", Ty::Sequence(TyId::new(0))),
        "Ty::Sequence value slot",
    )
}

fn probe_set_bitset_type() -> Result<String, String> {
    lowered(
        &identity_module(
            "inventory_set_bitset_type",
            Ty::Set(TyId::new(0), SetRepr::Bitset),
        ),
        "Ty::Set bitset value slot",
    )
}

fn probe_nested_sequence_type() -> Result<String, String> {
    lowered(
        &identity_module(
            "inventory_nested_sequence_type",
            Ty::Tuple(vec![Ty::I64, Ty::Sequence(TyId::new(0))]),
        ),
        "a Ty::Sequence tuple field",
    )
}

/// `ExtractElement` / `InsertElement` over a sequence constant this backend
/// materialized: trust-ir's codegen gate refuses it whatever the provenance.
fn sequence_element_op_module(name: &str, insert: bool) -> TrustIrModule {
    let seq = Ty::Sequence(TyId::new(0));
    let mut body = vec![
        sequence_const_node(vec![Constant::Int(5), Constant::Int(8)], v(0)),
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(v(1)),
    ];
    if insert {
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(9),
            })
            .with_result(v(2)),
        );
        body.push(
            InstrNode::new(Inst::InsertElement {
                ty: seq,
                array: v(0),
                index: v(1),
                value: v(2),
            })
            .with_result(v(3)),
        );
    } else {
        body.push(
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
        );
    }
    body.push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    let mut module = module_with_blocks(
        name,
        vec![],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body,
        }],
    );
    module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    module
}

fn probe_sequence_extract_element() -> Result<String, String> {
    lowered(
        &sequence_element_op_module("inventory_sequence_extract", false),
        "Inst::ExtractElement over a Ty::Sequence",
    )
}

fn probe_sequence_insert_element() -> Result<String, String> {
    lowered(
        &sequence_element_op_module("inventory_sequence_insert", true),
        "Inst::InsertElement over a Ty::Sequence",
    )
}

fn probe_record_type() -> Result<String, String> {
    let record = RecordId::new(0);
    let mut module = module_with_blocks(
        "inventory_record_type",
        vec![Ty::Record(record)],
        vec![Ty::I64],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::Record(record))],
            body: vec![
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::Record(record),
                    aggregate: v(0),
                    field: 0,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        }],
    );
    module.add_record(RecordDef {
        id: record,
        name: "InventoryRecord".to_string(),
        fields: vec![FieldDef {
            name: "field".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
    });
    lowered(&module, "Ty::Record value slot with RecordDef")
}

fn probe_record_type_without_def() -> Result<String, String> {
    type_lowers(
        &Ty::Record(RecordId::new(0)),
        "Ty::Record without RecordDef",
    )
}

fn probe_closure_type_without_table() -> Result<String, String> {
    type_lowers(
        &Ty::Closure(ClosureTyId::new(0)),
        "Ty::Closure without table",
    )
}

fn probe_never_return_signature() -> Result<String, String> {
    let module = module_with_blocks(
        "inventory_never_return",
        vec![],
        vec![Ty::Never],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Unreachable)],
        }],
    );
    lowered(&module, "fn() -> Never")
}

fn probe_reference_pointer_carriers() -> Result<String, String> {
    let mut summary = Vec::new();
    for (label, ty) in [
        ("Ref", Ty::Ref(Box::new(Ty::I64))),
        ("RefMut", Ty::RefMut(Box::new(Ty::I64))),
        ("PtrConst", Ty::PtrConst(Box::new(Ty::I64))),
        ("PtrMut", Ty::PtrMut(Box::new(Ty::I64))),
    ] {
        let module = single_inst_module(
            "inventory_reference_carrier",
            vec![(v(0), ty)],
            vec![Ty::I64],
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
            vec![v(1)],
        );
        summary.push(lowered(&module, label)?);
    }
    Ok(summary.join("; "))
}

fn probe_fence_orderings() -> Result<String, String> {
    let body = [
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ]
    .into_iter()
    .map(|ordering| InstrNode::new(Inst::Fence { ordering }))
    .chain(std::iter::once(InstrNode::new(Inst::Return {
        values: vec![],
    })))
    .collect();
    let module = module_with_blocks(
        "inventory_fence",
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body,
        }],
    );
    let func = translate_single(&module)?;
    let fences = func.blocks[&func.entry_block]
        .instructions
        .iter()
        .filter(|inst| {
            matches!(
                inst.opcode,
                trust_cg_lower::instructions::Opcode::Fence { .. }
            )
        })
        .count();
    if fences == 4 {
        Ok("Inst::Fence at Acquire/Release/AcqRel/SeqCst: 4 LIR fences".to_string())
    } else {
        Err(format!("expected 4 LIR fences, found {fences}"))
    }
}

fn probe_null_ptr() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_null_ptr",
            vec![],
            vec![Ty::Ptr],
            InstrNode::new(Inst::NullPtr).with_result(v(0)),
            vec![v(0)],
        ),
        "Inst::NullPtr",
    )
}

/// An undef whose poison is only transported (stored plainly, never
/// reloaded): lowers under the NoUndef zero model.
fn probe_undef_transported() -> Result<String, String> {
    lowered(
        &module_with_blocks(
            "inventory_undef_transported",
            vec![Ty::I64],
            vec![Ty::I64],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(1)),
                    InstrNode::new(Inst::Alloca {
                        ty: Ty::I64,
                        count: None,
                        align: None,
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Store {
                        ty: Ty::I64,
                        ptr: v(2),
                        value: v(1),
                        volatile: false,
                        align: None,
                    }),
                    InstrNode::new(Inst::Return { values: vec![v(0)] }),
                ],
            }],
        ),
        "Inst::Undef i64 transported",
    )
}

/// An undef returned: inspecting poison, refused.
fn probe_undef_scalar() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_undef",
            vec![],
            vec![Ty::I64],
            InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0)),
            vec![v(0)],
        ),
        "Inst::Undef i64",
    )
}

fn sequence_const_node(values: Vec<Constant>, result: ValueId) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::Sequence(TyId::new(0)),
        value: Constant::Sequence(values),
    })
    .with_result(result)
}

fn seq_map_module(name: &str, elem: Ty, values: Vec<Constant>, map: Inst) -> TrustIrModule {
    let mut module = module_with_blocks(
        name,
        vec![],
        vec![],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                sequence_const_node(values, v(0)),
                InstrNode::new(map).with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );
    module
        .add_type(elem)
        .expect("Module::add_type: test fixture");
    module
}

fn probe_seq_map_add_k() -> Result<String, String> {
    lowered(
        &seq_map_module(
            "inventory_seq_map_add_k",
            Ty::I64,
            vec![Constant::Int(1), Constant::Int(2)],
            Inst::SeqMapAddK {
                ty: Ty::Sequence(TyId::new(0)),
                seq: v(0),
                k: 1,
            },
        ),
        "Inst::SeqMapAddK",
    )
}

fn probe_seq_map_not() -> Result<String, String> {
    lowered(
        &seq_map_module(
            "inventory_seq_map_not",
            Ty::Bool,
            vec![Constant::Bool(true), Constant::Bool(false)],
            Inst::SeqMapNot {
                ty: Ty::Sequence(TyId::new(0)),
                seq: v(0),
            },
        ),
        "Inst::SeqMapNot",
    )
}

/// `SeqMap` over `[1, 2]` with the element function `fwd` (FuncId 1 is
/// `incr(p: &mut i64) { *p += 1 }`, FuncId 0 the mapping function itself).
fn seq_map_with_element_function(name: &str, fwd: FuncId) -> TrustIrModule {
    let mut module = seq_map_module(
        name,
        Ty::I64,
        vec![Constant::Int(1), Constant::Int(2)],
        Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(0),
            fwd,
        },
    );
    let pointer = Ty::RefMut(Box::new(Ty::I64));
    let ty = module
        .add_func_type(FuncTy {
            params: vec![pointer.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut incr = TrustIrFunction::new(f(1), "inventory_incr", ty, b(0));
    incr.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), pointer)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I64,
                lhs: v(1),
                rhs: v(2),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: v(0),
                value: v(3),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module
        .try_add_function(incr)
        .expect("Module::try_add_function: test fixture");
    module
}

fn probe_seq_map() -> Result<String, String> {
    lowered(
        &seq_map_with_element_function("inventory_seq_map", f(1)),
        "Inst::SeqMap",
    )
}

fn probe_seq_map_bad_fwd() -> Result<String, String> {
    // FuncId 0 is `() -> ()`, not `fn(&mut i64)`.
    lowered(
        &seq_map_with_element_function("inventory_seq_map_bad_fwd", f(0)),
        "Inst::SeqMap with a mismatched element function",
    )
}

fn probe_seq_map_add_k_float() -> Result<String, String> {
    lowered(
        &seq_map_module(
            "inventory_seq_map_add_k_float",
            Ty::F64,
            vec![Constant::Float(1.5)],
            Inst::SeqMapAddK {
                ty: Ty::Sequence(TyId::new(0)),
                seq: v(0),
                k: 1,
            },
        ),
        "Inst::SeqMapAddK over f64",
    )
}

fn probe_seq_map_not_int() -> Result<String, String> {
    lowered(
        &seq_map_module(
            "inventory_seq_map_not_int",
            Ty::I64,
            vec![Constant::Int(1)],
            Inst::SeqMapNot {
                ty: Ty::Sequence(TyId::new(0)),
                seq: v(0),
            },
        ),
        "Inst::SeqMapNot over i64",
    )
}

fn probe_borrow() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_borrow",
            vec![(v(0), Ty::Ptr)],
            vec![Ty::Ptr],
            InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::Borrow",
    )
}

fn probe_borrow_mut() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_borrow_mut",
            vec![(v(0), Ty::Ptr)],
            vec![Ty::Ptr],
            InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::BorrowMut",
    )
}

fn probe_end_borrow() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_end_borrow",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::EndBorrow { borrow_ptr: v(0) }),
            vec![],
        ),
        "Inst::EndBorrow",
    )
}

fn probe_borrow_non_pointer() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_borrow_non_pointer",
            vec![(v(0), Ty::I64)],
            vec![Ty::Ptr],
            InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::Borrow of an i64",
    )
}

fn probe_borrow_mut_of_shared() -> Result<String, String> {
    lowered(
        &module_with_blocks(
            "inventory_borrow_mut_of_shared",
            vec![Ty::Ptr],
            vec![Ty::Ptr],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::Ptr)],
                body: vec![
                    InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
                    InstrNode::new(Inst::BorrowMut { ptr: v(1) }).with_result(v(2)),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ],
            }],
        ),
        "Inst::BorrowMut of a shared borrow",
    )
}

fn probe_end_borrow_of_borrow() -> Result<String, String> {
    lowered(
        &module_with_blocks(
            "inventory_end_borrow_of_borrow",
            vec![Ty::Ptr],
            vec![],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::Ptr)],
                body: vec![
                    InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)),
                    InstrNode::new(Inst::EndBorrow { borrow_ptr: v(1) }),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            }],
        ),
        "Inst::EndBorrow of a borrow",
    )
}

fn probe_retain_without_runtime() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_retain",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::Retain { ptr: v(0) }),
            vec![],
        ),
        "Inst::Retain without RC runtime",
    )
}

fn probe_release_without_runtime() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_release",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::Release { ptr: v(0) }),
            vec![],
        ),
        "Inst::Release without RC runtime",
    )
}

fn probe_is_unique_without_runtime() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_is_unique",
            vec![(v(0), Ty::Ptr)],
            vec![Ty::Bool],
            InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::IsUnique without RC runtime",
    )
}

/// The most resolvable `Dealloc` there is: the result of a same-function
/// `RustHeap` `HeapAlloc` of one static layout (the shape the retired
/// provenance lowering emitted `__rust_dealloc` for).
fn probe_dealloc_of_a_same_function_heap_alloc() -> Result<String, String> {
    lowered(
        &module_with_blocks(
            "inventory_dealloc",
            vec![],
            vec![],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::HeapAlloc {
                        ty: Ty::U64,
                        count: None,
                        align: None,
                        origin: trust_ir::inst::AllocOrigin::RustHeap,
                    })
                    .with_result(v(0)),
                    InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            }],
        ),
        "Inst::Dealloc of a same-function HeapAlloc",
    )
}

fn frame_def() -> BindingFrameDef {
    BindingFrameDef::new(
        BindingFrameId::new(0),
        "inventory_frame",
        vec![BindingSlot::new("slot", Ty::I64)],
    )
}

fn probe_open_frame() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_open_frame",
            vec![],
            vec![Ty::Ptr],
            InstrNode::new(Inst::OpenFrame { def: frame_def() }).with_result(v(0)),
            vec![v(0)],
        ),
        "Inst::OpenFrame",
    )
}

fn probe_bind_slot() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_bind_slot",
            vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            vec![Ty::Ptr],
            InstrNode::new(Inst::BindSlot {
                frame: v(0),
                slot: 0,
                value: v(1),
            })
            .with_result(v(2)),
            vec![v(2)],
        ),
        "Inst::BindSlot",
    )
}

fn probe_load_slot() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_load_slot",
            vec![(v(0), Ty::Ptr)],
            vec![Ty::I64],
            InstrNode::new(Inst::LoadSlot {
                frame: v(0),
                slot: 0,
                ty: Ty::I64,
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::LoadSlot",
    )
}

/// A complete frame: open, bind, load, close.
fn probe_frame_program() -> Result<String, String> {
    lowered(
        &module_with_blocks(
            "inventory_frame_program",
            vec![Ty::I64],
            vec![Ty::I64],
            vec![TrustIrBlock {
                id: b(0),
                params: vec![(v(0), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::OpenFrame { def: frame_def() }).with_result(v(1)),
                    InstrNode::new(Inst::BindSlot {
                        frame: v(1),
                        slot: 0,
                        value: v(0),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::LoadSlot {
                        frame: v(2),
                        slot: 0,
                        ty: Ty::I64,
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::CloseFrame { frame: v(2) }),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            }],
        ),
        "binding frame open/bind/load/close",
    )
}

fn probe_close_frame_non_frame() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_close_frame_non_frame",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::CloseFrame { frame: v(0) }),
            vec![],
        ),
        "Inst::CloseFrame of a parameter",
    )
}

fn probe_unknown_dialect_op() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_unknown_dialect",
            vec![],
            vec![Ty::I64],
            InstrNode::new(Inst::DialectOp(Box::new(
                DialectInst::new("inventory_unknown", "opaque").with_result_ty(Ty::I64),
            )))
            .with_result(v(0)),
            vec![v(0)],
        ),
        "Inst::DialectOp unknown namespace",
    )
}

fn probe_make_closure() -> Result<String, String> {
    let module = runtime_closure::runtime_closure_module(true);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    lowered(&module, "Inst::MakeClosure")
}

fn probe_make_aggregate() -> Result<String, String> {
    let mut module = single_inst_module(
        "inventory_make_aggregate",
        vec![(v(0), Ty::I64)],
        vec![Ty::Struct(StructId::new(0))],
        InstrNode::new(Inst::MakeAggregate {
            ty: Ty::Struct(StructId::new(0)),
            variant: None,
            fields: vec![v(0)],
        })
        .with_result(v(1)),
        vec![v(1)],
    );
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "InventoryPair".to_string(),
        fields: vec![FieldDef {
            name: "lane".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::default(),
    });
    lowered(&module, "Inst::MakeAggregate")
}

fn probe_make_aggregate_enum() -> Result<String, String> {
    let mut module = single_inst_module(
        "inventory_make_aggregate_enum",
        vec![(v(0), Ty::Ptr)],
        vec![Ty::Enum(EnumId::new(0))],
        InstrNode::new(Inst::MakeAggregate {
            ty: Ty::Enum(EnumId::new(0)),
            variant: Some(1),
            fields: vec![v(0)],
        })
        .with_result(v(1)),
        vec![v(1)],
    );
    module.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "InventoryChoice".to_string(),
        variants: vec![
            EnumVariant {
                name: "Empty".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Full".to_string(),
                fields: vec![Ty::Ptr],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: Some(trust_ir::ty::EnumLayoutDescriptor {
            encoding: trust_ir::ty::EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: trust_ir::ty::EnumTagRepr::U64,
            },
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![], vec![0]],
        }),
    });
    lowered(
        &module,
        "Inst::MakeAggregate runtime raw-pointer niche validity",
    )
}

/// `f(x: u32, i: u64) -> u32 { [x; 4][i] }`.
fn probe_array_splat() -> Result<String, String> {
    let mut module = module_with_blocks(
        "inventory_array_splat",
        vec![Ty::U32, Ty::U64],
        vec![Ty::U32],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::U32), (v(1), Ty::U64)],
            body: vec![
                InstrNode::new(Inst::ArraySplat {
                    ty: Ty::Array(TyId::new(0), 4),
                    value: v(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::U32,
                    array: v(2),
                    index: v(1),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        }],
    );
    module.types = vec![Ty::U32];
    lowered(&module, "Inst::ArraySplat")
}

fn probe_array_splat_non_array() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_array_splat_non_array",
            vec![(v(0), Ty::U32)],
            vec![Ty::U32],
            InstrNode::new(Inst::ArraySplat {
                ty: Ty::U32,
                value: v(0),
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
        "Inst::ArraySplat at a non-array type",
    )
}

/// `f(i: u64) -> u32 { splat[ 1; 4 ][i] }`.
fn probe_splat_constant() -> Result<String, String> {
    let mut module = module_with_blocks(
        "inventory_splat_constant",
        vec![Ty::U64],
        vec![Ty::U32],
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), Ty::U64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Array(TyId::new(0), 4),
                    value: Constant::Splat {
                        elem: Box::new(Constant::Int(1)),
                        len: 4,
                    },
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::U32,
                    array: v(1),
                    index: v(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        }],
    );
    module.types = vec![Ty::U32];
    lowered(&module, "Constant::Splat")
}

fn probe_splat_constant_non_array() -> Result<String, String> {
    let name = "inventory_splat_constant_non_array";
    let malformed = const_module(
        name,
        Ty::U32,
        Constant::Splat {
            elem: Box::new(Constant::Int(1)),
            len: 2,
        },
    );
    // Preserve the original source, but require its actual canonical type
    // finding before backend constant materialization can erase the mismatch.
    Err(canonical_constants::body_refused(
        &malformed, name, "u32", "splat[2]",
    ))
}

fn probe_assert_panic() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_assert_panic",
            vec![(v(0), Ty::Bool)],
            vec![],
            InstrNode::new(Inst::Assert {
                cond: v(0),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            }),
            vec![],
        ),
        "Inst::Assert",
    )
}

/// trust-ir v54 (amendment P): `module` plus the panic entry its sites name,
/// `f(1)`, a `(ptr) -> ()` definition that never returns (the signature a
/// zero-operand kind's entry must have).
fn with_panic_entry(mut module: TrustIrModule) -> TrustIrModule {
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = TrustIrFunction::new(f(1), "panic_const_div_by_zero", ty, b(0));
    entry.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Unreachable)],
    }];
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The v54 site every probe uses: entry `f(1)`, the run-time location `v(1)`.
fn panic_site() -> trust_ir::PanicSite {
    trust_ir::PanicSite {
        entry: f(1),
        location: trust_ir::PanicLocation::Value(v(1)),
    }
}

fn probe_sited_assert() -> Result<String, String> {
    lowered(
        &with_panic_entry(single_inst_module(
            "inventory_sited_assert",
            vec![(v(0), Ty::Bool), (v(1), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::Assert {
                cond: v(0),
                kind: trust_ir::AssertKind::DivByZero,
                site: Some(panic_site()),
            }),
            vec![],
        )),
        "Inst::Assert { site: Some(_) }",
    )
}

fn probe_assert_invoke() -> Result<String, String> {
    lowered(
        &with_panic_entry(module_with_blocks(
            "inventory_assert_invoke",
            vec![Ty::Bool, Ty::Ptr],
            vec![],
            vec![
                TrustIrBlock {
                    id: b(0),
                    params: vec![(v(0), Ty::Bool), (v(1), Ty::Ptr)],
                    body: vec![InstrNode::new(Inst::AssertInvoke {
                        cond: v(0),
                        kind: trust_ir::AssertKind::DivByZero,
                        site: panic_site(),
                        normal_dest: b(1),
                        normal_args: vec![],
                        unwind_dest: b(2),
                    })],
                },
                TrustIrBlock {
                    id: b(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                TrustIrBlock {
                    id: b(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::LandingPad {
                            is_cleanup: true,
                            catch_type_indices: vec![],
                        })
                        .with_results([v(2), v(3)]),
                        InstrNode::new(Inst::Resume { exn: v(2) }),
                    ],
                },
            ],
        )),
        "Inst::AssertInvoke",
    )
}

fn probe_drop() -> Result<String, String> {
    lowered(
        &with_owner_struct(single_inst_module(
            "inventory_drop",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::Drop {
                ty: Ty::Struct(StructId::new(0)),
                ptr: v(0),
            }),
            vec![],
        )),
        "Inst::Drop",
    )
}

fn probe_call_cannot_unwind() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_call_cannot_unwind",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::CallCannotUnwind {
                callee: f(0),
                args: vec![v(0)],
            }),
            vec![],
        ),
        "Inst::CallCannotUnwind",
    )
}

fn probe_call_indirect_cannot_unwind() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_call_indirect_cannot_unwind",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::CallIndirectCannotUnwind {
                callee: v(0),
                sig: FuncTyId::new(0),
                args: vec![v(0)],
                calling_conv: trust_ir::CallingConv::default(),
            }),
            vec![],
        ),
        "Inst::CallIndirectCannotUnwind",
    )
}

/// v55 (amendment D): `module` with the struct `InventoryOwner` (`struct.0`,
/// not trivially droppable) and its drop glue `f(1)`, `(ptr) -> ()`,
/// registered in the module drop-glue table.
fn with_drop_glue(module: TrustIrModule) -> TrustIrModule {
    let mut module = with_owner_struct(module);
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut glue = TrustIrFunction::new(f(1), "inventory_owner_drop_glue", ty, b(0));
    glue.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module
        .try_add_function(glue)
        .expect("Module::try_add_function: test fixture");
    module
        .set_drop_glue(Ty::Struct(StructId::new(0)), f(1))
        .expect("one row for one type and one glue");
    module
}

/// `module` with the struct `InventoryOwner` (`struct.0`, not trivially
/// droppable). Since trust-ir v55 a drop of a trivially droppable type is not
/// the one spelling of a drop (trust-ir's own codegen verdict refuses it
/// before the floor), so the drop probes drop this struct.
fn with_owner_struct(mut module: TrustIrModule) -> TrustIrModule {
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "InventoryOwner".to_string(),
        fields: vec![FieldDef {
            name: "handle".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::default(),
    });
    module
}

fn probe_drop_glue_table() -> Result<String, String> {
    lowered_module(
        &with_drop_glue(control_module("inventory_drop_glue_table")),
        "drop_glue table",
    )
}

fn probe_drop_at_a_registered_type() -> Result<String, String> {
    lowered(
        &with_drop_glue(single_inst_module(
            "inventory_drop_registered",
            vec![(v(0), Ty::Ptr)],
            vec![],
            InstrNode::new(Inst::Drop {
                ty: Ty::Struct(StructId::new(0)),
                ptr: v(0),
            }),
            vec![],
        )),
        "Inst::Drop at a registered type",
    )
}

fn probe_drop_invoke() -> Result<String, String> {
    lowered(
        &with_drop_glue(module_with_blocks(
            "inventory_drop_invoke",
            vec![Ty::Ptr],
            vec![],
            vec![
                TrustIrBlock {
                    id: b(0),
                    params: vec![(v(0), Ty::Ptr)],
                    body: vec![InstrNode::new(Inst::DropInvoke {
                        ty: Ty::Struct(StructId::new(0)),
                        ptr: v(0),
                        normal_dest: b(1),
                        normal_args: vec![],
                        unwind_dest: b(2),
                    })],
                },
                TrustIrBlock {
                    id: b(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                TrustIrBlock {
                    id: b(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::LandingPad {
                            is_cleanup: true,
                            catch_type_indices: vec![],
                        })
                        .with_results([v(1), v(2)]),
                        InstrNode::new(Inst::Resume { exn: v(1) }),
                    ],
                },
            ],
        )),
        "Inst::DropInvoke",
    )
}

fn probe_invoke_indirect() -> Result<String, String> {
    lowered(
        &module_with_blocks(
            "inventory_invoke_indirect",
            vec![Ty::Ptr],
            vec![],
            vec![
                TrustIrBlock {
                    id: b(0),
                    params: vec![(v(0), Ty::Ptr)],
                    body: vec![InstrNode::new(Inst::InvokeIndirect {
                        callee: v(0),
                        sig: FuncTyId::new(0),
                        args: vec![v(0)],
                        calling_conv: trust_ir::CallingConv::default(),
                        normal_dest: b(1),
                        normal_args: vec![],
                        unwind_dest: b(2),
                    })],
                },
                TrustIrBlock {
                    id: b(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                TrustIrBlock {
                    id: b(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::LandingPad {
                            is_cleanup: true,
                            catch_type_indices: vec![],
                        })
                        .with_results([v(1), v(2)]),
                        InstrNode::new(Inst::Resume { exn: v(1) }),
                    ],
                },
            ],
        ),
        "Inst::InvokeIndirect",
    )
}

fn probe_weak_cmpxchg() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_weak_cmpxchg",
            vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
            vec![Ty::I64],
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(0),
                expected: v(1),
                desired: v(1),
                success: Ordering::SeqCst,
                failure: Ordering::SeqCst,
                weak: true,
            })
            .with_results([v(2), v(3)]),
            vec![v(2)],
        ),
        "Inst::CmpXchg weak",
    )
}

fn tensor_blob_value() -> Constant {
    Constant::TensorBlob {
        digest: trust_ir::blob::BlobDigest::of(&[0, 0, 0, 0]),
        dims: vec![1],
    }
}
fn probe_tensor_blob_constant() -> Result<String, String> {
    // The earlier whole-module type floor rejects the real tensor carrier.
    // Preserve the malformed-spelling twin through the real public gate too.
    // It is a prerequisite validation refusal, distinct from the native layout
    // refusal pinned for the well-typed carrier below.
    let malformed = probe_tensor_blob_scalar_bypass().expect_err("scalar spelling must refuse");
    assert!(
        malformed.contains("const type mismatch: expected i64, got tensor_blob[1]"),
        "{malformed}"
    );
    lowered(
        &const_module(
            "inventory_tensor_blob",
            Ty::Tensor(Box::new(Ty::I32), 1),
            tensor_blob_value(),
        ),
        "Constant::TensorBlob",
    )
}
fn probe_tensor_blob_scalar_bypass() -> Result<String, String> {
    // A malformed scalar spelling must not evade the separate body-constant
    // refusal merely by omitting the unsupported tensor type.
    lowered(
        &const_module(
            "inventory_tensor_blob_scalar_bypass",
            Ty::I64,
            tensor_blob_value(),
        ),
        "Constant::TensorBlob scalar bypass",
    )
}
fn probe_uninit_lane() -> Result<String, String> {
    lowered(
        &const_module(
            "inventory_uninit_lane",
            Ty::Tuple(vec![Ty::I64, Ty::I64]),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Uninit]),
        ),
        "Constant::Uninit",
    )
}

fn set_const_module(name: &str, values: Vec<Constant>) -> TrustIrModule {
    let mut module = single_inst_module(
        name,
        vec![],
        vec![],
        InstrNode::new(Inst::Const {
            ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            value: Constant::Set(values),
        })
        .with_result(v(0)),
        vec![],
    );
    module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    module
}

fn probe_set_constant() -> Result<String, String> {
    lowered(
        &set_const_module(
            "inventory_set_const",
            vec![Constant::Int(2), Constant::Int(1)],
        ),
        "Constant::Set",
    )
}

fn probe_set_constant_repeated() -> Result<String, String> {
    lowered(
        &set_const_module(
            "inventory_set_const_repeated",
            vec![Constant::Int(1), Constant::Int(1)],
        ),
        "Constant::Set with a repeated element",
    )
}

fn probe_phantom_constant() -> Result<String, String> {
    lowered(
        &canonical_constants::phantom_subject("inventory_phantom_const"),
        "Constant::PhantomData",
    )
}

fn probe_phantom_non_unit() -> Result<String, String> {
    Err(canonical_constants::phantom_non_unit(
        "inventory_phantom_non_unit",
    ))
}

fn probe_fndef_unregistered() -> Result<String, String> {
    Err(canonical_constants::fndef_unregistered(
        "inventory_fndef_unregistered",
    ))
}

fn probe_transmute() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_transmute",
            vec![(v(0), Ty::I64)],
            vec![Ty::F64],
            InstrNode::new(Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: v(0),
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
        "CastOp::Transmute i64 -> f64",
    )
}

fn probe_transmute_size_mismatch() -> Result<String, String> {
    lowered(
        &single_inst_module(
            "inventory_transmute_size_mismatch",
            vec![(v(0), Ty::I64)],
            vec![Ty::I32],
            InstrNode::new(Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
            vec![v(1)],
        ),
        "CastOp::Transmute i64 -> i32",
    )
}

fn control_module(name: &str) -> TrustIrModule {
    const_module(name, Ty::I64, Constant::Int(7))
}

fn obligation(id: u32, kind: ObligationKind, status: ProofStatus) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "inventory probe".to_string(),
        formula: None,
        function: Some(f(0)),
        source: None,
        site: None,
        spec: None,
    }
}

fn probe_proof_tables() -> Result<String, String> {
    let mut module = control_module("inventory_proof_tables");
    module.proof_obligations.push(obligation(
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    ));
    module
        .proof_certificates
        .push(trust_ir::proof::ProofCertificate {
            obligation: ProofId::new(0),
            prover: "inventory".to_string(),
            evidence: trust_ir::proof::ProofEvidence::Trusted("inventory probe".to_string()),
            assurance: None,
        });
    lowered_module(&module, "proof_obligations + proof_certificates")
}

fn probe_source_file_table() -> Result<String, String> {
    let mut module = TrustIrModule::new("inventory_files");
    let file = module
        .intern_file("inventory/probe.rs")
        .expect("Module::intern_file: test fixture");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), "inventory_files", ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(v(0))
            .with_span(SourceSpan {
                file,
                line: 3,
                col: 5,
            }),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    let lowered = translate_single(&module)?;
    match lowered.debug_meta.source_file.as_deref() {
        Some("inventory/probe.rs") => {
            Ok("Module.files resolved into debug_meta.source_file".to_string())
        }
        other => Err(format!(
            "Module.files was not consumed: debug_meta.source_file = {other:?}"
        )),
    }
}

fn probe_inert_sidecar_tables() -> Result<String, String> {
    let mut module = control_module("inventory_sidecars");
    module.proof_obligations.push(obligation(
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
    ));
    module.obligation_diagnostics.push(ObligationDiagnostic {
        obligation: ProofId::new(0),
        severity: DiagnosticSeverity::Warning,
        message: "inventory probe".to_string(),
        location: None,
        detail: None,
    });
    module.spec_modules.push(SpecModule::new("inventory_spec"));
    let _import = module
        .intern_import(ModuleImport::new("inventory_dep", ProofDigest::zero()))
        .expect("Module::intern_import: test fixture");
    lowered_module(
        &module,
        "obligation_diagnostics + spec_modules + imports carried",
    )
}

fn probe_universe_refinement() -> Result<String, String> {
    let mut module = TrustIrModule::new("inventory_universes");
    let base = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let universe = Universe::range(0, 9).ok_or("empty universe")?;
    let pred = module
        .intern_in_universe(universe, Space::Member)
        .expect("Module::intern_in_universe: test fixture")
        .ok_or("universe predicate not interned")?;
    let refined = Ty::Refine(base, pred);
    let ty = module
        .add_func_type(FuncTy {
            params: vec![refined.clone()],
            returns: vec![refined.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), "inventory_universes", ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), refined)],
        body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    if module.universes.is_empty()
        || !matches!(module.predicates.first(), Some(Pred::InUniverse(..)))
    {
        return Err("universe/predicate tables were not populated".to_string());
    }
    lowered_module(&module, "Refine<i64, InUniverse(0..=9, Member)>")
}

fn probe_global_asm() -> Result<String, String> {
    let mut module = control_module("inventory_global_asm");
    module.global_asm.push(".text".to_string());
    lowered_module(&module, "Module.global_asm")
}

fn probe_blob_table() -> Result<String, String> {
    // An otherwise lowerable module whose table no constant names: the table
    // is refused for itself, not only through a tensor-typed use.
    let mut module = control_module("inventory_blob_table");
    module.intern_blob(vec![7, 0, 0, 0]);
    lowered_module(&module, "Module.blobs")
}

fn probe_completeness_claim() -> Result<String, String> {
    let mut module = control_module("inventory_completeness");
    module.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    lowered_module(&module, "Module.completeness")
}

fn probe_declared_closure_layouts() -> Result<String, String> {
    let mut module = control_module("inventory_declared_closure_layouts");
    // A declared physical byte image is interpreted for this exact target,
    // not as a target-independent legacy closure capture layout.
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    module.closure_types.push(trust_ir::ClosureTy {
        func: module.functions[0].ty,
        captures: vec![Ty::U64, Ty::U8],
    });
    lowered_module(&module, "closure type without a declared image")?;
    module
        .closure_layouts
        .push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(0),
            size: 16,
            align: 8,
            capture_offsets: vec![8, 0],
        });
    module
        .validate_closure_layouts()
        .map_err(|error| format!("invalid declared closure control: {error}"))?;
    let original = module.clone();
    let result = lowered_module(&module, "Module.closure_layouts with reordered captures");
    if module != original {
        return Err("declared closure probe changed its original module".to_string());
    }
    result
}

fn tuple_layout_module(name: &str, by_value: bool, field_offsets: Vec<u64>) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    // Descriptor validation resolves the tuple's canonical layout, which needs
    // a target stamp (`TupleLayoutTargetMissing` otherwise).
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let tuple = Ty::Tuple(vec![Ty::I64, Ty::I64]);
    let tuple_id = module
        .add_type(tuple.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: tuple_id,
        size: 16,
        align: 8,
        field_offsets,
    });
    let carrier = if by_value {
        tuple
    } else {
        Ty::PtrConst(Box::new(tuple))
    };
    let ty = module
        .add_func_type(FuncTy {
            params: vec![carrier.clone()],
            returns: vec![carrier.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(f(0), name, ty, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), carrier)],
        body: vec![InstrNode::new(Inst::Return { values: vec![v(0)] })],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn probe_tuple_layouts_pointer_transport() -> Result<String, String> {
    lowered_module(
        &tuple_layout_module("inventory_tuple_layout_pointer", false, vec![0, 8]),
        "tuple_layouts in the pointer-transport profile",
    )
}

/// WS7.7: a by-value tuple under a row EQUAL to the declaration-order layout
/// the byte path emits is consumed, honoured by construction.
fn probe_tuple_layouts_by_value_agreeing() -> Result<String, String> {
    probe_tuple_layouts_pointer_transport()?;
    lowered_module(
        &tuple_layout_module("inventory_tuple_layout_by_value", true, vec![0, 8]),
        "tuple_layouts with a by-value tuple under an agreeing row",
    )
}

/// WS7.7 negative twin: the same by-value tuple under a reordered (valid)
/// row is refused as a layout disagreement.
fn probe_tuple_layouts_by_value_reordered() -> Result<String, String> {
    lowered_module(
        &tuple_layout_module("inventory_tuple_layout_reordered", true, vec![8, 0]),
        "tuple_layouts with a by-value tuple under a reordered row",
    )
}

// ---------------------------------------------------------------------------
// Gate.
// ---------------------------------------------------------------------------

fn check_family_complete(rows: &[Row], family: Family, expected: &[&str]) {
    let mut seen = BTreeSet::new();
    let mut duplicates = Vec::new();
    for row in rows.iter().filter(|row| row.family == family) {
        if !seen.insert(row.construct) {
            duplicates.push(row.construct);
        }
    }
    let expected_set: BTreeSet<&str> = expected.iter().copied().collect();
    let missing: Vec<&str> = expected_set.difference(&seen).copied().collect();
    let unknown: Vec<&str> = seen.difference(&expected_set).copied().collect();
    assert!(
        duplicates.is_empty() && missing.is_empty() && unknown.is_empty(),
        "{} inventory at the pinned trust-ir: duplicates {duplicates:?}, missing rows {missing:?}, rows for no such construct {unknown:?}",
        family.label()
    );
    assert_eq!(
        expected.len(),
        expected_set.len(),
        "{} variant list has duplicate names",
        family.label()
    );
}

fn run_probe(probe: Probe) -> Result<String, String> {
    probe()
}

fn assert_needles(context: &str, text: &str, needles: &[&str]) {
    for needle in needles {
        assert!(
            text.contains(needle),
            "{context}: diagnostic must contain `{needle}`, got `{text}`"
        );
    }
}

/// Precision migration of the identical original sited input. This historical
/// test name is retained; valid native delivery is now positive, not Refused.
#[test]
fn sited_assert_is_refused_by_the_site_name() {
    run_probe(probe_sited_assert).expect("sited native delivery now lowers");
    match run_probe(probe_assert_panic) {
        Ok(what) => panic!("an unspecified unsited assertion must still refuse ({what})"),
        Err(text) => assert_needles("unspecified assertion", &text, &["panic"]),
    }
}

#[test]
fn every_ty_variant_has_exactly_one_row() {
    check_family_complete(&all_rows(), Family::Ty, TY_VARIANTS);
}

#[test]
fn every_inst_variant_has_exactly_one_row() {
    check_family_complete(&all_rows(), Family::Inst, INST_VARIANTS);
}

#[test]
fn every_constant_variant_has_exactly_one_row() {
    check_family_complete(&all_rows(), Family::Constant, CONSTANT_VARIANTS);
    assert_eq!(
        CONSTANT_VARIANTS.len(),
        18,
        "Constant variant census at the pinned trust-ir"
    );
}

#[test]
fn every_cast_op_variant_has_exactly_one_row() {
    check_family_complete(&all_rows(), Family::CastOp, CAST_OP_VARIANTS);
    assert_eq!(
        CAST_OP_VARIANTS.len(),
        17,
        "CastOp variant census at the pinned trust-ir"
    );
}

#[test]
fn every_module_table_has_exactly_one_row() {
    let tables = module_table_names(&TrustIrModule::new("inventory_tables"));
    assert_eq!(
        tables.len(),
        24,
        "Module table census at the pinned trust-ir"
    );
    let mut expected: Vec<&str> = tables.clone();
    expected.extend(MODULE_SUBTABLES);
    check_family_complete(&all_rows(), Family::ModuleTable, &expected);
    for sub in MODULE_SUBTABLES {
        let (table, _) = sub
            .split_once('.')
            .unwrap_or_else(|| panic!("sub-table `{sub}` must be spelled table.field"));
        assert!(
            tables.contains(&table),
            "sub-table `{sub}` names no Module table"
        );
    }
}

#[test]
fn rows_are_well_formed() {
    for row in all_rows() {
        let context = format!("{}::{}", row.family.label(), row.construct);
        assert!(
            !row.needle.is_empty(),
            "{context}: needle must be non-empty"
        );
        assert!(!row.note.is_empty(), "{context}: note must be non-empty");
        match &row.disposition {
            Disposition::Executed { file, test } | Disposition::ModelOnly { file, test } => {
                assert!(
                    !file.is_empty() && !test.is_empty(),
                    "{context}: evidence must be named"
                );
                assert!(
                    file.starts_with(CG) || file.starts_with(LW),
                    "{context}: evidence file `{file}` must be a codegen or lower test target"
                );
                if *file == SELF_FILE {
                    assert!(
                        row.probe.is_some(),
                        "{context}: evidence in this file needs an adapter probe"
                    );
                }
            }
            Disposition::Refused {
                diagnostic,
                pin_file,
                pin_test,
            } => {
                assert!(
                    !diagnostic.is_empty(),
                    "{context}: refusal needs a diagnostic needle"
                );
                assert!(
                    !pin_file.is_empty() && !pin_test.is_empty(),
                    "{context}: refusal pin must be named"
                );
                assert!(
                    row.probe.is_some(),
                    "{context}: refusal needs an adapter probe"
                );
                assert!(
                    row.negative.is_none(),
                    "{context}: a refused row is its own negative evidence"
                );
            }
        }
    }
}

#[test]
fn refused_rows_are_refused_by_the_adapter_by_name() {
    for row in all_rows() {
        let Disposition::Refused { diagnostic, .. } = row.disposition else {
            continue;
        };
        let context = format!("{}::{}", row.family.label(), row.construct);
        let probe = row
            .probe
            .unwrap_or_else(|| panic!("{context}: refused row has no probe"));
        match run_probe(probe) {
            Ok(what) => panic!(
                "{context}: must be refused at the pinned trust-ir but lowered ({what}); if the construct is now supported, move the row to ModelOnly/Executed and flip every pin of the old refusal"
            ),
            Err(text) => assert_needles(&context, &text, diagnostic),
        }
    }
}

#[test]
fn positive_probes_lower_through_the_adapter() {
    let mut probed = 0;
    for row in all_rows() {
        if matches!(row.disposition, Disposition::Refused { .. }) {
            continue;
        }
        let context = format!("{}::{}", row.family.label(), row.construct);
        if let Some(probe) = row.probe {
            run_probe(probe)
                .unwrap_or_else(|err| panic!("{context}: positive probe failed: {err}"));
            probed += 1;
        }
    }
    assert!(
        probed >= 12,
        "expected the self-evidenced rows to be probed, got {probed}"
    );
}

#[test]
fn negative_twins_are_refused_by_name() {
    let mut probed = 0;
    for row in all_rows() {
        let Some((needles, probe)) = row.negative else {
            continue;
        };
        let context = format!("{}::{} (negative)", row.family.label(), row.construct);
        match run_probe(probe) {
            Ok(what) => panic!("{context}: must be refused but lowered ({what})"),
            Err(text) => assert_needles(&context, &text, needles),
        }
        probed += 1;
    }
    assert!(
        probed >= 8,
        "expected the negative twins to be probed, got {probed}"
    );
}

#[test]
fn row_count_is_every_variant_and_table() {
    assert_eq!(
        all_rows().len(),
        TY_VARIANTS.len()
            + INST_VARIANTS.len()
            + CONSTANT_VARIANTS.len()
            + CAST_OP_VARIANTS.len()
            + module_table_names(&TrustIrModule::new("inventory_count")).len()
            + MODULE_SUBTABLES.len()
    );
}

#[test]
fn variant_name_functions_agree_with_the_derived_lists() {
    // The name functions and the lists come from one macro invocation; this
    // pins that a sample of each enum resolves to a listed name.
    let samples: [(&str, &str); 8] = [
        (ty_variant_name(&Ty::I8), "I8"),
        (
            ty_variant_name(&Ty::Handle(Box::new(trust_ir::ty::HandleTy::new(
                "Nat",
                "trust_bignum::Nat",
            )))),
            "Handle",
        ),
        (inst_variant_name(&Inst::Unreachable), "Unreachable"),
        (inst_variant_name(&Inst::NullPtr), "NullPtr"),
        (constant_variant_name(&Constant::PhantomData), "PhantomData"),
        (constant_variant_name(&Constant::Int(1)), "Int"),
        (cast_op_variant_name(&CastOp::Trunc), "Trunc"),
        (cast_op_variant_name(&CastOp::FPToUISat), "FPToUISat"),
    ];
    for (actual, expected) in samples {
        assert_eq!(actual, expected);
    }
    assert!(TY_VARIANTS.contains(&"Handle"));
    assert!(INST_VARIANTS.contains(&"MakeAggregate"));
    assert!(CONSTANT_VARIANTS.contains(&"SymbolAddr"));
    assert!(CAST_OP_VARIANTS.contains(&"ReifyFnPointer"));
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

#[test]
fn runtime_raw_niche_constructor_preserves_inventory_refusal() {
    let err =
        probe_make_aggregate_enum().expect_err("an unconstrained raw niche must remain refused");
    assert!(
        err.contains("Inst::MakeAggregate") && err.contains("no typed nonreserved"),
        "{err}"
    );
}
