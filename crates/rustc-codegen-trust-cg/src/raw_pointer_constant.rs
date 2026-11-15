// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical address transport for an original thin Rust raw-pointer constant
//! (or a single-field newtype over one: `NonNull<T>`, `Unique<T>`)
//! whose CTFE image carries no provenance: the null pointer, and the
//! address-only pointers `ptr::without_provenance(addr)` spells
//! (`NonNull::dangling()`, the aligned sentinel an empty `Vec`, its `RawVec`
//! and its `vec::IntoIter` hold). TrustIR spells such a value as the
//! pointer-width integer cast by `IntToPtr`. Its reference interpreter reads
//! zero as `NullPtr`, an address inside or one past a live allocation as a
//! pointer into that allocation, and any other address as the no-provenance
//! `DanglingPtr`. A `Constant::Int` at a typed raw pointer is malformed, and
//! the shared constant floor refuses it.
//!
//! The transport supplies no allocation, lifetime, aliasing or dereference
//! authority: dereferencing such a pointer is undefined in Rust. TrustIR
//! faults on a `DanglingPtr` dereference and is more defined than Rust, never
//! less, for an address that lands in a live allocation. References, integer
//! operands, fat pointers and any image carrying
//! provenance cannot use this path because of their numerical
//! representation. A provenance-carrying image stays on `emit_const_alloc_addr`.

use rustc_middle::mir::{self, ConstValue};
use rustc_middle::ty::{self, Ty as RustTy};
use trust_ir::{Block, CastOp, Constant, Inst, InstrNode, Ty, ValueId};

use super::MirLoweringCtx;

// Only the original Rust type, evaluated scalar and actual target layout can
// construct this witness. Its fields are private even to the parent module.
struct AddressOnlyRawPointer {
    integer: Ty,
    destination: Ty,
    address: i128,
}

/// The thin raw pointer `ty` is, alone or under newtypes over one: a pattern
/// type refines validity, never representation, and a struct whose single
/// non-zero-sized field sits at offset 0 of a layout the same size as that
/// field's is that field's value. Bounded at 8 links; anything else
/// (a reference, a union, an enum, a second non-zero-sized field) is `None`.
fn peel_newtypes_to_raw_pointer<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: RustTy<'tcx>,
) -> Option<RustTy<'tcx>> {
    let layout_of = |ty: RustTy<'tcx>| {
        tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
            .ok()
    };
    let mut current = ty;
    for _ in 0..8 {
        match current.kind() {
            ty::RawPtr(..) => return Some(current),
            ty::Pat(base, _) => current = *base,
            ty::Adt(adt, args) if adt.is_struct() => {
                let outer = layout_of(current)?;
                let mut payload = None;
                for (index, field) in adt.non_enum_variant().fields.iter().enumerate() {
                    let field_ty = super::normalized_adt_field_ty(tcx, field, *args);
                    let field_layout = layout_of(field_ty)?;
                    if field_layout.is_zst() {
                        continue;
                    }
                    if payload.is_some()
                        || outer.fields.offset(index).bytes() != 0
                        || outer.size != field_layout.size
                    {
                        return None;
                    }
                    payload = Some(field_ty);
                }
                current = payload?;
            }
            _ => return None,
        }
    }
    None
}

/// The pointer-width integer carrier of a `session_bits`-wide target.
fn address_integer(session_bits: u32) -> Option<Ty> {
    match session_bits {
        32 => Some(Ty::I32),
        64 => Some(Ty::I64),
        _ => None,
    }
}

impl AddressOnlyRawPointer {
    fn authenticate<'tcx>(
        ctx: &MirLoweringCtx<'tcx>,
        source: RustTy<'tcx>,
        evaluated: &mir::Const<'tcx>,
        destination: &Ty,
        session_bits: u32,
    ) -> Result<Option<Self>, String> {
        let source = ctx.monomorphize_ty(source);
        // A thin raw pointer, alone or under newtypes over one (`NonNull<T>`
        // through its pattern-typed field, `Unique<T>`, a user `struct
        // W(NonNull<T>)`): the same one-word value. A reference never
        // qualifies.
        let Some(pointer) = peel_newtypes_to_raw_pointer(ctx.tcx, source) else {
            return Ok(None);
        };
        let mir::Const::Val(ConstValue::Scalar(scalar), _) = *evaluated else {
            return Ok(None);
        };
        let Ok(integer) = scalar.try_to_scalar_int() else {
            // An image with provenance (a real allocation address) remains on
            // emit_const_alloc_addr.
            return Ok(None);
        };

        let refuse = |detail| format!("[TCG-RAW-ADDR-CONST] {detail}");
        if ctx.monomorphize_ty(evaluated.ty()) != source {
            return Err(refuse("original and evaluated Rust pointer types differ"));
        }
        let layout = ctx
            .tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(source))
            .map_err(|_| refuse("original raw-pointer layout is unavailable"))?;
        let pointer_size = ctx.tcx.data_layout.pointer_size();
        if pointer_size.bits() != u64::from(session_bits)
            || integer.size() != pointer_size
            || layout.size != pointer_size
            || !matches!(layout.backend_repr, rustc_abi::BackendRepr::Scalar(scalar)
                if matches!(scalar.primitive(), rustc_abi::Primitive::Pointer(_)))
        {
            return Err(refuse(
                "scalar, original thin layout and target pointer widths differ",
            ));
        }
        let actual = super::rust_ty_to_trust_ir_ty(ctx.tcx, source)?;
        if &actual != destination
            || super::rust_ty_to_trust_ir_ty(ctx.tcx, pointer).as_ref() != Ok(&actual)
            || !matches!(destination, Ty::PtrConst(_) | Ty::PtrMut(_))
            || !super::pointer_casts::is_thin_pointer(destination)
        {
            return Err(refuse(
                "requested carrier is not the original thin raw-pointer type \
                 or its newtype's",
            ));
        }
        let Some(integer_ty) = address_integer(session_bits) else {
            return Err(refuse("unsupported target pointer width"));
        };
        let address = spelled_address(integer.to_bits(integer.size()), session_bits)
            .ok_or_else(|| refuse("address image is wider than the target pointer"))?;
        Ok(Some(Self {
            integer: integer_ty,
            destination: actual,
            address,
        }))
    }

    fn emit(
        &self,
        block: &mut Block,
        result: ValueId,
        fresh: impl FnMut() -> ValueId,
    ) -> Result<(), String> {
        emit_transport(
            block,
            &self.integer,
            &self.destination,
            self.address,
            result,
            fresh,
        )
    }
}

/// `bits`, an unsigned address image of a `session_bits`-wide pointer, as the
/// canonical `Constant::Int` of the signed pointer-width integer
/// (two's complement, so `usize::MAX as *const T` is `-1`). `None` when the
/// image has bits above the pointer width.
fn spelled_address(bits: u128, session_bits: u32) -> Option<i128> {
    if session_bits == 0 || session_bits >= 128 || bits >> session_bits != 0 {
        return None;
    }
    let bits = i128::try_from(bits).ok()?;
    Some(super::int_const_spelled_in_width(bits, session_bits, true))
}

/// Emit `Const integer address`, then `IntToPtr` to the bare `Ptr` carrier and
/// `PtrToPtr` to the typed raw pointer `destination`, defining `result`.
/// Every carrier fact is re-checked before anything is allocated or emitted,
/// so a witness cannot outlive a session-width change.
fn emit_transport(
    block: &mut Block,
    integer: &Ty,
    destination: &Ty,
    address: i128,
    result: ValueId,
    mut fresh: impl FnMut() -> ValueId,
) -> Result<(), String> {
    let bits = super::session_pointer_bits();
    if integer.bit_width() != Some(bits)
        || address_integer(bits).as_ref() != Some(integer)
        || !matches!(destination, Ty::PtrConst(_) | Ty::PtrMut(_))
        || !super::pointer_casts::can_transport_address(&Ty::Ptr, destination)
        || spelled_address(address.rem_euclid(1i128 << bits) as u128, bits) != Some(address)
    {
        return Err("[TCG-RAW-ADDR-CONST] authenticated address carrier changed".into());
    }
    let word = fresh();
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: integer.clone(),
            value: Constant::Int(address),
        })
        .with_result(word),
    );
    super::pointer_casts::emit_pointer_integer_cast(
        block,
        CastOp::IntToPtr,
        integer.clone(),
        destination.clone(),
        word,
        result,
        fresh,
    )
}

pub(super) fn lower<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    block: &mut Block,
    source: RustTy<'tcx>,
    evaluated: &mir::Const<'tcx>,
    destination: &Ty,
    result: ValueId,
) -> Result<bool, String> {
    let Some(pointer) = AddressOnlyRawPointer::authenticate(
        ctx,
        source,
        evaluated,
        destination,
        super::session_pointer_bits(),
    )?
    else {
        return Ok(false);
    };
    pointer.emit(block, result, || ctx.fresh_value())?;
    Ok(true)
}

/// The value of the raw-pointer leaf `leaf_ty` of a constant aggregate whose
/// `width`-byte image decoded to `bits`, defined through the same transport as
/// [`lower`]. Returns `Ok(None)`, allocating and emitting nothing, for a leaf
/// that is not a thin typed raw pointer (`PtrConst` / `PtrMut`); the caller
/// keeps its own spelling for those, and a reference leaf is never transported.
///
/// Preconditions the caller establishes: the image carries no provenance (a
/// `Scalar::Ptr` with a relocation, or an allocation with any pointer
/// relocation, is refused before the decode), and `leaf_ty` comes from the
/// rustc layout walk of the constant's own type, in which the type mapper
/// produces `PtrConst` / `PtrMut` only for a thin `ty::RawPtr` field, alone or
/// under single-field newtypes over one (`NonNull`, `Unique`).
pub(super) fn lower_aggregate_leaf(
    block: &mut Block,
    leaf_ty: &Ty,
    bits: u128,
    width: u64,
    mut fresh: impl FnMut() -> ValueId,
) -> Result<Option<ValueId>, String> {
    if !matches!(leaf_ty, Ty::PtrConst(_) | Ty::PtrMut(_)) {
        return Ok(None);
    }
    let session_bits = super::session_pointer_bits();
    let refuse = |detail| format!("[TCG-RAW-ADDR-CONST] {detail}");
    if !super::pointer_casts::is_thin_pointer(leaf_ty)
        || width.checked_mul(8) != Some(u64::from(session_bits))
    {
        return Err(refuse(
            "aggregate raw-pointer leaf is not one target pointer wide",
        ));
    }
    let integer =
        address_integer(session_bits).ok_or_else(|| refuse("unsupported target pointer width"))?;
    let address = spelled_address(bits, session_bits)
        .ok_or_else(|| refuse("address image is wider than the target pointer"))?;
    let result = fresh();
    emit_transport(block, &integer, leaf_ty, address, result, fresh)?;
    Ok(Some(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::adapter::{AdapterError, validate_codegen_prerequisites};
    use trust_ir::{BlockId, FuncId, FuncTy, Function, Module};

    include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

    fn floor_module(destination: Ty, mut block: Block, result: ValueId) -> Module {
        let mut module = Module::new("original_address_only_raw_pointer");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![destination],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "address", signature, block.id);
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![result],
        }));
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        module
    }

    fn assert_transport(block: &Block, destination: &Ty, result: ValueId, expected: i128) {
        assert_eq!(block.body.len(), 3);
        let integer = match super::super::session_pointer_bits() {
            32 => Ty::I32,
            64 => Ty::I64,
            _ => panic!("supported source target"),
        };
        let word = block.body[0].results[0];
        let address = block.body[1].results[0];
        assert_eq!(
            block.body[0].inst,
            Inst::Const {
                ty: integer.clone(),
                value: Constant::Int(expected)
            }
        );
        assert_eq!(
            block.body[1].inst,
            Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: integer,
                dst_ty: Ty::Ptr,
                operand: word,
            }
        );
        assert_eq!(
            block.body[2].inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: destination.clone(),
                operand: address,
            }
        );
        assert_eq!(block.body[2].results, vec![result]);
    }

    const SOURCE: &str = r#"
const NULL_CONST: *const u8 = core::ptr::null();
const NULL_MUT: *mut u8 = core::ptr::null_mut();
const NONZERO: *mut u8 = 1usize as *mut u8;
const DANGLING: *const u64 = core::ptr::NonNull::<u64>::dangling().as_ptr();
const HIGH: *mut u8 = usize::MAX as *mut u8;
const NON_NULL: core::ptr::NonNull<u32> = core::ptr::NonNull::dangling();
pub struct Wrapped(core::ptr::NonNull<u16>, core::marker::PhantomData<u8>);
const WRAPPED: Wrapped = Wrapped(core::ptr::NonNull::dangling(), core::marker::PhantomData);
#[repr(transparent)]
pub struct Borrowed(&'static u16);
const BORROWED: Borrowed = Borrowed(&9);
const FAT: *const [u8] = core::ptr::slice_from_raw_parts(core::ptr::null(), 0);
static BYTE: u8 = 7;
const INTO_STATIC: *const u8 = &BYTE as *const u8;
pub fn null_const() -> *const u8 { NULL_CONST }
pub fn null_mut() -> *mut u8 { NULL_MUT }
pub fn nonzero() -> *mut u8 { NONZERO }
pub fn dangling() -> *const u64 { DANGLING }
pub fn high() -> *mut u8 { HIGH }
pub fn non_null() -> core::ptr::NonNull<u32> { NON_NULL }
pub fn wrapped() -> Wrapped { WRAPPED }
pub fn borrowed() -> Borrowed { BORROWED }
pub fn integer() -> usize { 0 }
pub fn reference() -> &'static u8 { &7 }
pub fn fat() -> *const [u8] { FAT }
pub fn into_static() -> *const u8 { INTO_STATIC }
"#;

    /// The address each actual source constant carries: `None` for a source
    /// that is not a provenance-free thin raw pointer.
    fn expected_address(name: &str) -> Option<i128> {
        match name {
            "null_const" | "null_mut" => Some(0),
            "nonzero" => Some(1),
            "dangling" => Some(8),
            "non_null" => Some(4),
            "wrapped" => Some(2),
            // usize::MAX at the signed pointer-width spelling.
            "high" => Some(-1),
            _ => None,
        }
    }

    fn check_original<'tcx>(tcx: rustc_middle::ty::TyCtxt<'tcx>) {
        for name in [
            "null_const",
            "null_mut",
            "nonzero",
            "dangling",
            "high",
            "non_null",
            "wrapped",
            "borrowed",
            "integer",
            "reference",
            "fat",
            "into_static",
        ] {
            let definition = tcx
                .hir_body_owners()
                .find(|id| tcx.item_name(id.to_def_id()).as_str() == name)
                .unwrap();
            let instance = ty::Instance::mono(tcx, definition.to_def_id());
            let body = tcx.instance_mir(instance.def);
            let operand = body
                .basic_blocks
                .iter()
                .flat_map(|data| &data.statements)
                .find_map(|statement| {
                    let mir::StatementKind::Assign(assignment) = &statement.kind else {
                        return None;
                    };
                    let mir::Rvalue::Use(operand @ mir::Operand::Constant(_), _) = &assignment.1
                    else {
                        return None;
                    };
                    Some(operand)
                })
                .unwrap_or_else(|| panic!("{name}: actual original constant operand"));
            let mir::Operand::Constant(constant) = operand else {
                unreachable!()
            };
            let mut ctx = MirLoweringCtx::new(name, tcx, instance);
            let source = ctx.monomorphize_ty(constant.const_.ty());
            let evaluated = ctx.eval_const_operand(constant);
            let destination = super::super::rust_ty_to_trust_ir_ty(tcx, source).unwrap();
            let receipt = AddressOnlyRawPointer::authenticate(
                &ctx,
                source,
                &evaluated,
                &destination,
                super::super::session_pointer_bits(),
            )
            .unwrap();
            if let Some(expected) = expected_address(name) {
                assert_eq!(
                    receipt.as_ref().map(|receipt| receipt.address),
                    Some(expected),
                    "{name}: genuine provenance-free source address"
                );
                let result = ctx.fresh_value();
                let mut block = Block::new(BlockId::new(0));
                super::super::lower_operand_inner(
                    &mut ctx,
                    body,
                    &mut block,
                    operand,
                    destination.clone(),
                    result,
                )
                .unwrap();
                assert_transport(&block, &destination, result, expected);
                validate_codegen_prerequisites(&floor_module(destination.clone(), block, result))
                    .unwrap();
                let mut block = Block::new(BlockId::new(0));
                let result =
                    super::super::lower_operand_to_value(&mut ctx, body, &mut block, operand)
                        .unwrap();
                assert_transport(&block, &destination, result, expected);
                validate_codegen_prerequisites(&floor_module(destination.clone(), block, result))
                    .unwrap();
                let wrong_width = if super::super::session_pointer_bits() == 64 {
                    32
                } else {
                    64
                };
                assert!(
                    AddressOnlyRawPointer::authenticate(
                        &ctx,
                        source,
                        &evaluated,
                        &destination,
                        wrong_width
                    )
                    .is_err()
                );
                for wrong in [
                    Ty::U64,
                    Ty::Ptr,
                    Ty::Ref(Box::new(Ty::U8)),
                    Ty::RefMut(Box::new(Ty::U8)),
                ] {
                    assert!(
                        AddressOnlyRawPointer::authenticate(
                            &ctx,
                            source,
                            &evaluated,
                            &wrong,
                            super::super::session_pointer_bits()
                        )
                        .is_err()
                    );
                }
            } else {
                assert!(
                    receipt.is_none(),
                    "{name}: unrelated actual source never gains an address witness"
                );
                let before = ctx.next_value;
                let mut block = Block::new(BlockId::new(0));
                assert!(
                    !lower(
                        &mut ctx,
                        &mut block,
                        source,
                        &evaluated,
                        &destination,
                        ValueId::new(999)
                    )
                    .unwrap()
                );
                assert!(block.body.is_empty());
                assert_eq!(ctx.next_value, before);
            }
        }
    }

    #[test]
    fn actual_rust_address_only_raw_pointer_authentication_and_both_operand_hooks() {
        const CHILD: &str = "BRIDGE_ADDRESS_ONLY_RAW_POINTER_TEST_CHILD";
        const MARKER: &str = "original Rust address-only raw-pointer controls checked";
        if std::env::var_os(CHILD).is_some() {
            extern crate rustc_interface;
            struct Callbacks;
            impl rustc_driver::Callbacks for Callbacks {
                fn config(&mut self, config: &mut rustc_interface::interface::Config) {
                    config.input = rustc_session::config::Input::Str {
                        name: rustc_span::FileName::Custom("address_only_raw_pointer.rs".into()),
                        input: SOURCE.into(),
                    };
                }
                fn after_analysis<'tcx>(
                    &mut self,
                    _: &rustc_interface::interface::Compiler,
                    tcx: ty::TyCtxt<'tcx>,
                ) -> rustc_driver::Compilation {
                    check_original(tcx);
                    eprintln!("{MARKER}");
                    rustc_driver::Compilation::Stop
                }
            }
            let sysroot = std::process::Command::new(BUILD_COMPILER)
                .args(["--print", "sysroot"])
                .output()
                .unwrap();
            assert!(
                sysroot.status.success(),
                "{}",
                String::from_utf8_lossy(&sysroot.stderr)
            );
            let arguments = vec![
                "trustc".into(),
                "--edition=2021".into(),
                "--crate-type=lib".into(),
                "--emit=metadata".into(),
                "-Ztrust-verify=off".into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout).unwrap().trim().into(),
                "-".into(),
            ];
            rustc_driver::run_compiler(&arguments, &mut Callbacks);
            return;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap()).args([
            "--exact", "raw_pointer_constant::tests::actual_rust_address_only_raw_pointer_authentication_and_both_operand_hooks", "--nocapture",
        ]).env(CHILD, "1").output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
        assert!(
            stderr.contains(MARKER),
            "assertions did not execute: {stderr}"
        );
        assert!(!stderr.contains("panicked"), "{stderr}");
    }

    #[test]
    fn numerical_zero_and_nonzero_typed_raw_pointer_literals_still_refuse() {
        for destination in [Ty::PtrConst(Box::new(Ty::U8)), Ty::PtrMut(Box::new(Ty::U8))] {
            for integer in [0, 1, 8, i128::MAX] {
                let mut block = Block::new(BlockId::new(0));
                block.body.push(
                    InstrNode::new(Inst::Const {
                        ty: destination.clone(),
                        value: Constant::Int(integer),
                    })
                    .with_result(ValueId::new(0)),
                );
                let error = validate_codegen_prerequisites(&floor_module(
                    destination.clone(),
                    block,
                    ValueId::new(0),
                ))
                .unwrap_err();
                assert!(
                    matches!(&error, AdapterError::TrustIrAdmissionRefused { error }
                    if error.contains("const type mismatch") && error.contains("got int")),
                    "{error:?}"
                );
            }
        }
    }

    #[test]
    fn aggregate_raw_pointer_leaf_transports_its_address_and_nothing_else() {
        let bits = super::super::session_pointer_bits();
        let width = u64::from(bits / 8);
        let all_ones = (1u128 << bits) - 1;
        for destination in [
            Ty::PtrConst(Box::new(Ty::U64)),
            Ty::PtrMut(Box::new(Ty::U8)),
        ] {
            for (image, expected) in [(0u128, 0i128), (8, 8), (all_ones, -1)] {
                let mut next = 0u32;
                let fresh = || {
                    next += 1;
                    ValueId::new(next)
                };
                let mut block = Block::new(BlockId::new(0));
                let result = lower_aggregate_leaf(&mut block, &destination, image, width, fresh)
                    .unwrap()
                    .expect("a typed raw-pointer leaf is transported");
                // The leaf's own value is allocated before the transport's word.
                assert_eq!(result, ValueId::new(1));
                assert_transport(&block, &destination, result, expected);
                validate_codegen_prerequisites(&floor_module(destination.clone(), block, result))
                    .unwrap();
            }
            // A leaf narrower than the target pointer, or an image with bits
            // above it, is refused by name rather than truncated.
            for (image, wrong_width) in [(8u128, width / 2), (1u128 << bits, width)] {
                let mut block = Block::new(BlockId::new(0));
                let error =
                    lower_aggregate_leaf(&mut block, &destination, image, wrong_width, || {
                        panic!("no value is allocated for a refused leaf")
                    })
                    .unwrap_err();
                assert!(error.starts_with("[TCG-RAW-ADDR-CONST]"), "{error}");
                assert!(block.body.is_empty());
            }
        }
        // A reference, the bare `Ptr` carrier and an integer leaf are not
        // transported: nothing is emitted and the caller keeps its spelling.
        for other in [
            Ty::Ref(Box::new(Ty::U8)),
            Ty::RefMut(Box::new(Ty::U8)),
            Ty::Ptr,
            Ty::U64,
        ] {
            let mut block = Block::new(BlockId::new(0));
            assert!(
                lower_aggregate_leaf(&mut block, &other, 8, width, || {
                    panic!("no value is allocated for a leaf that is not transported")
                })
                .unwrap()
                .is_none()
            );
            assert!(block.body.is_empty());
        }
    }
}
