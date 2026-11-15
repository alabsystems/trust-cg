// trust-cg-codegen/wasm/lower/value.rs - memory-carried values
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Lowering of values carried in linear memory ([`Carrier::Mem`]): structs,
//! tuples, enums, arrays, fat pointers and the 128-bit integers that are not
//! pair-carried ([`Carrier::Pair`], `pair.rs`). A pair crosses memory here
//! as its 16-byte image: two `i64` stores where a memory-carried value's
//! bytes are copied, two `i64` loads where they are aliased or copied in.
//!
//! Such a value's wasm local holds the ADDRESS of its bytes, and those bytes
//! are exactly its trust-ir memory image ([`super::super::layout`]). The one
//! invariant everything here maintains: **a memory-carried value's bytes are
//! written only by its own definition** (for a block parameter, by the edge
//! copies that bind it). An instruction that builds a new value
//! (`InsertField`, `MakeAggregate`, a `Load`, a call result, an edge into a
//! block parameter) writes its OWN home slot; an instruction that only views
//! an existing value (`ExtractField` of an aggregate lane, `Select`, `Copy`, a
//! pooled `Const`) aliases storage it does not write. That is what makes an
//! alias sound (see `owns_storage`). A lane read THROUGH a pointer carrier is
//! not a view of a value but a load from memory anything may later write, so
//! it owns and fills its own home, as a `Load` does (`extract_reads_through`). Two homes share frame bytes only when
//! neither value, nor any alias of it, can be read while the other is written
//! (`storage.rs`), so a shared home is still written only by the definition
//! whose value is live.
//!
//! It is also why a by-address argument can be handed without a copy to a
//! callee this lane compiled, when the linker cannot replace that body
//! (`interposable_linkage`): the callee only reads it. A by-address ENTRY
//! parameter is the one parameter an edge could write — a branch back to the
//! entry block rebinds it — so such a parameter (and one whose address may
//! escape the callee) is first copied into the callee's own home
//! (`Lowering::assign_locals`); the caller's storage is never written.

use trust_ir::{CastOp, Constant, Ty, ValueId};

use super::super::encode::{ValType, emit_i32_const, emit_local_get, emit_memarg, op};
use super::super::layout::{self, Carrier, EnumImage, EnumView, Lane};
use super::{Lowering, WasmLowerError, mem_ops, slot};

/// The i64 immediate carrying discriminant `disc` of an enum whose tag is at
/// most 64 bits wide (`layout::enum_image` refuses 128-bit tags, and every
/// effective discriminant fits the canonical tag repr): its low 64 bits — a
/// `u64` discriminant above `i64::MAX` is its two's-complement pattern. The
/// discriminant is reduced to the tag's canonical carrier afterwards, so the
/// truncation is exact; the range check keeps it fail-closed should either
/// invariant change.
fn disc_imm(disc: i128) -> Result<i64, WasmLowerError> {
    if (i128::from(i64::MIN)..=i128::from(u64::MAX)).contains(&disc) {
        Ok(disc as i64)
    } else {
        Err(WasmLowerError::UnsupportedType(format!(
            "enum discriminant {disc} is wider than 64 bits"
        )))
    }
}

impl Lowering<'_> {
    /// How `v` is carried.
    pub(super) fn carrier(&self, v: ValueId) -> Result<Carrier, WasmLowerError> {
        self.carriers
            .get(&v)
            .copied()
            .ok_or_else(|| WasmLowerError::UndefinedValue(format!("{v:?}")))
    }

    /// The local holding the address of `v`'s bytes: a memory-carried
    /// value's own local, or — under the pointer-carried aggregate convention
    /// (`super::is_pointer_carrier`) — the pointer itself (a raw 64-bit
    /// address is wrapped to its wasm32 value first).
    pub(super) fn addr_local(&mut self, v: ValueId) -> Result<u32, WasmLowerError> {
        match self.carrier(v)? {
            Carrier::Mem { .. } => Ok(slot(&self.locals, v)?.0),
            Carrier::Scalar(ValType::I32) if super::is_pointer_carrier(&self.value_ty(v)?) => {
                Ok(slot(&self.locals, v)?.0)
            }
            Carrier::Scalar(ValType::I64) if super::is_pointer_carrier(&self.value_ty(v)?) => {
                let raw = slot(&self.locals, v)?.0;
                let t = self.temp(ValType::I32);
                emit_local_get(&mut self.code, raw);
                self.code.push(op::I32_WRAP_I64);
                self.emit_local_set(t);
                Ok(t)
            }
            other => Err(WasmLowerError::UnsupportedInst(format!(
                "{v:?} is {other:?}, not memory-carried, in `{}`",
                self.func.name
            ))),
        }
    }

    /// Whether `v` is an aggregate carried by POINTER here (its actual type is
    /// a pointer carrier while an aggregate is expected).
    pub(super) fn pointer_carried(&self, v: ValueId) -> Result<bool, WasmLowerError> {
        Ok(!self.carrier(v)?.is_mem() && super::is_pointer_carrier(&self.value_ty(v)?))
    }

    /// `[addr] -> [value]`: load scalar `ty` from `addr + offset`.
    pub(super) fn emit_load(&mut self, ty: &Ty, offset: u32) -> Result<(), WasmLowerError> {
        let (load_op, _, align) = mem_ops(ty)?;
        self.code.push(load_op);
        emit_memarg(&mut self.code, align, offset);
        Ok(())
    }

    /// `[addr, value] -> []`: store scalar `ty` at `addr + offset`.
    pub(super) fn emit_store(&mut self, ty: &Ty, offset: u32) -> Result<(), WasmLowerError> {
        let (_, store_op, align) = mem_ops(ty)?;
        self.code.push(store_op);
        emit_memarg(&mut self.code, align, offset);
        Ok(())
    }

    /// Push `local + offset`.
    fn push_addr(&mut self, local: u32, offset: u32) {
        emit_local_get(&mut self.code, local);
        if offset != 0 {
            emit_i32_const(&mut self.code, offset as i32);
            self.code.push(op::I32_ADD);
        }
    }

    /// `memory.copy`: `size` bytes from `src + src_off` to `dst + dst_off`.
    /// Overlap is defined (memmove semantics), which the edge copies rely on.
    pub(super) fn emit_copy(&mut self, dst: u32, dst_off: u32, src: u32, src_off: u32, size: u32) {
        if size == 0 {
            return;
        }
        self.push_addr(dst, dst_off);
        self.push_addr(src, src_off);
        emit_i32_const(&mut self.code, size as i32);
        self.emit_bulk(op::MEMORY_COPY);
        self.code.push(0x00); // destination memory
        self.code.push(0x00); // source memory
    }

    /// The `0xfc`-prefixed bulk-memory opcode `sub`.
    pub(super) fn emit_bulk(&mut self, sub: u32) {
        self.code.push(op::FC_PREFIX);
        super::super::encode::write_uleb128(&mut self.code, u64::from(sub));
        self.features.insert("bulk-memory");
    }

    /// Refuse writing `value` into lane `field` (of type `lane_ty`) of a `ty`
    /// unless its carrier moves exactly the lane's bytes: a memory-carried
    /// value of another size would be copied over the lane's neighbours, or
    /// past the end of the aggregate.
    fn check_lane_write(
        &self,
        ty: &Ty,
        field: u32,
        value: ValueId,
        lane_ty: &Ty,
    ) -> Result<(), WasmLowerError> {
        let have = self.carrier(value)?;
        let lane = layout::carrier_of(self.module, lane_ty)?;
        if super::lane_carriers_agree(have, lane) {
            return Ok(());
        }
        Err(WasmLowerError::UnsupportedInst(format!(
            "InsertField lane {field} of {ty:?} is a {lane_ty:?} ({lane:?}); the value written is \
             a {:?} ({have:?}) in `{}`",
            self.value_ty(value)?,
            self.func.name
        )))
    }

    /// Refuse copying the `size`-byte image of an `op` result from the
    /// memory-carried `source` unless `source` holds exactly `size` bytes: a
    /// smaller operand would be read past its end.
    fn check_same_size(&self, source: ValueId, size: u32, op: &str) -> Result<(), WasmLowerError> {
        match self.carrier(source)? {
            Carrier::Mem { size: have, .. } if have == size => Ok(()),
            other => Err(WasmLowerError::UnsupportedInst(format!(
                "{op} builds a {size}-byte value from a {:?} ({other:?}) in `{}`",
                self.value_ty(source)?,
                self.func.name
            ))),
        }
    }

    /// Write `value` (any carrier) into memory at `dst + offset` as a `ty`.
    fn write_value_at(
        &mut self,
        dst: u32,
        offset: u32,
        value: ValueId,
        ty: &Ty,
    ) -> Result<(), WasmLowerError> {
        match self.carrier(value)? {
            Carrier::Void => Ok(()),
            Carrier::Scalar(_) => {
                let v = slot(&self.locals, value)?.0;
                emit_local_get(&mut self.code, dst);
                emit_local_get(&mut self.code, v);
                self.emit_store(ty, offset)
            }
            Carrier::Mem { size, .. } => {
                let src = self.addr_local(value)?;
                self.emit_copy(dst, offset, src, 0, size);
                Ok(())
            }
            Carrier::Pair => self.store_pair_at(dst, offset, value),
        }
    }

    /// Define result `dst` as the part `part` of the memory-carried value whose
    /// address is in `base` (plus `dyn_off`, a local holding a runtime byte
    /// offset, when the lane is dynamic). `through`: `base` is a POINTER
    /// carrier's pointee, not an SSA value's bytes, so a memory-carried part is
    /// copied into `dst`'s own home (`super::extract_reads_through`) instead of
    /// aliased — those bytes may be written while `dst` is live.
    fn read_part(
        &mut self,
        dst: ValueId,
        base: u32,
        dyn_off: Option<u32>,
        offset: u32,
        ty: &Ty,
        through: bool,
    ) -> Result<(), WasmLowerError> {
        let push_base = |s: &mut Self| {
            emit_local_get(&mut s.code, base);
            if let Some(d) = dyn_off {
                emit_local_get(&mut s.code, d);
                s.code.push(op::I32_ADD);
            }
        };
        match self.carrier(dst)? {
            Carrier::Void => Ok(()),
            Carrier::Scalar(_) => {
                let d = slot(&self.locals, dst)?.0;
                push_base(self);
                self.emit_load(ty, offset)?;
                self.emit_local_set(d);
                Ok(())
            }
            // A pair has no address to alias: its halves are read now, which
            // is the value an alias would read (the parent's bytes are written
            // only by the parent's own definition), and for a read through a
            // pointer is exactly the load.
            Carrier::Pair => self.load_pair_from(dst, offset, &push_base),
            Carrier::Mem { size, .. } if through => {
                // A lane read through a pointer is a load: copy the bytes into
                // the home `set_home_addr` pointed `dst` at. A result without
                // a home would copy to whatever its address local holds.
                if !self.home_offsets.contains_key(&dst) {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "{dst:?} reads a {ty:?} lane through a pointer but owns no home in `{}`",
                        self.func.name
                    )));
                }
                let d = self.addr_local(dst)?;
                let src = match dyn_off {
                    None => base,
                    Some(_) => {
                        let at = self.temp(ValType::I32);
                        push_base(self);
                        self.emit_local_set(at);
                        at
                    }
                };
                self.emit_copy(d, 0, src, offset, size);
                Ok(())
            }
            Carrier::Mem { .. } => {
                // An aggregate lane of an SSA value ALIASES its parent's bytes.
                let d = self.addr_local(dst)?;
                push_base(self);
                if offset != 0 {
                    emit_i32_const(&mut self.code, offset as i32);
                    self.code.push(op::I32_ADD);
                }
                self.emit_local_set(d);
                Ok(())
            }
        }
    }

    /// `ExtractField { ty, aggregate, field }`.
    pub(super) fn lower_extract_field(
        &mut self,
        result: ValueId,
        ty: &Ty,
        aggregate: ValueId,
        field: u32,
    ) -> Result<(), WasmLowerError> {
        let carried = self.pointer_carried(aggregate)?;
        // The historical spelling declares the AGGREGATE type (over a pointer
        // carrier, over a by-value aggregate of exactly that type, or over one
        // it reinterprets); the result is its lane.
        let operand_ty = self.value_ty(aggregate)?;
        let historical = super::is_aggregate_ty(ty)
            && (carried
                || &operand_ty == ty
                || super::extract_reinterprets(self.module, ty, &operand_ty, field));
        let (agg_ty, access_ty) = if historical {
            (ty.clone(), self.value_ty(result)?)
        } else {
            (self.value_ty(aggregate)?, ty.clone())
        };
        let ty = &access_ty;
        if self.carrier(aggregate)? == Carrier::Void {
            // A zero-sized aggregate has no bytes, so every lane is zero-sized
            // — except lane 0 of an enum, its discriminant: a type-level
            // constant there (a zero-sized enum can only be untagged; a direct
            // or niche encoding keeps its tag in bytes).
            if matches!(agg_ty, Ty::Enum(_)) && field == 0 {
                let image = layout::enum_image(self.module, &agg_ty)?;
                if !matches!(image.view, EnumView::Untagged { .. }) {
                    return Err(WasmLowerError::UnsupportedType(format!(
                        "zero-sized enum {agg_ty:?} keeps its tag in bytes"
                    )));
                }
                return self.bind_enum_discriminant(result, &agg_ty, ty, &image, None);
            }
            return Ok(());
        }
        let base = self.addr_local(aggregate)?;
        match layout::lane(self.module, &agg_ty, field, ty)? {
            Lane::At(part) => {
                // The result is carried as its own type says; a lane of
                // another size would make the result (an alias, for a
                // memory-carried one) name bytes outside the lane.
                let lane = layout::carrier_of(self.module, &part.ty)?;
                if !super::lane_carriers_agree(self.carrier(result)?, lane) {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "ExtractField lane {field} of {agg_ty:?} is a {:?} ({lane:?}); the result \
                         is declared {ty:?} ({:?}) in `{}`",
                        part.ty,
                        self.carrier(result)?,
                        self.func.name
                    )));
                }
                self.read_part(result, base, None, part.offset, &part.ty, carried)
            }
            Lane::EnumTag(image) => {
                self.bind_enum_discriminant(result, &agg_ty, ty, &image, Some(base))
            }
        }
    }

    /// Define `result` (read at `access_ty`) as the discriminant of an enum of
    /// type `agg_ty` whose bytes are at `base` (`None`: it has no bytes).
    fn bind_enum_discriminant(
        &mut self,
        result: ValueId,
        agg_ty: &Ty,
        access_ty: &Ty,
        image: &EnumImage,
        base: Option<u32>,
    ) -> Result<(), WasmLowerError> {
        if &image.tag_ty != access_ty {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "ExtractField lane 0 of {agg_ty:?} read at {access_ty:?}; its tag lane is {:?}",
                image.tag_ty
            )));
        }
        let d = slot(&self.locals, result)?.0;
        self.emit_enum_discriminant(image, base)?;
        self.emit_local_set(d);
        Ok(())
    }

    /// Push the discriminant of the enum whose bytes are at `base`, in the tag
    /// type's canonical carrier. Only an untagged enum's discriminant needs no
    /// bytes (`base` may then be `None`).
    fn emit_enum_discriminant(
        &mut self,
        image: &EnumImage,
        base: Option<u32>,
    ) -> Result<(), WasmLowerError> {
        let tag_ty = image.tag_ty.clone();
        let base = match (&image.view, base) {
            (EnumView::Untagged { variant }, _) => {
                let disc = image.discriminants[*variant];
                return self.emit_const(&tag_ty, &Constant::Int(disc));
            }
            (_, Some(base)) => base,
            (_, None) => {
                return Err(WasmLowerError::UnsupportedType(format!(
                    "the discriminant of {tag_ty:?}-tagged enum bytes that do not exist"
                )));
            }
        };
        match &image.view {
            EnumView::Untagged { .. } => unreachable!("handled above"),
            EnumView::Direct { offset } => {
                emit_local_get(&mut self.code, base);
                self.emit_load(&tag_ty, *offset)
            }
            EnumView::Niche {
                untagged_variant,
                start,
                end,
                niche_start,
                offset,
                bytes,
            } => {
                // lane = the niche bytes, zero-extended to i64.
                let lane_ty = match bytes {
                    1 => Ty::U8,
                    2 => Ty::U16,
                    4 => Ty::U32,
                    8 => Ty::U64,
                    other => {
                        return Err(WasmLowerError::UnsupportedType(format!(
                            "{other}-byte niche lane"
                        )));
                    }
                };
                emit_local_get(&mut self.code, base);
                self.emit_load(&lane_ty, *offset)?;
                if *bytes < 8 {
                    self.code.push(op::I64_EXTEND_I32_U);
                }
                let lane = self.temp(ValType::I64);
                self.emit_local_set(lane);
                // relative = (lane - niche_start) mod 2^(8*bytes)
                let mask: u64 = if *bytes >= 8 {
                    u64::MAX
                } else {
                    (1u64 << (bytes * 8)) - 1
                };
                let relative = self.temp(ValType::I64);
                emit_local_get(&mut self.code, lane);
                self.code.push(op::I64_CONST);
                super::super::encode::write_sleb128(&mut self.code, *niche_start as u64 as i64);
                self.code.push(op::I64_SUB);
                if *bytes < 8 {
                    self.code.push(op::I64_CONST);
                    super::super::encode::write_sleb128(&mut self.code, mask as i64);
                    self.code.push(op::I64_AND);
                }
                self.emit_local_set(relative);
                // variant = relative <= end - start ? start + relative : untagged
                let span = u64::from(end - start);
                let variant = self.temp(ValType::I64);
                emit_local_get(&mut self.code, relative);
                self.code.push(op::I64_CONST);
                super::super::encode::write_sleb128(&mut self.code, i64::from(*start));
                self.code.push(op::I64_ADD);
                self.code.push(op::I64_CONST);
                super::super::encode::write_sleb128(&mut self.code, *untagged_variant as i64);
                emit_local_get(&mut self.code, relative);
                self.code.push(op::I64_CONST);
                super::super::encode::write_sleb128(&mut self.code, span as i64);
                self.code.push(op::I64_LE_U);
                self.code.push(op::SELECT);
                self.emit_local_set(variant);
                // discriminant = discriminants[variant]
                self.emit_variant_to_discriminant(image, variant)?;
                // i64 -> the tag's carrier, canonical.
                let tag_repr = super::int_repr_of(&tag_ty).ok_or_else(|| {
                    WasmLowerError::UnsupportedType(format!("enum tag {tag_ty:?}"))
                })?;
                if tag_repr.carrier == ValType::I32 {
                    self.code.push(op::I32_WRAP_I64);
                }
                self.emit_canonicalize(tag_repr)
            }
        }
    }

    /// `[] -> [i64 discriminant]` for the runtime variant index in local
    /// `variant` (i64).
    fn emit_variant_to_discriminant(
        &mut self,
        image: &EnumImage,
        variant: u32,
    ) -> Result<(), WasmLowerError> {
        let d = &image.discriminants;
        // The common case — discriminant = index + k — is one add.
        if let Some(first) = d.first()
            && d.iter().enumerate().all(|(i, x)| *x == first + i as i128)
        {
            emit_local_get(&mut self.code, variant);
            if *first != 0 {
                // `index + first` wraps mod 2^64 in the i64 add, which is exact:
                // the caller keeps only the tag's (at most 64) low bits.
                let k = disc_imm(*first)?;
                self.code.push(op::I64_CONST);
                super::super::encode::write_sleb128(&mut self.code, k);
                self.code.push(op::I64_ADD);
            }
            return Ok(());
        }
        if d.len() > 256 {
            return Err(WasmLowerError::UnsupportedType(format!(
                "niche enum with {} irregular discriminants",
                d.len()
            )));
        }
        // A select chain: start from the last variant's discriminant and
        // override it for each earlier index.
        let last = disc_imm(*d.last().unwrap_or(&0))?;
        self.code.push(op::I64_CONST);
        super::super::encode::write_sleb128(&mut self.code, last);
        for (i, disc) in d.iter().enumerate().rev().skip(1) {
            let disc = disc_imm(*disc)?;
            let acc = self.temp(ValType::I64);
            self.emit_local_set(acc);
            self.code.push(op::I64_CONST);
            super::super::encode::write_sleb128(&mut self.code, disc);
            emit_local_get(&mut self.code, acc);
            emit_local_get(&mut self.code, variant);
            self.code.push(op::I64_CONST);
            super::super::encode::write_sleb128(&mut self.code, i as i64);
            self.code.push(op::I64_EQ);
            self.code.push(op::SELECT);
        }
        Ok(())
    }

    /// `InsertField { ty, aggregate, field, value }`: copy the aggregate into
    /// the result's home slot, then overwrite the lane.
    pub(super) fn lower_insert_field(
        &mut self,
        result: ValueId,
        ty: &Ty,
        aggregate: ValueId,
        field: u32,
        value: ValueId,
    ) -> Result<(), WasmLowerError> {
        let value_ty = self.value_ty(value)?;
        if self.pointer_carried(aggregate)? && self.value_ty(aggregate)? != *ty {
            // The bridge's write-THROUGH form (the native adapter's
            // `insert_field_writes_through`): the operand is a pointer to the
            // aggregate, the field is stored through it, and the result is
            // that same pointer.
            let ptr = self.addr_local(aggregate)?;
            match layout::lane(self.module, ty, field, &value_ty)? {
                Lane::At(part) => {
                    self.check_lane_write(ty, field, value, &part.ty)?;
                    self.write_value_at(ptr, part.offset, value, &part.ty)?;
                }
                Lane::EnumTag(_) => {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "InsertField lane 0 of {ty:?} rewrites an enum discriminant"
                    )));
                }
            }
            if let Ok((d, _)) = slot(&self.locals, result) {
                emit_local_get(&mut self.code, ptr);
                self.emit_local_set(d);
            }
            return Ok(());
        }
        let Carrier::Mem { size, .. } = self.carrier(result)? else {
            if matches!(ty, Ty::Enum(_)) && field == 0 {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "InsertField lane 0 of {ty:?} rewrites an enum discriminant, which trust-ir \
                     makes undefined behaviour; construct the variant with Const or MakeAggregate"
                )));
            }
            return Ok(()); // zero-sized
        };
        let dst = self.addr_local(result)?;
        if self.carrier(aggregate)?.is_mem() {
            self.check_same_size(aggregate, size, "InsertField")?;
            let src = self.addr_local(aggregate)?;
            self.emit_copy(dst, 0, src, 0, size);
        }
        match layout::lane(self.module, ty, field, &value_ty)? {
            Lane::At(part) => {
                self.check_lane_write(ty, field, value, &part.ty)?;
                self.write_value_at(dst, part.offset, value, &part.ty)
            }
            Lane::EnumTag(_) => Err(WasmLowerError::UnsupportedInst(format!(
                "InsertField lane 0 of {ty:?} rewrites an enum discriminant, which trust-ir \
                 makes undefined behaviour; construct the variant with Const or MakeAggregate"
            ))),
        }
    }

    /// `MakeAggregate { ty, variant, fields }`: write every lane into the
    /// result's home slot (and, for an enum, the variant's tag image).
    pub(super) fn lower_make_aggregate(
        &mut self,
        result: ValueId,
        ty: &Ty,
        variant: Option<u32>,
        fields: &[ValueId],
    ) -> Result<(), WasmLowerError> {
        if !self.carrier(result)?.is_mem() {
            return Ok(());
        }
        let dst = self.addr_local(result)?;
        let parts: Vec<layout::Part> = match ty {
            Ty::Struct(_) | Ty::Tuple(_) => layout::record_fields(self.module, ty)?,
            Ty::Array(_, _) => {
                let (elem, stride, len) = layout::array_elem(self.module, ty)?;
                (0..len as u32)
                    .map(|i| layout::Part {
                        offset: i * stride,
                        ty: elem.clone(),
                    })
                    .collect()
            }
            Ty::Enum(_) => {
                let image = layout::enum_image(self.module, ty)?;
                let v = variant.ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "MakeAggregate of enum {ty:?} names no variant"
                    ))
                })? as usize;
                let parts = image.variants.get(v).cloned().ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!("{ty:?} has no variant {v}"))
                })?;
                if let Some((offset, width, value)) = layout::tag_write(self.module, ty, &image, v)?
                {
                    self.emit_store_int_const(dst, offset, width, value)?;
                }
                parts
            }
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "MakeAggregate of {other:?}"
                )));
            }
        };
        if parts.len() != fields.len() {
            return Err(WasmLowerError::ArityMismatch(format!(
                "MakeAggregate {ty:?}: {} lanes for {} fields",
                fields.len(),
                parts.len()
            )));
        }
        for (part, &field) in parts.iter().zip(fields) {
            self.write_value_at(dst, part.offset, field, &part.ty)?;
        }
        Ok(())
    }

    /// `ArraySplat { ty, value }` (trust-ir v50): `n` copies of one element
    /// into the result's home slot, in code size constant in `n` (the
    /// interpreter's lazy `ArrayValue::splat` reads `value` at every lane).
    /// The element is written ONCE into lane 0, then copied by doubling:
    /// `[0, k*stride)` onto `[k*stride, 2k*stride)` (the last copy clipped),
    /// so at most ceil(log2 n) `memory.copy`s, disjoint because `k*stride` is
    /// at least the copy's length, moving exactly the `(n-1)*stride` bytes a
    /// lane loop moves. The element's carrier must be the lane's, as
    /// `InsertElement` requires.
    pub(super) fn lower_array_splat(
        &mut self,
        result: ValueId,
        ty: &Ty,
        value: ValueId,
    ) -> Result<(), WasmLowerError> {
        let Carrier::Mem { size, .. } = self.carrier(result)? else {
            return Ok(()); // zero-sized
        };
        let (elem, stride, len) = layout::array_elem(self.module, ty)?;
        let elem_carrier = layout::carrier_of(self.module, &elem)?;
        if !super::lane_carriers_agree(self.carrier(value)?, elem_carrier) {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "ArraySplat of a {:?} ({:?}) into {ty:?}, whose element is a {elem:?} \
                 ({elem_carrier:?}), in `{}`",
                self.value_ty(value)?,
                self.carrier(value)?,
                self.func.name
            )));
        }
        let total = u64::from(stride)
            .checked_mul(len)
            .filter(|total| *total == u64::from(size))
            .ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!(
                    "ArraySplat {ty:?} in `{}`: {len} lanes of stride {stride} are not its \
                     {size}-byte home slot",
                    self.func.name
                ))
            })?;
        if total == 0 {
            return Ok(());
        }
        let dst = self.addr_local(result)?;
        self.write_value_at(dst, 0, value, &elem)?;
        let mut done = u64::from(stride);
        while done < total {
            let chunk = done.min(total - done);
            // Both fit: `done + chunk <= total == size`, a `u32`.
            self.emit_copy(dst, done as u32, dst, 0, chunk as u32);
            done += chunk;
        }
        Ok(())
    }

    /// Store the constant integer `value` as `width` bytes at `dst + offset`.
    fn emit_store_int_const(
        &mut self,
        dst: u32,
        offset: u32,
        width: u32,
        value: u128,
    ) -> Result<(), WasmLowerError> {
        let ty = match width {
            1 => Ty::U8,
            2 => Ty::U16,
            4 => Ty::U32,
            8 => Ty::U64,
            other => {
                return Err(WasmLowerError::UnsupportedType(format!(
                    "{other}-byte tag store"
                )));
            }
        };
        emit_local_get(&mut self.code, dst);
        self.emit_const(&ty, &Constant::Int(value as i128))?;
        self.emit_store(&ty, offset)
    }

    /// `ExtractElement { ty, array, index }`: the element at a RUNTIME index.
    pub(super) fn lower_extract_element(
        &mut self,
        result: ValueId,
        ty: &Ty,
        array: ValueId,
        index: ValueId,
    ) -> Result<(), WasmLowerError> {
        let arr_ty = self.value_ty(array)?;
        if self.carrier(array)? == Carrier::Void {
            return Ok(());
        }
        let (elem, stride, _) = layout::array_elem(self.module, &arr_ty)?;
        if &elem != ty {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "ExtractElement at {ty:?} of {arr_ty:?}"
            )));
        }
        let through = self.pointer_carried(array)?;
        let base = self.addr_local(array)?;
        let off = self.emit_index_offset(index, stride)?;
        self.read_part(result, base, Some(off), 0, &elem, through)
    }

    /// `InsertElement { ty, array, index, value }`.
    pub(super) fn lower_insert_element(
        &mut self,
        result: ValueId,
        ty: &Ty,
        array: ValueId,
        index: ValueId,
        value: ValueId,
    ) -> Result<(), WasmLowerError> {
        let Carrier::Mem { size, .. } = self.carrier(result)? else {
            return Ok(());
        };
        let (elem, stride, _) = layout::array_elem(self.module, ty)?;
        if self.carrier(array)?.is_mem() {
            self.check_same_size(array, size, "InsertElement")?;
        }
        let elem_carrier = layout::carrier_of(self.module, &elem)?;
        if !super::lane_carriers_agree(self.carrier(value)?, elem_carrier) {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "InsertElement of a {:?} ({:?}) into {ty:?}, whose element is a {elem:?} \
                 ({elem_carrier:?}), in `{}`",
                self.value_ty(value)?,
                self.carrier(value)?,
                self.func.name
            )));
        }
        let dst = self.addr_local(result)?;
        let src = self.addr_local(array)?;
        self.emit_copy(dst, 0, src, 0, size);
        let off = self.emit_index_offset(index, stride)?;
        // A scratch address local: dst + index * stride.
        let at = self.temp(ValType::I32);
        emit_local_get(&mut self.code, dst);
        emit_local_get(&mut self.code, off);
        self.code.push(op::I32_ADD);
        self.emit_local_set(at);
        self.write_value_at(at, 0, value, &elem)
    }

    /// `[] -> [i32]`: an integer operand of ANY width used as an index or a
    /// byte count — its value modulo 2^32 (a narrow carrier already is: it is
    /// the value sign- or zero-extended, invariant N).
    ///
    /// Exact on every input trust-ir defines: a wasm32 address, an in-range
    /// element index and a byte count that fits the address space are all
    /// below 2^32, and a negative or wider value makes the access undefined
    /// behaviour (`interpret.rs`: `eval_gep` / `runtime_index` refuse a
    /// negative index, and a result past 2^32 - 1 is UB on wasm32), so only
    /// the low 32 bits of a defined operand matter. A 128-bit operand is
    /// memory-carried: its local holds the ADDRESS of its bytes, so the low
    /// word is loaded, never the address itself used as the value.
    pub(super) fn emit_index_i32(&mut self, v: ValueId, what: &str) -> Result<(), WasmLowerError> {
        let ity = self.value_ty(v)?;
        if !ity.is_integer() && !matches!(ity, Ty::Usize | Ty::Isize) {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "{what} of type {ity:?} in `{}` (an index or byte count is an integer)",
                self.func.name
            )));
        }
        match self.carrier(v)? {
            Carrier::Mem { .. } if super::wide::is_wide(&ity) => {
                let a = self.addr_local(v)?;
                emit_local_get(&mut self.code, a);
                self.emit_load(&Ty::U32, 0)
            }
            Carrier::Pair => {
                let (lo, _) = self.pair_of(v)?;
                emit_local_get(&mut self.code, lo);
                self.code.push(op::I32_WRAP_I64);
                Ok(())
            }
            Carrier::Scalar(vt) => {
                let l = slot(&self.locals, v)?.0;
                emit_local_get(&mut self.code, l);
                match vt {
                    ValType::I32 => Ok(()),
                    ValType::I64 => {
                        self.code.push(op::I32_WRAP_I64);
                        Ok(())
                    }
                    other => Err(WasmLowerError::UnsupportedInst(format!(
                        "{what} carried as {other:?} in `{}`",
                        self.func.name
                    ))),
                }
            }
            other => Err(WasmLowerError::UnsupportedInst(format!(
                "{what} of type {ity:?} carried as {other:?} in `{}`",
                self.func.name
            ))),
        }
    }

    /// A local holding `index * stride` as an i32 byte offset (the index read
    /// by [`Self::emit_index_i32`]).
    fn emit_index_offset(&mut self, index: ValueId, stride: u32) -> Result<u32, WasmLowerError> {
        self.emit_index_i32(index, "element index")?;
        if stride != 1 {
            emit_i32_const(&mut self.code, stride as i32);
            self.code.push(op::I32_MUL);
        }
        let off = self.temp(ValType::I32);
        self.emit_local_set(off);
        Ok(off)
    }

    /// A memory-carried `Const`: its image lives in the constant pool.
    pub(super) fn lower_mem_const(&mut self, result: ValueId) -> Result<(), WasmLowerError> {
        let addr = *self
            .const_pool
            .get(&(self.func.id, result))
            .ok_or_else(|| {
                WasmLowerError::UnsupportedConstantData(format!(
                    "{result:?} in `{}` has no pooled image",
                    self.func.name
                ))
            })?;
        let d = self.addr_local(result)?;
        self.emit_data_addr(addr, 0);
        self.emit_local_set(d);
        Ok(())
    }

    /// `Load` of a memory-carried type: copy the bytes into the home slot.
    pub(super) fn lower_mem_load(
        &mut self,
        result: ValueId,
        ptr: ValueId,
    ) -> Result<(), WasmLowerError> {
        let Carrier::Mem { size, .. } = self.carrier(result)? else {
            return Ok(());
        };
        let dst = self.addr_local(result)?;
        let p = slot(&self.locals, ptr)?.0;
        self.emit_copy(dst, 0, p, 0, size);
        Ok(())
    }

    /// `Copy` / `Select` of a memory-carried value alias an operand's bytes;
    /// a pair's copy is a copy of its two locals.
    pub(super) fn alias(&mut self, result: ValueId, source: ValueId) -> Result<(), WasmLowerError> {
        match self.carrier(result)? {
            Carrier::Void => Ok(()),
            Carrier::Pair => self.copy_pair(result, source),
            Carrier::Mem { .. } => {
                let s = self.addr_local(source)?;
                let d = self.addr_local(result)?;
                emit_local_get(&mut self.code, s);
                self.emit_local_set(d);
                Ok(())
            }
            Carrier::Scalar(_) => {
                let s = slot(&self.locals, source)?.0;
                let d = slot(&self.locals, result)?.0;
                emit_local_get(&mut self.code, s);
                self.emit_local_set(d);
                Ok(())
            }
        }
    }

    /// `PtrData` / `PtrMetadata` / `PtrFromParts`.
    pub(super) fn lower_ptr_data(
        &mut self,
        result: ValueId,
        ptr_ty: &Ty,
        ptr: ValueId,
    ) -> Result<(), WasmLowerError> {
        if matches!(ptr_ty, Ty::FatPtr(_)) {
            let (data, _) = layout::fat_ptr_lanes(ptr_ty)?;
            let base = self.addr_local(ptr)?;
            self.read_part(result, base, None, data.offset, &data.ty, false)
        } else {
            self.alias(result, ptr)
        }
    }

    pub(super) fn lower_ptr_metadata(
        &mut self,
        result: ValueId,
        ptr_ty: &Ty,
        ptr: ValueId,
    ) -> Result<(), WasmLowerError> {
        if matches!(ptr_ty, Ty::FatPtr(_)) {
            let (_, meta) = layout::fat_ptr_lanes(ptr_ty)?;
            let base = self.addr_local(ptr)?;
            self.read_part(result, base, None, meta.offset, &meta.ty, false)
        } else {
            // A thin pointer's metadata is `()`.
            Ok(())
        }
    }

    pub(super) fn lower_ptr_from_parts(
        &mut self,
        result: ValueId,
        ptr_ty: &Ty,
        data: ValueId,
        metadata: ValueId,
    ) -> Result<(), WasmLowerError> {
        if !matches!(ptr_ty, Ty::FatPtr(_)) {
            return self.alias(result, data);
        }
        let (d, m) = layout::fat_ptr_lanes(ptr_ty)?;
        let dst = self.addr_local(result)?;
        self.write_value_at(dst, d.offset, data, &d.ty)?;
        self.write_value_at(dst, m.offset, metadata, &m.ty)
    }

    /// Copy memory-carried edge argument `arg` into block parameter `param`'s
    /// home slot.
    pub(super) fn copy_edge_arg(
        &mut self,
        param: ValueId,
        arg: ValueId,
    ) -> Result<(), WasmLowerError> {
        let Carrier::Mem { size, .. } = self.carrier(param)? else {
            return Ok(());
        };
        let dst = self.addr_local(param)?;
        let src = self.addr_local(arg)?;
        self.emit_copy(dst, 0, src, 0, size);
        Ok(())
    }

    /// The two-phase edge copy for a block with several memory-carried
    /// parameters: every argument into its parameter's staging slot, then every
    /// staging slot into the parameter.
    pub(super) fn copy_edge_args_staged(
        &mut self,
        pairs: &[(ValueId, ValueId)],
    ) -> Result<(), WasmLowerError> {
        let base = self
            .frame
            .map(|f| f.base_local)
            .ok_or_else(|| WasmLowerError::UnsupportedInst("staging without a frame".into()))?;
        for &(param, arg) in pairs {
            let Carrier::Mem { size, .. } = self.carrier(param)? else {
                continue;
            };
            let stage = *self.staging_offsets.get(&param).ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!("{param:?} has no staging slot"))
            })?;
            let src = self.addr_local(arg)?;
            self.emit_copy(base, stage, src, 0, size);
        }
        for &(param, _) in pairs {
            let Carrier::Mem { size, .. } = self.carrier(param)? else {
                continue;
            };
            let stage = self.staging_offsets[&param];
            let dst = self.addr_local(param)?;
            self.emit_copy(dst, 0, base, stage, size);
        }
        Ok(())
    }

    /// A `Cast` whose source or destination is memory- or pair-carried:
    /// 128-bit integer widening and narrowing, conversions between a 128-bit
    /// integer and `f32`/`f64` (inline, see `wide.rs`), and same-size
    /// reinterpretation (`Bitcast` / `Transmute`) between any two carriers.
    pub(super) fn lower_mem_cast(
        &mut self,
        result: ValueId,
        cop: CastOp,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: ValueId,
    ) -> Result<(), WasmLowerError> {
        let src_c = self.carrier(operand)?;
        let dst_c = self.carrier(result)?;
        let refuse =
            || WasmLowerError::UnsupportedInst(format!("Cast::{cop:?} {src_ty:?} -> {dst_ty:?}"));
        let wide = |t: &Ty| matches!(t, Ty::I128 | Ty::U128);
        match cop {
            CastOp::ZExt | CastOp::SExt if wide(dst_ty) && !wide(src_ty) => {
                // lo = the source at 64 bits (its own signedness view), hi =
                // 0 or the sign of lo.
                let repr = super::int_repr_of(src_ty).ok_or_else(refuse)?;
                let src = slot(&self.locals, operand)?.0;
                let view = if cop == CastOp::SExt {
                    super::IntView::Signed
                } else {
                    super::IntView::Unsigned
                };
                let lo = self.temp(ValType::I64);
                emit_local_get(&mut self.code, src);
                self.emit_view(repr, view)?;
                if repr.carrier == ValType::I32 {
                    self.code.push(if cop == CastOp::SExt {
                        op::I64_EXTEND_I32_S
                    } else {
                        op::I64_EXTEND_I32_U
                    });
                }
                self.emit_local_set(lo);
                let push_hi = |s: &mut Self| {
                    if cop == CastOp::SExt {
                        emit_local_get(&mut s.code, lo);
                        s.code.push(op::I64_CONST);
                        super::super::encode::write_sleb128(&mut s.code, 63);
                        s.code.push(op::I64_SHR_S);
                    } else {
                        s.code.push(op::I64_CONST);
                        super::super::encode::write_sleb128(&mut s.code, 0);
                    }
                };
                if dst_c == Carrier::Pair {
                    let (dlo, dhi) = self.pair_of(result)?;
                    emit_local_get(&mut self.code, lo);
                    self.emit_local_set(dlo);
                    push_hi(self);
                    self.emit_local_set(dhi);
                    return Ok(());
                }
                let dst = self.addr_local(result)?;
                emit_local_get(&mut self.code, dst);
                emit_local_get(&mut self.code, lo);
                self.emit_store(&Ty::U64, 0)?;
                emit_local_get(&mut self.code, dst);
                push_hi(self);
                self.emit_store(&Ty::U64, 8)
            }
            CastOp::Trunc if wide(src_ty) && !wide(dst_ty) => {
                let repr = super::int_repr_of(dst_ty).ok_or_else(refuse)?;
                let src = self.wide_source(operand)?;
                let dst = slot(&self.locals, result)?.0;
                self.push_wide_half(src, false)?;
                if repr.carrier == ValType::I32 {
                    self.code.push(op::I32_WRAP_I64);
                }
                self.emit_canonicalize(repr)?;
                self.emit_local_set(dst);
                Ok(())
            }
            // The signedness is the OP's, as the reference interpreter reads
            // it (`fptosi.sat f64 -> u128` clamps to the i128 range; `sitofp`
            // of a `u128` reads it signed), never the integer type's.
            CastOp::FPToSI | CastOp::FPToSISat | CastOp::FPToUI | CastOp::FPToUISat
                if wide(dst_ty) && matches!(src_ty, Ty::F32 | Ty::F64) =>
            {
                let signed = matches!(cop, CastOp::FPToSI | CastOp::FPToSISat);
                self.lower_float_to_wide(result, signed, src_ty, operand)
            }
            CastOp::SIToFP | CastOp::UIToFP
                if wide(src_ty) && matches!(dst_ty, Ty::F32 | Ty::F64) =>
            {
                self.lower_wide_to_float(result, cop == CastOp::SIToFP, dst_ty, operand)
            }
            CastOp::Bitcast | CastOp::Transmute | CastOp::ZExt | CastOp::SExt | CastOp::Trunc => {
                // Same-size reinterpretation (a 128-bit resize to 128 bits is
                // the identity on the bytes).
                let (ss, _) = layout::size_align(self.module, src_ty)?;
                let (ds, _) = layout::size_align(self.module, dst_ty)?;
                if ss != ds {
                    return Err(refuse());
                }
                match (src_c, dst_c) {
                    (Carrier::Mem { size, .. }, Carrier::Mem { .. }) => {
                        let src = self.addr_local(operand)?;
                        let dst = self.addr_local(result)?;
                        self.emit_copy(dst, 0, src, 0, size);
                        Ok(())
                    }
                    // A pair on either side: 16 bytes (checked above) moved
                    // as the two halves of their little-endian image.
                    (Carrier::Pair, Carrier::Pair | Carrier::Mem { .. })
                    | (Carrier::Mem { .. }, Carrier::Pair) => {
                        let h = self.load_halves(operand)?;
                        self.store_halves(result, h)
                    }
                    (Carrier::Scalar(_), Carrier::Mem { .. }) => {
                        let src = slot(&self.locals, operand)?.0;
                        let dst = self.addr_local(result)?;
                        emit_local_get(&mut self.code, dst);
                        emit_local_get(&mut self.code, src);
                        self.emit_store(src_ty, 0)
                    }
                    (Carrier::Mem { .. }, Carrier::Scalar(_)) => {
                        let src = self.addr_local(operand)?;
                        let dst = slot(&self.locals, result)?.0;
                        emit_local_get(&mut self.code, src);
                        self.emit_load(dst_ty, 0)?;
                        self.emit_local_set(dst);
                        Ok(())
                    }
                    _ => Err(refuse()),
                }
            }
            _ => Err(refuse()),
        }
    }
}
