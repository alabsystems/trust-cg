// trust-cg-codegen/wasm/lower/calls.rs - calls, returns and edge arguments
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Moving values across calls, returns and CFG edges, lane by lane
//! ([`super::abi`]).
//!
//! * A by-address argument is the ADDRESS of the argument's bytes. A callee
//!   whose body this lane compiled, and that every call reaches, only reads
//!   it (see `value.rs`; a by-address entry parameter an edge could rebind is
//!   copied into the callee's own home first), so the caller's own storage is
//!   passed. A FOREIGN callee — an import (host or linker-resolved code), a
//!   definition the linker may replace (`interposable_linkage`), or any
//!   indirect-call target — may write to its by-address parameter (the C ABI
//!   hands it a copy it owns), so the caller passes a fresh copy in its frame.
//! * An `sret` result is written by the callee straight into the call
//!   result's home slot (or a scratch slot when the result is unused or
//!   pair-carried, a pair then loaded from it); the values of a multi-value
//!   return are written into a scratch buffer and bound from it.
//! * A pair-carried 128-bit argument is its two halves (`Split128`), and a
//!   pair-carried 128-bit return value is stored into the `sret` buffer.
//! * Narrow scalar results are re-canonicalized (invariant N): the callee may
//!   be a host import whose return value is not ours to trust.
//! * A direct call to a function the object routes through its internal entry
//!   (`lower.rs`, `internal_abi_plan`) uses the internal ABI
//!   ([`abi::lower_internal_sig`]): the results come back as wasm values, a
//!   128-bit one as its two halves, bound straight into the result's pair
//!   locals or stored into its home; the function's own `return` pushes them.
//!   Every other call, and every function pointer, uses the C form.

use trust_ir::{CallingConv, FuncId, FuncTy, FuncTyId, Ty, ValueId};

use super::super::encode::{ValType, emit_i32_const, emit_local_get, op};
use super::super::layout::Carrier;
use super::abi::{self, ParamLane, RetLane, WasmSig};
use super::{Lowering, WasmLowerError, slot};

impl Lowering<'_> {
    /// Push the wasm arguments of a call: the `sret` destination (if any),
    /// then each parameter's lane.
    fn push_call_args(
        &mut self,
        site: (usize, usize),
        sig: &WasmSig,
        args: &[ValueId],
        results: &[ValueId],
        foreign: bool,
    ) -> Result<(), WasmLowerError> {
        if args.len() != sig.params.len() {
            return Err(WasmLowerError::ArityMismatch(format!(
                "call in `{}` passes {} arguments to a {}-parameter signature",
                self.func.name,
                args.len(),
                sig.params.len()
            )));
        }
        if sig.sret {
            // A single memory-carried result is written straight into its home
            // slot; anything else (an unused result, or the values of a
            // multi-value return) goes through the call site's scratch buffer.
            let direct = sig
                .direct_sret_index()
                .and_then(|i| results.get(i).copied())
                .filter(|r| !self.is_pair(*r));
            match direct {
                Some(r) => {
                    let a = self.addr_local(r)?;
                    emit_local_get(&mut self.code, a);
                }
                None => {
                    let off = *self.sret_scratch.get(&site).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "unused sret result in `{}` has no scratch slot",
                            self.func.name
                        ))
                    })?;
                    let base = self.frame_base()?;
                    emit_local_get(&mut self.code, base);
                    emit_i32_const(&mut self.code, off as i32);
                    self.code.push(op::I32_ADD);
                }
            }
        }
        for (ai, (lane, &arg)) in sig.params.iter().zip(args).enumerate() {
            match lane {
                ParamLane::Void => {}
                ParamLane::Scalar(_) => {
                    let a = slot(&self.locals, arg)?.0;
                    emit_local_get(&mut self.code, a);
                }
                ParamLane::ByAddr { size } => {
                    let src = self.addr_local(arg)?;
                    match (
                        foreign,
                        self.arg_copy_offsets.get(&(site.0, site.1, ai)).copied(),
                    ) {
                        (true, Some(off)) => {
                            let base = self.frame_base()?;
                            self.emit_copy(base, off, src, 0, *size);
                            emit_local_get(&mut self.code, base);
                            emit_i32_const(&mut self.code, off as i32);
                            self.code.push(op::I32_ADD);
                        }
                        // `compute_frame` plans a copy slot for every
                        // by-address lane of a foreign call; passing the
                        // caller's own storage instead would let the callee
                        // write it.
                        (true, None) => {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "by-address argument {ai} of a foreign call in `{}` has no \
                                 frame copy slot",
                                self.func.name
                            )));
                        }
                        (false, _) => emit_local_get(&mut self.code, src),
                    }
                }
                ParamLane::Singleton { offset, ty, .. } => {
                    let src = self.addr_local(arg)?;
                    emit_local_get(&mut self.code, src);
                    self.emit_load(ty, *offset)?;
                }
                ParamLane::Split128 { offset: 0 } if self.is_pair(arg) => {
                    let (lo, hi) = self.pair_of(arg)?;
                    emit_local_get(&mut self.code, lo);
                    emit_local_get(&mut self.code, hi);
                }
                ParamLane::Split128 { offset } => {
                    let src = self.addr_local(arg)?;
                    emit_local_get(&mut self.code, src);
                    self.emit_load(&Ty::U64, *offset)?;
                    emit_local_get(&mut self.code, src);
                    self.emit_load(&Ty::U64, offset + 8)?;
                }
            }
        }
        Ok(())
    }

    /// Bind the results a call left on the stack (last result on top), then
    /// the scalars of a multi-value return from the call site's sret buffer.
    fn bind_call_results(
        &mut self,
        site: (usize, usize),
        sig: &WasmSig,
        ret_tys: &[Ty],
        results: &[ValueId],
    ) -> Result<(), WasmLowerError> {
        for (i, lane) in sig.rets.iter().enumerate().rev() {
            match lane {
                RetLane::Sret { .. } => {
                    // A pair-carried result was returned into the call site's
                    // scratch slot (`push_call_args`).
                    if let Some(&r) = results.get(i)
                        && self.is_pair(r)
                    {
                        let off = *self.sret_scratch.get(&site).ok_or_else(|| {
                            WasmLowerError::UnsupportedInst(format!(
                                "pair-carried sret result in `{}` has no scratch slot",
                                self.func.name
                            ))
                        })?;
                        let base = self.frame_base()?;
                        self.load_pair_from(r, off, &|s: &mut Self| {
                            emit_local_get(&mut s.code, base)
                        })?;
                    }
                }
                RetLane::Void | RetLane::Field { .. } => {}
                // The halves are on the stack, the high one on top.
                RetLane::Wide => match results.get(i) {
                    Some(&r) if self.is_pair(r) => {
                        let (lo, hi) = self.pair_of(r)?;
                        self.emit_local_set(hi);
                        self.emit_local_set(lo);
                    }
                    Some(&r) => {
                        let hi = self.temp(ValType::I64);
                        self.emit_local_set(hi);
                        let lo = self.temp(ValType::I64);
                        self.emit_local_set(lo);
                        let a = self.addr_local(r)?;
                        for (half, offset) in [(lo, 0), (hi, 8)] {
                            emit_local_get(&mut self.code, a);
                            emit_local_get(&mut self.code, half);
                            self.emit_store(&Ty::U64, offset)?;
                        }
                    }
                    None => {
                        self.code.push(op::DROP);
                        self.code.push(op::DROP);
                    }
                },
                RetLane::Scalar(_) => match results.get(i) {
                    Some(r) => {
                        if let Some(ty) = ret_tys.get(i) {
                            self.canonicalize_result(ty)?;
                        }
                        let d = slot(&self.locals, *r)?.0;
                        self.emit_local_set(d);
                    }
                    None => self.code.push(op::DROP),
                },
                RetLane::Singleton { vt, offset, ty } => match results.get(i) {
                    Some(r) => {
                        let t = self.temp(*vt);
                        self.emit_local_set(t);
                        let a = self.addr_local(*r)?;
                        emit_local_get(&mut self.code, a);
                        emit_local_get(&mut self.code, t);
                        self.emit_store(ty, *offset)?;
                    }
                    None => self.code.push(op::DROP),
                },
            }
        }
        for (i, lane) in sig.rets.iter().enumerate() {
            let RetLane::Field { offset, ty } = lane else {
                continue;
            };
            let Some(r) = results.get(i) else { continue };
            let off = *self.sret_scratch.get(&site).ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!(
                    "multi-value result in `{}` has no scratch buffer",
                    self.func.name
                ))
            })?;
            let base = self.frame_base()?;
            match self.carrier(*r)? {
                Carrier::Mem { size, .. } => {
                    let d = self.addr_local(*r)?;
                    self.emit_copy(d, 0, base, off + offset, size);
                }
                Carrier::Pair => {
                    self.load_pair_from(*r, off + offset, &|s: &mut Self| {
                        emit_local_get(&mut s.code, base)
                    })?;
                }
                Carrier::Scalar(_) => {
                    let d = slot(&self.locals, *r)?.0;
                    emit_local_get(&mut self.code, base);
                    self.emit_load(ty, off + offset)?;
                    self.emit_local_set(d);
                }
                Carrier::Void => {}
            }
        }
        Ok(())
    }

    /// The frame base local (a frame must exist).
    fn frame_base(&self) -> Result<u32, WasmLowerError> {
        self.frame.map(|f| f.base_local).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "`{}` needs a frame slot but has no frame",
                self.func.name
            ))
        })
    }

    /// The signature a direct call to `callee` (of type `ft` under `cc`)
    /// uses: the internal form when the object routes the call through the
    /// callee's internal entry, the C form otherwise. The function's own
    /// signature (`Lowering::build`) is chosen by the same rule.
    pub(super) fn direct_call_sig(
        &self,
        callee: FuncId,
        ft: &FuncTy,
        cc: CallingConv,
    ) -> Result<WasmSig, WasmLowerError> {
        if !self.internal_abi.contains_key(&callee) {
            return abi::lower_sig(self.module, ft, cc);
        }
        abi::lower_internal_sig(self.module, ft, cc)?.ok_or_else(|| {
            WasmLowerError::UnsupportedAbi(format!(
                "[TCG-WASM-INTERNAL-ABI] {callee:?} is routed through an internal entry, but \
                 its signature has no internal form"
            ))
        })
    }

    /// A direct `Call`.
    pub(super) fn lower_call(
        &mut self,
        site: (usize, usize),
        results: &[ValueId],
        callee: FuncId,
        args: &[ValueId],
    ) -> Result<(), WasmLowerError> {
        let widx = *self
            .internal_abi
            .get(&callee)
            .or_else(|| self.call_targets.get(&callee))
            .ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!("Call to unknown {callee:?}"))
            })?;
        let callee_fn = self.module.function_by_id(callee).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!("Call to unknown {callee:?}"))
        })?;
        let ft = self.module.func_type(callee_fn.ty).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!("unknown signature {:?}", callee_fn.ty))
        })?;
        let ret_tys = ft.returns.clone();
        let sig = self.direct_call_sig(callee, ft, callee_fn.calling_conv)?;
        let foreign = self.foreign.contains(&callee);
        self.push_call_args(site, &sig, args, results, foreign)?;
        self.emit_call(widx);
        self.note_sig_features(&sig);
        self.bind_call_results(site, &sig, &ret_tys, results)
    }

    /// A `CallIndirect` through a function pointer (a table index).
    pub(super) fn lower_call_indirect(
        &mut self,
        site: (usize, usize),
        results: &[ValueId],
        callee: ValueId,
        sig_id: FuncTyId,
        args: &[ValueId],
        cc: CallingConv,
    ) -> Result<(), WasmLowerError> {
        let ft = self.module.func_type(sig_id).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!("call_indirect with unknown {sig_id:?}"))
        })?;
        let ret_tys = ft.returns.clone();
        let sig = abi::lower_sig(self.module, ft, cc)?;
        let type_idx = *self.sig_types.get(&(sig_id, cc)).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!("call_indirect with unknown {sig_id:?}"))
        })?;
        // The target is unknown, so treat it as foreign: it may be an import.
        self.push_call_args(site, &sig, args, results, true)?;
        let c = slot(&self.locals, callee)?.0;
        emit_local_get(&mut self.code, c);
        self.emit_call_indirect(type_idx);
        self.note_sig_features(&sig);
        self.bind_call_results(site, &sig, &ret_tys, results)
    }

    pub(super) fn note_sig_features(&mut self, sig: &WasmSig) {
        if sig.multivalue() {
            self.features.insert("multivalue");
        }
    }

    /// `Return { values }`: write an `sret` result, restore the caller's stack
    /// pointer, push the scalar results.
    pub(super) fn emit_return(&mut self, values: &[ValueId]) -> Result<(), WasmLowerError> {
        let rets = self.sig.rets.clone();
        if values.len() != rets.len() {
            return Err(WasmLowerError::ArityMismatch(format!(
                "`{}` returns {} values from a {}-result signature",
                self.func.name,
                values.len(),
                rets.len()
            )));
        }
        for (lane, &v) in rets.iter().zip(values) {
            let sret = || {
                self.sret_local.ok_or_else(|| {
                    WasmLowerError::UnsupportedInst("sret return without an sret param".into())
                })
            };
            match lane {
                RetLane::Sret { size } if self.is_pair(v) => {
                    let dst = sret()?;
                    if *size != 16 {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "a 128-bit pair returned as a {size}-byte result from `{}`",
                            self.func.name
                        )));
                    }
                    self.store_pair_at(dst, 0, v)?;
                }
                RetLane::Sret { size } => {
                    let dst = sret()?;
                    let src = self.addr_local(v)?;
                    self.emit_copy(dst, 0, src, 0, *size);
                }
                RetLane::Field { offset, ty } => {
                    let dst = sret()?;
                    match self.carrier(v)? {
                        Carrier::Mem { size, .. } => {
                            let src = self.addr_local(v)?;
                            self.emit_copy(dst, *offset, src, 0, size);
                        }
                        Carrier::Pair => self.store_pair_at(dst, *offset, v)?,
                        Carrier::Scalar(_) => {
                            let l = slot(&self.locals, v)?.0;
                            emit_local_get(&mut self.code, dst);
                            emit_local_get(&mut self.code, l);
                            self.emit_store(ty, *offset)?;
                        }
                        Carrier::Void => {}
                    }
                }
                _ => {}
            }
        }
        // Epilogue: restore the caller's stack pointer before leaving.
        if let Some(frame) = self.frame {
            emit_local_get(&mut self.code, frame.saved_sp_local);
            self.emit_global_op(op::GLOBAL_SET, frame.sp_global);
        }
        let ret_tys: Vec<Ty> = self
            .module
            .func_type(self.func.ty)
            .map(|ft| ft.returns.clone())
            .unwrap_or_default();
        for (v, t) in values.iter().zip(&ret_tys) {
            if matches!(
                self.carriers.get(v),
                Some(super::super::layout::Carrier::Scalar(_))
            ) {
                self.check_operand(*v, t)?;
            }
        }
        for (lane, &v) in rets.iter().zip(values) {
            match lane {
                RetLane::Scalar(_) => {
                    let l = slot(&self.locals, v)?.0;
                    emit_local_get(&mut self.code, l);
                }
                RetLane::Singleton { offset, ty, .. } => {
                    let a = self.addr_local(v)?;
                    emit_local_get(&mut self.code, a);
                    self.emit_load(ty, *offset)?;
                }
                RetLane::Wide if self.is_pair(v) => {
                    let (lo, hi) = self.pair_of(v)?;
                    emit_local_get(&mut self.code, lo);
                    emit_local_get(&mut self.code, hi);
                }
                RetLane::Wide => {
                    let a = self.addr_local(v)?;
                    for offset in [0, 8] {
                        emit_local_get(&mut self.code, a);
                        self.emit_load(&Ty::U64, offset)?;
                    }
                }
                RetLane::Void | RetLane::Sret { .. } | RetLane::Field { .. } => {}
            }
        }
        self.code.push(op::RETURN);
        let results: Vec<ValType> = self.sig.wasm.results.clone();
        if self.result_types.is_none() {
            self.result_types = Some(results);
        }
        Ok(())
    }
}
