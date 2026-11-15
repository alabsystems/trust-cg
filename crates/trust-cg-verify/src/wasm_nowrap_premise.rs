// trust-cg-verify/wasm_nowrap_premise.rs - the trust-ir no-wrap premise of a lowered GEP add
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The cross-layer premise under which `wasm_local_tv` accepts a memarg
//! offset folded out of a GEP's address addition.
//!
//! **The semantics it rests on.** trust-ir's GEP is flat: `gep T, base, i`
//! computes `base + i * size_of(T)`, a negative signed index is undefined
//! behaviour, the byte offset is computed without wrapping (an overflowing
//! product or sum is undefined behaviour), and on a 32-bit target a result
//! address past `2^32 - 1` is undefined behaviour (trust-ir WS2.16: the
//! reference interpreter's `eval_gep` checks the result against the target's
//! highest address, for every GEP, `inbounds` or not; `inbounds` itself is a
//! hint with no run-time effect there). So in every execution in which a
//! single-index GEP is defined, `addr(base) + i * size` is at most
//! `2^32 - 1` as an exact integer. The wasm32 lane lowers that GEP as
//! `local.get B; local.get I; [i32.const size; i32.mul]; i32.add; local.set
//! V` (the multiply omitted for a one-byte element at O1 and above): when
//! the GEP is defined, `I` holds `i` below `2^32` and the product does not
//! wrap, so the `i32.add` does not wrap either. Folding a constant addend of
//! that addition into a load's or store's memarg offset is then equivalent
//! (`wasm_memarg_offset_proofs::memarg_gep_fold_obligation`).
//!
//! An integer address chain (`inttoptr (ptrtoint p + k)`) carries no such
//! premise: trust-ir's `add` on `i32`/`usize` wraps at the target width, and
//! the wrapped integer is a legal address, so nothing here admits one.
//!
//! **What the checker re-derives.** [`check_nowrap_premises`] is given the
//! trust-ir function and module, the lane's value-to-local map, the lane's
//! CLAIMS (a GEP value and the byte offset of the `i32.add` it says lowers
//! it) and the lowering's own body. It admits a claim only when, with its
//! own code:
//!
//! - the module's target has 32-bit pointers and the reference interpreter
//!   executes its layout (the premise is WS2.16's, which holds only there);
//! - the claimed value is the only result of a `GEP` with exactly one index,
//!   whose element size the interpreter's layout (`fsym_layout`) gives as a
//!   nonzero `u32`;
//! - the GEP, its base and its index each have a local of their own (no
//!   other value is mapped to it), all three `i32` locals and distinct;
//! - the body's instruction at the claimed offset is `i32.add`, directly
//!   preceded by `local.get B; local.get I` (an element size of 1) or
//!   `local.get B; local.get I; i32.const size; i32.mul`, and directly
//!   followed by `local.set V`, the ONLY write of `V` in the body.
//!
//! The result is a [`NoWrapPremise`] per admitted claim, a type only this
//! module constructs. `wasm_local_tv::validate_with_premises` then checks the
//! body side again on the body it validates: it activates a premise only for
//! a local written exactly once there, and at that write marks the value
//! written as a no-wrap sum only when it IS `B + I` (or `B + I * size`) of
//! the values `B` and `I` hold at that point.
//!
//! **What a premise is bound to.** A premise names the function (its
//! trust-ir name) and the body (a digest of the code the claims index) it
//! was derived from; `validate_with_premises` activates it only for that
//! function name and a pre body with that digest. The digest is a 64-bit
//! FNV-1a guard against a premise reaching another function or body through
//! the caller's plumbing, not a cryptographic commitment. A premise moves to
//! a control-cleaned body only through
//! `wasm_local_tv::validate_control_with_premises`, after the lockstep
//! simulation accepted the cleanup (that function says why the premise
//! carries over).
//!
//! **What it does not establish.** The binding of a trust-ir value to its
//! local is the lane's map (checked injective here: a value listed twice or
//! a local listed for two values refuses, never derived); that the code
//! writing `B` computes the base's address is the correctness of the
//! lowering, which the emission validation has never claimed. The premise
//! is therefore conditional: the folded body equals the lowering's body on
//! every execution in which the claimed GEPs are defined, given that the
//! lowering computes the trust-ir function. A wasm32 module is reference
//! execution only (trust-ir subset condition 5 refuses it), so the premise
//! is the reference interpreter's semantics, not Lean-backed.
//!
//! **The address model it assumes.** WS2.16 bounds the GEP's result in the
//! reference interpreter's own address space, whose allocations a bump
//! allocator places from address 1024; the wasm execution's base is a
//! shadow-stack or linear-memory address the interpreter never computes.
//! The premise transfers only by reading trust-ir allocation placement as
//! unspecified, with the wasm execution's addresses one admissible
//! placement and the interpreter's 1024-based bump allocator another, so a
//! wasm address past `2^32 - 1` makes the GEP undefined under that
//! placement. trust-ir at the pinned revision does not state placement as
//! unspecified normatively (its Lean differential treats addresses as
//! engine-private and compares pointers by nullness only); that reading is
//! an open premise of this module, not interpreter-backed.

use std::collections::HashMap;

use trust_ir::{Function, Inst, Module, ValueId};

use crate::fsym_layout::FsymLayout;
use crate::wasm_cfg_proofs::{DecodedInst, Imm, ValKind, decode_body};
use crate::wasm_local_tv::TvBody;

/// The lane's claim that the `i32.add` at byte `add_offset` of the
/// lowering's body is the address addition of the GEP defining `value`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NoWrapClaim {
    /// The GEP's result.
    pub value: ValueId,
    /// Byte offset of the `i32.add` in the lowering's body.
    pub add_offset: u32,
}

/// An admitted premise: the value the body writes to local `result` (once)
/// is `base + index * scale` of the values those locals hold, and that
/// addition does not wrap in any execution in which the trust-ir GEP is
/// defined. Constructed only by [`check_nowrap_premises`], and bound to the
/// function and body it was derived from (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NoWrapPremise {
    result: u32,
    base: u32,
    index: u32,
    scale: u32,
    multiplied: bool,
    /// [`digest`] of the trust-ir function's name.
    function: u64,
    /// [`digest`] of the code of the body the premise holds for.
    body: u64,
}

/// 64-bit FNV-1a of `bytes` (module docs: a plumbing guard, not a
/// commitment).
pub(crate) fn digest(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &b| {
        (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

impl NoWrapPremise {
    /// Whether this premise was derived for the function named `function`
    /// and holds for the body whose code is `code`.
    pub(crate) fn binds(&self, function: &str, code: &[u8]) -> bool {
        self.function == digest(function.as_bytes()) && self.body == digest(code)
    }

    /// This premise moved from the body whose code digests to `from` to the
    /// body whose code digests to `to`, when it holds for `from`. Only an
    /// accepted control cleanup moves a premise
    /// (`wasm_local_tv::validate_control_with_premises`).
    pub(crate) fn carried(self, from: u64, to: u64) -> Option<NoWrapPremise> {
        (self.body == from).then_some(NoWrapPremise { body: to, ..self })
    }

    /// A premise on `function`'s body `code`, for the validator's own unit
    /// tests of the body-side re-check (never constructed outside tests).
    #[cfg(test)]
    pub(crate) fn for_test(
        (result, base, index, scale, multiplied): (u32, u32, u32, u32, bool),
        function: &str,
        code: &[u8],
    ) -> NoWrapPremise {
        NoWrapPremise {
            result,
            base,
            index,
            scale,
            multiplied,
            function: digest(function.as_bytes()),
            body: digest(code),
        }
    }

    /// The GEP result's local.
    pub fn result(&self) -> u32 {
        self.result
    }

    /// The base pointer's local.
    pub fn base(&self) -> u32 {
        self.base
    }

    /// The index's local.
    pub fn index(&self) -> u32 {
        self.index
    }

    /// The element size the index is scaled by.
    pub fn scale(&self) -> u32 {
        self.scale
    }

    /// Whether the lowering multiplies the index (`false` only for an
    /// element size of 1 added unscaled).
    pub fn multiplied(&self) -> bool {
        self.multiplied
    }
}

/// Why a claim was not admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum NoWrapRefusal {
    /// The target is not a 32-bit reference-execution target.
    Target,
    /// The claimed value is not the only result of a `GEP`.
    NotGep,
    /// The GEP has other than one index.
    IndexCount,
    /// The element has no interpreter layout, a zero size, or one past `u32`.
    ElementSize,
    /// The GEP, its base or its index has no local, or shares it; or the
    /// lane's map lists a value twice.
    Local,
    /// The body does not decode, or nothing starts at the claimed offset.
    Offset,
    /// The instructions around the claimed offset are not the GEP's lowering.
    Shape,
    /// The GEP's local is written more than once.
    Writes,
}

impl NoWrapRefusal {
    /// Stable short name, for evidence counts.
    pub fn as_str(self) -> &'static str {
        match self {
            NoWrapRefusal::Target => "target",
            NoWrapRefusal::NotGep => "not_gep",
            NoWrapRefusal::IndexCount => "index_count",
            NoWrapRefusal::ElementSize => "element_size",
            NoWrapRefusal::Local => "local",
            NoWrapRefusal::Offset => "offset",
            NoWrapRefusal::Shape => "shape",
            NoWrapRefusal::Writes => "writes",
        }
    }
}

/// What [`check_nowrap_premises`] decided, claim by claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NoWrapCheck {
    /// The admitted premises, in claim order.
    pub premises: Vec<NoWrapPremise>,
    /// The refused claims, with the reason.
    pub refused: Vec<(NoWrapClaim, NoWrapRefusal)>,
}

/// Re-derive the no-wrap premise of every claim (module docs). `slots` is the
/// lane's value-to-local map (wasm parameters included in the local index
/// space; a value listed twice refuses every claim, [`NoWrapRefusal::Local`]);
/// `params` the function's wasm parameter types; `body` the lowering's own
/// body, which the claims' offsets index. Every admitted premise is bound to
/// `func`'s name and `body`'s code.
pub fn check_nowrap_premises(
    module: &Module,
    func: &Function,
    slots: &[(ValueId, u32)],
    params: &[ValKind],
    body: &TvBody<'_>,
    claims: &[NoWrapClaim],
) -> NoWrapCheck {
    let mut out = NoWrapCheck::default();
    let refuse_all = |out: &mut NoWrapCheck, why: NoWrapRefusal| {
        out.refused.extend(claims.iter().map(|c| (*c, why)));
    };
    if claims.is_empty() {
        return out;
    }
    let layout = FsymLayout::new(module);
    if layout.pointer_bits() != 32 || layout.reference_execution().is_err() {
        refuse_all(&mut out, NoWrapRefusal::Target);
        return out;
    }
    let Ok(insts) = decode_body(body.code, 0) else {
        refuse_all(&mut out, NoWrapRefusal::Offset);
        return out;
    };
    let mut ctx = Context {
        layout,
        params,
        body,
        insts: &insts,
        local_of: HashMap::new(),
        sharing: HashMap::new(),
        writes: HashMap::new(),
        geps: HashMap::new(),
        defined: HashMap::new(),
    };
    // The map must be a function from values to locals: a value listed
    // twice would hide one of its locals from the sharing count.
    for &(v, l) in slots {
        if ctx.local_of.insert(v, l).is_some() {
            refuse_all(&mut out, NoWrapRefusal::Local);
            return out;
        }
        *ctx.sharing.entry(l).or_default() += 1;
    }
    for x in &insts {
        if let (0x21 | 0x22, Imm::Index(l)) = (x.opcode, &x.imm) {
            *ctx.writes.entry(*l).or_default() += 1;
        }
    }
    for b in &func.blocks {
        for (v, _) in &b.params {
            *ctx.defined.entry(*v).or_default() += 1;
        }
        for node in &b.body {
            for r in &node.results {
                *ctx.defined.entry(*r).or_default() += 1;
            }
            if let [r] = node.results.as_slice()
                && matches!(node.inst, Inst::GEP { .. })
            {
                ctx.geps.insert(*r, &node.inst);
            }
        }
    }
    let (function, code) = (digest(func.name.as_bytes()), digest(body.code));
    for claim in claims {
        match ctx.admit(claim) {
            Ok(p) => out.premises.push(NoWrapPremise {
                function,
                body: code,
                ..p
            }),
            Err(why) => out.refused.push((*claim, why)),
        }
    }
    out
}

/// What [`check_nowrap_premises`] indexes once per function.
struct Context<'a> {
    layout: FsymLayout<'a>,
    params: &'a [ValKind],
    body: &'a TvBody<'a>,
    insts: &'a [DecodedInst],
    /// The lane's local of every value.
    local_of: HashMap<ValueId, u32>,
    /// How many values the lane maps to each local.
    sharing: HashMap<u32, usize>,
    /// Writes (`local.set`, `local.tee`) of each local in the body.
    writes: HashMap<u32, usize>,
    /// The `GEP` defining each value as its only result.
    geps: HashMap<ValueId, &'a Inst>,
    /// Definitions of each value (block parameters and results).
    defined: HashMap<ValueId, usize>,
}

impl Context<'_> {
    /// The local of `v`, when no other value is mapped to it.
    fn own(&self, v: ValueId) -> Option<u32> {
        let l = *self.local_of.get(&v)?;
        (self.sharing.get(&l) == Some(&1)).then_some(l)
    }

    /// Whether local `l` (parameters first) is an `i32` local.
    fn is_i32(&self, l: u32) -> bool {
        let l = l as usize;
        let ty = if l < self.params.len() {
            Some(self.params[l])
        } else {
            self.body.locals.get(l - self.params.len()).copied()
        };
        ty == Some(ValKind::I32)
    }

    /// One claim (module docs).
    fn admit(&self, claim: &NoWrapClaim) -> Result<NoWrapPremise, NoWrapRefusal> {
        let gep = self
            .geps
            .get(&claim.value)
            .filter(|_| self.defined.get(&claim.value) == Some(&1))
            .ok_or(NoWrapRefusal::NotGep)?;
        let Inst::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } = gep
        else {
            return Err(NoWrapRefusal::NotGep);
        };
        let [index] = indices.as_slice() else {
            return Err(NoWrapRefusal::IndexCount);
        };
        let scale = self
            .layout
            .size(pointee_ty)
            .ok()
            .filter(|&s| s != 0)
            .and_then(|s| u32::try_from(s).ok())
            .ok_or(NoWrapRefusal::ElementSize)?;
        let (Some(lv), Some(lb), Some(li)) =
            (self.own(claim.value), self.own(*base), self.own(*index))
        else {
            return Err(NoWrapRefusal::Local);
        };
        if lv == lb
            || lv == li
            || lb == li
            || !self.is_i32(lv)
            || !self.is_i32(lb)
            || !self.is_i32(li)
        {
            return Err(NoWrapRefusal::Local);
        }
        let at = self
            .insts
            .iter()
            .position(|x| x.offset == claim.add_offset as usize)
            .ok_or(NoWrapRefusal::Offset)?;
        let op = |k: usize| self.insts.get(k).map(|x| (x.opcode, &x.imm));
        let is_get = |k: usize, l: u32| op(k) == Some((0x20, &Imm::Index(l)));
        if op(at).map(|o| o.0) != Some(0x6a) || op(at + 1) != Some((0x21, &Imm::Index(lv))) {
            return Err(NoWrapRefusal::Shape);
        }
        let unscaled = at >= 2 && is_get(at - 2, lb) && is_get(at - 1, li);
        let scaled = at >= 4
            && is_get(at - 4, lb)
            && is_get(at - 3, li)
            && op(at - 2) == Some((0x41, &Imm::Int(i64::from(scale as i32))))
            && op(at - 1).map(|o| o.0) == Some(0x6c);
        let multiplied = match (unscaled, scaled) {
            (true, _) if scale == 1 => false,
            (_, true) => true,
            _ => return Err(NoWrapRefusal::Shape),
        };
        if self.writes.get(&lv) != Some(&1) {
            return Err(NoWrapRefusal::Writes);
        }
        Ok(NoWrapPremise {
            result: lv,
            base: lb,
            index: li,
            scale,
            multiplied,
            function: 0,
            body: 0,
        })
    }
}
