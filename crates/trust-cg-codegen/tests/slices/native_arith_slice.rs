// native_arith_slice — self-contained slice of the clean-kernel micro-checker's
// `whnf_impl` WITH its NATIVE-ARITHMETIC iota (`reduce_nat_app` / `reduce_bool_app`
// over the closed Nat/Bool ops), reconstructed VERBATIM from the native oracle
// (`NaChecker::na_whnf_impl` et al.) in tests/e2e_frontend_roundtrip.rs, with the
// `na_` prefixes dropped back to the canonical names and `MeArc` -> real
// `std::sync::Arc`. The BigUint DIGIT ARITHMETIC is a SEPARATE trusted base: the
// `bu_*` ops are FOREIGN extern leaves (bound to faithful num_bigint shims by the
// test); the slice itself never links num_bigint.
//
// Crate name is load-bearing; MUST stay `native_arith_slice`.
//
// EMIT: `trust_ir_mir native_arith_slice.rs --crate-type=lib -C panic=abort
//   -C overflow-checks=off -C debug-assertions=off --mir-emit-closure whnf_impl <out>`.
#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(improper_ctypes)]

use std::sync::Arc;

#[derive(PartialEq, Eq, Clone)]
pub enum MicroLevel {
    Zero,
    Succ(Arc<MicroLevel>),
    Max(Arc<MicroLevel>, Arc<MicroLevel>),
    IMax(Arc<MicroLevel>, Arc<MicroLevel>),
}

/// An OWNED, opaque thin handle to a heap `num_bigint::BigUint`. The real BigUint
/// lives behind it (allocated/read exclusively by the faithful `bu_*` leaves).
/// Clone/PartialEq are POINTER ops (the leak model — bitwise-copied, never freed).
pub struct BuHandle(*const u8);
impl Clone for BuHandle {
    fn clone(&self) -> Self {
        BuHandle(self.0)
    }
}
impl PartialEq for BuHandle {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for BuHandle {}

#[derive(PartialEq, Eq, Clone)]
pub enum MicroLiteral {
    Nat(BuHandle),
    String(Arc<str>),
}

#[derive(PartialEq, Eq, Clone)]
pub enum MicroExpr {
    BVar(u32),
    Sort(MicroLevel),
    App(Arc<MicroExpr>, Arc<MicroExpr>),
    Lam(Arc<MicroExpr>, Arc<MicroExpr>),
    Pi(Arc<MicroExpr>, Arc<MicroExpr>),
    Let(Arc<MicroExpr>, Arc<MicroExpr>, Arc<MicroExpr>),
    Opaque(Arc<MicroExpr>),
    Lit(MicroLiteral),
    Proj(u32, Arc<MicroExpr>),
    Const(Arc<str>),
}

#[derive(Clone)]
pub enum MicroError {
    TypeMismatch {
        expected: MicroExpr,
        actual: MicroExpr,
    },
    InvalidBVar(u32),
    ExpectedSort(MicroExpr),
    ExpectedPi(MicroExpr),
    LevelMismatch {
        expected: MicroLevel,
        actual: MicroLevel,
    },
    StructureMismatch,
    Unsupported(Arc<str>),
}

// The faithful BigUint arithmetic — a SEPARATE trusted base, bound to num_bigint
// shims by the harness. Unmangled `bu_*` names.
extern "C" {
    fn bu_zero() -> BuHandle;
    fn bu_clone(h: &BuHandle) -> BuHandle;
    fn bu_succ(h: &BuHandle) -> BuHandle;
    fn bu_add(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_sub(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_mul(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_div(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_rem(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_land(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_lor(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_xor(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_pow(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_shl(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_shr(a: &BuHandle, b: &BuHandle) -> BuHandle;
    fn bu_ge(a: &BuHandle, b: &BuHandle) -> bool;
    fn bu_eq(a: &BuHandle, b: &BuHandle) -> bool;
    fn bu_le(a: &BuHandle, b: &BuHandle) -> bool;
    fn bu_is_zero(h: &BuHandle) -> bool;
    fn bu_is_null(h: &BuHandle) -> bool;
}

#[repr(C)]
pub struct MicroChecker<'e> {
    env: &'e [(Arc<str>, Option<MicroExpr>)],
}

impl<'e> MicroChecker<'e> {
    fn env_get(&self, name: &Arc<str>) -> Option<&MicroExpr> {
        let mut i: usize = 0;
        let n = self.env.len();
        while i < n {
            let entry = &self.env[i];
            if entry.0 == *name {
                return entry.1.as_ref();
            }
            i += 1;
        }
        None
    }
    fn burn(&self) -> Result<(), MicroError> {
        Ok(())
    }

    fn whnf_impl(&self, e: &MicroExpr) -> Result<MicroExpr, MicroError> {
        self.burn()?;
        match e {
            MicroExpr::Const(name) => {
                if is_native_op(name) {
                    return Ok(e.clone());
                }
                if let Some(body) = self.env_get(name) {
                    return self.whnf_impl(body);
                }
                Ok(e.clone())
            }
            MicroExpr::App(f, a) => {
                let f_whnf = self.whnf_impl(f)?;
                match &f_whnf {
                    MicroExpr::Lam(_, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        let mut head = f_whnf;
                        let mut args: Vec<MicroExpr> = vec![a.as_ref().clone()];
                        while let MicroExpr::App(hf, ha) = &head {
                            args.push(ha.as_ref().clone());
                            head = self.whnf_impl(hf)?;
                        }
                        args.reverse();
                        if let MicroExpr::Const(name) = &head {
                            if is_nat_binop_or_succ(name) {
                                let mut red_args = Vec::with_capacity(args.len());
                                for arg in &args {
                                    red_args.push(self.whnf_impl(arg)?);
                                }
                                if let Some(r) = reduce_nat_app(name, &red_args) {
                                    return self.whnf_impl(&r);
                                }
                                let mut rebuilt = head.clone();
                                for arg in red_args {
                                    rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                                }
                                return Ok(rebuilt);
                            }
                            if is_bool_binop(name) {
                                let mut red_args = Vec::with_capacity(args.len());
                                for arg in &args {
                                    red_args.push(self.whnf_impl(arg)?);
                                }
                                if let Some(r) = reduce_bool_app(name, &red_args) {
                                    return self.whnf_impl(&r);
                                }
                                let mut rebuilt = head.clone();
                                for arg in red_args {
                                    rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                                }
                                return Ok(rebuilt);
                            }
                            if is_recursor(name) {
                                if let Some(r) = self.reduce_recursor(name, &args)? {
                                    return self.whnf_impl(&r);
                                }
                                let mut rebuilt = head.clone();
                                for arg in args {
                                    rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                                }
                                return Ok(rebuilt);
                            }
                            if let Some(body) = self.env_get(name) {
                                let mut applied = body.clone();
                                for arg in &args {
                                    applied = MicroExpr::App(
                                        Arc::new(applied),
                                        Arc::new(arg.clone()),
                                    );
                                }
                                return self.whnf_impl(&applied);
                            }
                        }
                        let mut rebuilt = head;
                        for arg in args {
                            rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                        }
                        Ok(rebuilt)
                    }
                }
            }
            MicroExpr::Let(_, val, body) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            _ => Ok(e.clone()),
        }
    }

    fn reduce_recursor(
        &self,
        name: &str,
        args: &[MicroExpr],
    ) -> Result<Option<MicroExpr>, MicroError> {
        self.burn()?;
        let num_minors = if name_is_bool_rec(name) || name_is_nat_rec(name) {
            2
        } else {
            return Ok(None);
        };
        let major_idx = 1 + num_minors;
        if args.len() <= major_idx {
            return Ok(None);
        }
        let minors = &args[1..major_idx];
        let major = self.whnf_impl(&args[major_idx])?;
        let extra = &args[major_idx + 1..];
        let reduced = if name_is_bool_rec(name) {
            let Some(b) = as_bool(&major) else {
                return Ok(None);
            };
            let minor = if b { &minors[1] } else { &minors[0] };
            minor.clone()
        } else if name_is_nat_rec(name) {
            match nat_constructor(&major) {
                Some(NatCtor::Zero) => minors[0].clone(),
                Some(NatCtor::Succ(pred)) => {
                    let rec_on_pred = {
                        let mut spine = MicroExpr::Const(Arc::from(name));
                        spine = MicroExpr::App(Arc::new(spine), Arc::new(args[0].clone()));
                        for m in minors {
                            spine = MicroExpr::App(Arc::new(spine), Arc::new(m.clone()));
                        }
                        MicroExpr::App(Arc::new(spine), Arc::new(pred.clone()))
                    };
                    MicroExpr::App(
                        Arc::new(MicroExpr::App(
                            Arc::new(minors[1].clone()),
                            Arc::new(pred),
                        )),
                        Arc::new(rec_on_pred),
                    )
                }
                None => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        let mut out = reduced;
        for e in extra {
            out = MicroExpr::App(Arc::new(out), Arc::new(e.clone()));
        }
        Ok(Some(out))
    }
}

impl MicroExpr {
    fn lift(&self, cutoff: u32, amount: u32) -> MicroExpr {
        match self {
            MicroExpr::BVar(idx) => {
                if *idx >= cutoff {
                    MicroExpr::BVar(idx.saturating_add(amount))
                } else {
                    self.clone()
                }
            }
            MicroExpr::Sort(l) => MicroExpr::Sort(l.clone()),
            MicroExpr::App(f, a) => MicroExpr::App(
                Arc::new(f.lift(cutoff, amount)),
                Arc::new(a.lift(cutoff, amount)),
            ),
            MicroExpr::Lam(ty, body) => MicroExpr::Lam(
                Arc::new(ty.lift(cutoff, amount)),
                Arc::new(body.lift(cutoff.saturating_add(1), amount)),
            ),
            MicroExpr::Pi(ty, body) => MicroExpr::Pi(
                Arc::new(ty.lift(cutoff, amount)),
                Arc::new(body.lift(cutoff.saturating_add(1), amount)),
            ),
            MicroExpr::Let(ty, val, body) => MicroExpr::Let(
                Arc::new(ty.lift(cutoff, amount)),
                Arc::new(val.lift(cutoff, amount)),
                Arc::new(body.lift(cutoff.saturating_add(1), amount)),
            ),
            MicroExpr::Opaque(ty) => MicroExpr::Opaque(Arc::new(ty.lift(cutoff, amount))),
            MicroExpr::Lit(_) => self.clone(),
            MicroExpr::Proj(idx, e) => MicroExpr::Proj(*idx, Arc::new(e.lift(cutoff, amount))),
            MicroExpr::Const(_) => self.clone(),
        }
    }
    fn subst(&self, depth: u32, val: &MicroExpr) -> MicroExpr {
        match self {
            MicroExpr::BVar(idx) => {
                use std::cmp::Ordering;
                match idx.cmp(&depth) {
                    Ordering::Equal => val.lift(0, depth),
                    Ordering::Greater => MicroExpr::BVar(idx - 1),
                    Ordering::Less => self.clone(),
                }
            }
            MicroExpr::Sort(l) => MicroExpr::Sort(l.clone()),
            MicroExpr::App(f, a) => MicroExpr::App(
                Arc::new(f.subst(depth, val)),
                Arc::new(a.subst(depth, val)),
            ),
            MicroExpr::Lam(ty, body) => MicroExpr::Lam(
                Arc::new(ty.subst(depth, val)),
                Arc::new(body.subst(depth.saturating_add(1), val)),
            ),
            MicroExpr::Pi(ty, body) => MicroExpr::Pi(
                Arc::new(ty.subst(depth, val)),
                Arc::new(body.subst(depth.saturating_add(1), val)),
            ),
            MicroExpr::Let(ty, v, body) => MicroExpr::Let(
                Arc::new(ty.subst(depth, val)),
                Arc::new(v.subst(depth, val)),
                Arc::new(body.subst(depth.saturating_add(1), val)),
            ),
            MicroExpr::Opaque(ty) => MicroExpr::Opaque(Arc::new(ty.subst(depth, val))),
            MicroExpr::Lit(_) => self.clone(),
            MicroExpr::Proj(idx, e) => MicroExpr::Proj(*idx, Arc::new(e.subst(depth, val))),
            MicroExpr::Const(_) => self.clone(),
        }
    }
    fn instantiate(&self, arg: &MicroExpr) -> MicroExpr {
        self.subst(0, arg)
    }
}

enum NatCtor {
    Zero,
    Succ(MicroExpr),
}

fn as_bool(e: &MicroExpr) -> Option<bool> {
    match e {
        MicroExpr::Const(name) => {
            if name_is_bool_true(name) {
                Some(true)
            } else if name_is_bool_false(name) {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}
fn bool_const(b: bool) -> MicroExpr {
    if b {
        MicroExpr::Const(Arc::from("Bool.true"))
    } else {
        MicroExpr::Const(Arc::from("Bool.false"))
    }
}
fn as_nat(e: &MicroExpr) -> Option<BuHandle> {
    match e {
        MicroExpr::Lit(MicroLiteral::Nat(n)) => Some(unsafe { bu_clone(n) }),
        MicroExpr::Const(name) if name_is_nat_zero(name) => Some(unsafe { bu_zero() }),
        MicroExpr::App(f, a) => match &**f {
            MicroExpr::Const(name) if name_is_nat_succ(name) => {
                let inner = as_nat(a)?;
                Some(unsafe { bu_succ(&inner) })
            }
            _ => None,
        },
        _ => None,
    }
}
fn nat_lit(n: BuHandle) -> MicroExpr {
    MicroExpr::Lit(MicroLiteral::Nat(n))
}
fn nat_constructor(e: &MicroExpr) -> Option<NatCtor> {
    match e {
        MicroExpr::Const(name) if name_is_nat_zero(name) => Some(NatCtor::Zero),
        MicroExpr::App(f, a) => match &**f {
            MicroExpr::Const(name) if name_is_nat_succ(name) => {
                Some(NatCtor::Succ(a.as_ref().clone()))
            }
            _ => None,
        },
        _ => None,
    }
}
fn reduce_bool_app(op: &str, args: &[MicroExpr]) -> Option<MicroExpr> {
    if args.len() != 2 {
        return None;
    }
    let x = as_bool(&args[0])?;
    let y = as_bool(&args[1])?;
    if op_is_bool_beq(op) {
        Some(bool_const(x == y))
    } else {
        None
    }
}
fn reduce_nat_app(op: &str, args: &[MicroExpr]) -> Option<MicroExpr> {
    if op_is_nat_succ(op) {
        if args.len() != 1 {
            return None;
        }
        let n = as_nat(&args[0])?;
        return Some(nat_lit(unsafe { bu_succ(&n) }));
    }
    if args.len() != 2 {
        return None;
    }
    let x = as_nat(&args[0])?;
    let y = as_nat(&args[1])?;
    if op_is_nat_add(op) {
        Some(nat_lit(unsafe { bu_add(&x, &y) }))
    } else if op_is_nat_sub(op) {
        if unsafe { bu_ge(&x, &y) } {
            Some(nat_lit(unsafe { bu_sub(&x, &y) }))
        } else {
            Some(nat_lit(unsafe { bu_zero() }))
        }
    } else if op_is_nat_mul(op) {
        Some(nat_lit(unsafe { bu_mul(&x, &y) }))
    } else if op_is_nat_div(op) {
        if unsafe { bu_is_zero(&y) } {
            Some(nat_lit(unsafe { bu_zero() }))
        } else {
            Some(nat_lit(unsafe { bu_div(&x, &y) }))
        }
    } else if op_is_nat_mod(op) {
        if unsafe { bu_is_zero(&y) } {
            Some(nat_lit(x))
        } else {
            Some(nat_lit(unsafe { bu_rem(&x, &y) }))
        }
    } else if op_is_nat_pow(op) {
        let r = unsafe { bu_pow(&x, &y) };
        if unsafe { bu_is_null(&r) } {
            None
        } else {
            Some(nat_lit(r))
        }
    } else if op_is_nat_land(op) {
        Some(nat_lit(unsafe { bu_land(&x, &y) }))
    } else if op_is_nat_lor(op) {
        Some(nat_lit(unsafe { bu_lor(&x, &y) }))
    } else if op_is_nat_xor(op) {
        Some(nat_lit(unsafe { bu_xor(&x, &y) }))
    } else if op_is_nat_shl(op) {
        let r = unsafe { bu_shl(&x, &y) };
        if unsafe { bu_is_null(&r) } {
            None
        } else {
            Some(nat_lit(r))
        }
    } else if op_is_nat_shr(op) {
        Some(nat_lit(unsafe { bu_shr(&x, &y) }))
    } else if op_is_nat_beq(op) {
        Some(bool_const(unsafe { bu_eq(&x, &y) }))
    } else if op_is_nat_ble(op) {
        Some(bool_const(unsafe { bu_le(&x, &y) }))
    } else {
        None
    }
}

fn is_native_op(name: &str) -> bool {
    name_is_nat_binop_or_succ(name) || op_is_nat_succ(name) || name_is_bool_binop(name)
}
fn is_nat_binop_or_succ(name: &str) -> bool {
    name_is_nat_binop_or_succ(name)
}
fn is_bool_binop(name: &str) -> bool {
    name_is_bool_binop(name)
}
fn is_recursor(name: &str) -> bool {
    name_is_bool_rec(name) || name_is_nat_rec(name)
}

fn name_is_bool_rec(n: &str) -> bool {
    n == "Bool.rec"
}
fn name_is_nat_rec(n: &str) -> bool {
    n == "Nat.rec"
}
fn name_is_bool_true(n: &str) -> bool {
    n == "Bool.true"
}
fn name_is_bool_false(n: &str) -> bool {
    n == "Bool.false"
}
fn name_is_nat_zero(n: &str) -> bool {
    n == "Nat.zero"
}
fn name_is_nat_succ(n: &str) -> bool {
    n == "Nat.succ"
}
fn nat_binops(n: &str) -> bool {
    matches!(
        n,
        "Nat.add"
            | "Nat.sub"
            | "Nat.mul"
            | "Nat.div"
            | "Nat.mod"
            | "Nat.pow"
            | "Nat.land"
            | "Nat.lor"
            | "Nat.xor"
            | "Nat.shiftLeft"
            | "Nat.shiftRight"
            | "Nat.beq"
            | "Nat.ble"
    )
}
fn name_is_nat_binop_or_succ(n: &str) -> bool {
    nat_binops(n) || n == "Nat.succ"
}
fn name_is_bool_binop(n: &str) -> bool {
    n == "Bool.beq"
}
fn op_is_nat_succ(n: &str) -> bool {
    n == "Nat.succ"
}
fn op_is_nat_add(n: &str) -> bool {
    n == "Nat.add"
}
fn op_is_nat_sub(n: &str) -> bool {
    n == "Nat.sub"
}
fn op_is_nat_mul(n: &str) -> bool {
    n == "Nat.mul"
}
fn op_is_nat_div(n: &str) -> bool {
    n == "Nat.div"
}
fn op_is_nat_mod(n: &str) -> bool {
    n == "Nat.mod"
}
fn op_is_nat_pow(n: &str) -> bool {
    n == "Nat.pow"
}
fn op_is_nat_land(n: &str) -> bool {
    n == "Nat.land"
}
fn op_is_nat_lor(n: &str) -> bool {
    n == "Nat.lor"
}
fn op_is_nat_xor(n: &str) -> bool {
    n == "Nat.xor"
}
fn op_is_nat_shl(n: &str) -> bool {
    n == "Nat.shiftLeft"
}
fn op_is_nat_shr(n: &str) -> bool {
    n == "Nat.shiftRight"
}
fn op_is_nat_beq(n: &str) -> bool {
    n == "Nat.beq"
}
fn op_is_nat_ble(n: &str) -> bool {
    n == "Nat.ble"
}
fn op_is_bool_beq(n: &str) -> bool {
    n == "Bool.beq"
}

#[no_mangle]
pub extern "C" fn __root_whnf_impl(chk: &MicroChecker<'_>, e: &MicroExpr) -> u64 {
    match chk.whnf_impl(e) {
        Ok(_) => 1,
        Err(_) => 0,
    }
}
