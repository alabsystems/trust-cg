// reduce_recursor_slice — self-contained slice of the clean-kernel micro-checker's
// `whnf_impl` WITH its iota RECURSOR engine (`reduce_recursor` for Bool.rec / Nat.rec)
// wired in via a non-empty recursor gate. Reconstructed VERBATIM from the native
// oracle (`RrChecker::rr_whnf_impl` / `rr_reduce_recursor` et al.) in
// tests/e2e_frontend_roundtrip.rs, with the `rr_` prefixes dropped back to the
// canonical clean-kernel names and `MeArc` re-bound to real `std::sync::Arc`.
//
// Crate name is load-bearing (it appears in the mangled leaf symbols); MUST stay
// `reduce_recursor_slice`.
//
// EMIT: `trust_ir_mir reduce_recursor_slice.rs --crate-type=lib -C panic=abort
//   -C overflow-checks=off -C debug-assertions=off --mir-emit-closure whnf_impl <out>`.
#![allow(dead_code)]
#![allow(clippy::all)]

use std::sync::Arc;

#[derive(PartialEq, Eq, Clone)]
pub enum MicroLevel {
    Zero,
    Succ(Arc<MicroLevel>),
    Max(Arc<MicroLevel>, Arc<MicroLevel>),
    IMax(Arc<MicroLevel>, Arc<MicroLevel>),
}

#[derive(PartialEq, Eq, Clone)]
pub enum MicroLiteral {
    Nat(u64),
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
fn is_recursor(name: &str) -> bool {
    name_is_bool_rec(name) || name_is_nat_rec(name)
}
fn is_nat_binop_or_succ(_n: &str) -> bool {
    false
}
fn is_bool_binop(_n: &str) -> bool {
    false
}
fn is_native_op(_n: &Arc<str>) -> bool {
    false
}
fn reduce_nat_app(_op: &str, _a: &[MicroExpr]) -> Option<MicroExpr> {
    None
}
fn reduce_bool_app(_op: &str, _a: &[MicroExpr]) -> Option<MicroExpr> {
    None
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

#[no_mangle]
pub extern "C" fn __root_whnf_impl(chk: &MicroChecker<'_>, e: &MicroExpr) -> u64 {
    match chk.whnf_impl(e) {
        Ok(_) => 1,
        Err(_) => 0,
    }
}
