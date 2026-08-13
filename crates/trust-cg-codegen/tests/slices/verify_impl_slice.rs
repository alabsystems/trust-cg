// verify_impl_slice — self-contained slice of the clean-kernel micro-checker's
// certificate TYPE-CHECKER `verify_impl`, composing the verified `def_eq_impl` +
// `whnf_impl` pillars and SELF-RECURSING over (MicroCert, MicroExpr) with a
// threaded `context` Vec. Reconstructed VERBATIM from the native oracle
// (`VeChecker::ve_verify_impl` et al.) in tests/e2e_frontend_roundtrip.rs, with the
// `ve_` prefixes dropped back to the canonical clean-kernel names and `MeArc`
// re-bound to real `std::sync::Arc`.
//
// Crate name is load-bearing: it appears in the mangled symbols of the trait/extern
// leaves the JIT binds, so it MUST stay `verify_impl_slice`.
//
// EMIT: `trust_ir_mir verify_impl_slice.rs --crate-type=lib -C panic=abort
//   -C overflow-checks=off -C debug-assertions=off --mir-emit-closure verify_impl <out>`.
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

// The certificate AST (parallel to MicroExpr; same rustc layout).
#[derive(Clone)]
pub enum MicroCert {
    Sort {
        level: MicroLevel,
    },
    BVar {
        idx: u32,
        ty: Box<MicroExpr>,
    },
    Opaque {
        ty: Box<MicroExpr>,
    },
    Const {
        name: Arc<str>,
        ty: Box<MicroExpr>,
    },
    App {
        fn_cert: Box<MicroCert>,
        arg_cert: Box<MicroCert>,
        result_ty: Box<MicroExpr>,
    },
    Lam {
        arg_ty_cert: Box<MicroCert>,
        body_cert: Box<MicroCert>,
        result_ty: Box<MicroExpr>,
    },
    Pi {
        arg_ty_cert: Box<MicroCert>,
        arg_level: MicroLevel,
        body_ty_cert: Box<MicroCert>,
        body_level: MicroLevel,
    },
    Let {
        ty_cert: Box<MicroCert>,
        val_cert: Box<MicroCert>,
        body_cert: Box<MicroCert>,
        result_ty: Box<MicroExpr>,
    },
    Lit {
        lit: MicroLiteral,
        ty: Box<MicroExpr>,
    },
    Proj {
        idx: u32,
        expr_cert: Box<MicroCert>,
        field_ty: Box<MicroExpr>,
    },
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

impl MicroLevel {
    fn succ(l: MicroLevel) -> MicroLevel {
        MicroLevel::Succ(Arc::new(l))
    }
    fn imax(a: MicroLevel, b: MicroLevel) -> MicroLevel {
        MicroLevel::IMax(Arc::new(a), Arc::new(b))
    }
    fn level_eq(&self, other: &MicroLevel) -> bool {
        self == other
    }
}

// The not-in-env Unsupported leaf (no format!/String) — the Const env-coverage gate.
fn unsupported_const(name: &Arc<str>) -> MicroError {
    MicroError::Unsupported(name.clone())
}

fn is_native_op(_name: &Arc<str>) -> bool {
    false
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

#[repr(C)]
pub struct MicroChecker<'e> {
    context: Vec<MicroExpr>,
    env: &'e [(Arc<str>, Option<MicroExpr>)],
    universe_blind: bool,
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
    fn whnf(&self, e: &MicroExpr) -> MicroExpr {
        match e {
            MicroExpr::Const(name) => {
                if is_native_op(name) {
                    return e.clone();
                }
                if let Some(body) = self.env_get(name) {
                    return self.whnf(body);
                }
                e.clone()
            }
            MicroExpr::App(f, a) => {
                let f_whnf = self.whnf(f);
                match &f_whnf {
                    MicroExpr::Lam(_, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf(&reduced)
                    }
                    _ => {
                        let mut head = f_whnf;
                        let mut args: Vec<MicroExpr> = vec![a.as_ref().clone()];
                        while let MicroExpr::App(hf, ha) = &head {
                            args.push(ha.as_ref().clone());
                            head = self.whnf(hf);
                        }
                        args.reverse();
                        if let MicroExpr::Const(name) = &head {
                            if !is_native_op(name) {
                                if let Some(body) = self.env_get(name) {
                                    let mut applied = body.clone();
                                    for arg in &args {
                                        applied = MicroExpr::App(
                                            Arc::new(applied),
                                            Arc::new(arg.clone()),
                                        );
                                    }
                                    return self.whnf(&applied);
                                }
                            }
                        }
                        let mut rebuilt = head;
                        for arg in args {
                            rebuilt = MicroExpr::App(Arc::new(rebuilt), Arc::new(arg));
                        }
                        rebuilt
                    }
                }
            }
            MicroExpr::Let(_, val, body) => {
                let reduced = body.instantiate(val);
                self.whnf(&reduced)
            }
            _ => e.clone(),
        }
    }
    fn structural_eq(&self, a: &MicroExpr, b: &MicroExpr) -> bool {
        match (a, b) {
            (MicroExpr::BVar(i), MicroExpr::BVar(j)) => i == j,
            (MicroExpr::Sort(l1), MicroExpr::Sort(l2)) => self.universe_blind || l1 == l2,
            (MicroExpr::Const(n1), MicroExpr::Const(n2)) => n1 == n2,
            (MicroExpr::App(f1, a1), MicroExpr::App(f2, a2)) => {
                self.structural_eq(f1, f2) && self.structural_eq(a1, a2)
            }
            (MicroExpr::Lam(ty1, b1), MicroExpr::Lam(ty2, b2))
            | (MicroExpr::Pi(ty1, b1), MicroExpr::Pi(ty2, b2)) => {
                self.structural_eq(ty1, ty2) && self.structural_eq(b1, b2)
            }
            (MicroExpr::Let(ty1, v1, b1), MicroExpr::Let(ty2, v2, b2)) => {
                self.structural_eq(ty1, ty2)
                    && self.structural_eq(v1, v2)
                    && self.structural_eq(b1, b2)
            }
            (MicroExpr::Opaque(t1), MicroExpr::Opaque(t2)) => self.structural_eq(t1, t2),
            (MicroExpr::Lit(l1), MicroExpr::Lit(l2)) => l1 == l2,
            (MicroExpr::Proj(i1, e1), MicroExpr::Proj(i2, e2)) => {
                i1 == i2 && self.structural_eq(e1, e2)
            }
            _ => false,
        }
    }
    fn def_eq_impl(&self, a: &MicroExpr, b: &MicroExpr) -> Result<bool, MicroError> {
        let a_whnf = self.whnf(a);
        let b_whnf = self.whnf(b);
        if self.structural_eq(&a_whnf, &b_whnf) {
            return Ok(true);
        }
        if let (MicroExpr::App(f1, a1), MicroExpr::App(f2, a2)) = (&a_whnf, &b_whnf) {
            return Ok(self.def_eq_impl(f1, f2)? && self.def_eq_impl(a1, a2)?);
        }
        if let (MicroExpr::Pi(t1, b1), MicroExpr::Pi(t2, b2))
        | (MicroExpr::Lam(t1, b1), MicroExpr::Lam(t2, b2)) = (&a_whnf, &b_whnf)
        {
            return Ok(self.def_eq_impl(t1, t2)? && self.def_eq_impl(b1, b2)?);
        }
        Ok(false)
    }
    fn whnf_impl(&self, e: &MicroExpr) -> Result<MicroExpr, MicroError> {
        Ok(self.whnf(e))
    }
    fn verify_impl(
        &mut self,
        cert: &MicroCert,
        expr: &MicroExpr,
    ) -> Result<MicroExpr, MicroError> {
        match (cert, expr) {
            (MicroCert::Sort { level }, MicroExpr::Sort(l)) => {
                if !level.level_eq(l) {
                    return Err(MicroError::LevelMismatch {
                        expected: level.clone(),
                        actual: l.clone(),
                    });
                }
                Ok(MicroExpr::Sort(MicroLevel::succ(level.clone())))
            }
            (MicroCert::Const { name, ty }, MicroExpr::Const(n)) => {
                if name != n {
                    return Err(MicroError::StructureMismatch);
                }
                if self.env_get(name).is_none() {
                    return Err(unsupported_const(name));
                }
                Ok(ty.as_ref().clone())
            }
            (MicroCert::BVar { idx, ty }, MicroExpr::BVar(i)) => {
                if *idx != *i {
                    return Err(MicroError::InvalidBVar(*i));
                }
                let depth = self.context.len();
                if (*idx as usize) >= depth {
                    return Err(MicroError::InvalidBVar(*idx));
                }
                let ctx_pos = depth - 1 - *idx as usize;
                let ctx_ty = &self.context[ctx_pos];
                let lifted_ctx_ty = ctx_ty.lift(0, (depth - ctx_pos) as u32);
                if !self.def_eq_impl(ty.as_ref(), &lifted_ctx_ty)? {
                    return Err(MicroError::TypeMismatch {
                        expected: lifted_ctx_ty,
                        actual: ty.as_ref().clone(),
                    });
                }
                Ok(ty.as_ref().clone())
            }
            (MicroCert::Opaque { ty }, MicroExpr::Opaque(t)) => {
                if !self.def_eq_impl(ty.as_ref(), t.as_ref())? {
                    return Err(MicroError::TypeMismatch {
                        expected: ty.as_ref().clone(),
                        actual: t.as_ref().clone(),
                    });
                }
                Ok(ty.as_ref().clone())
            }
            (
                MicroCert::App {
                    fn_cert,
                    arg_cert,
                    result_ty,
                },
                MicroExpr::App(f, a),
            ) => {
                let fn_ty = self.verify_impl(fn_cert, f)?;
                let fn_ty_whnf = self.whnf_impl(&fn_ty)?;
                let (expected_arg_ty, body_ty) = match &fn_ty_whnf {
                    MicroExpr::Pi(arg_ty, body) => (arg_ty.as_ref(), body.as_ref()),
                    _ => return Err(MicroError::ExpectedPi(fn_ty_whnf)),
                };
                let arg_ty = self.verify_impl(arg_cert, a)?;
                if !self.def_eq_impl(&arg_ty, expected_arg_ty)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_arg_ty.clone(),
                        actual: arg_ty,
                    });
                }
                let expected_result = body_ty.instantiate(a);
                if !self.def_eq_impl(result_ty.as_ref(), &expected_result)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_result,
                        actual: result_ty.as_ref().clone(),
                    });
                }
                Ok(result_ty.as_ref().clone())
            }
            (
                MicroCert::Lam {
                    arg_ty_cert,
                    body_cert,
                    result_ty,
                },
                MicroExpr::Lam(arg_ty, body),
            ) => {
                let arg_sort = self.verify_impl(arg_ty_cert, arg_ty)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort)?;
                if !matches!(arg_sort_whnf, MicroExpr::Sort(_)) {
                    return Err(MicroError::ExpectedSort(arg_sort_whnf));
                }
                self.context.push(arg_ty.as_ref().clone());
                let body_ty = self.verify_impl(body_cert, body);
                self.context.pop();
                let body_ty = body_ty?;
                let expected_pi = MicroExpr::Pi(arg_ty.clone(), Arc::new(body_ty));
                if !self.def_eq_impl(result_ty.as_ref(), &expected_pi)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_pi,
                        actual: result_ty.as_ref().clone(),
                    });
                }
                Ok(result_ty.as_ref().clone())
            }
            (
                MicroCert::Pi {
                    arg_ty_cert,
                    arg_level,
                    body_ty_cert,
                    body_level,
                },
                MicroExpr::Pi(arg_ty, body_ty),
            ) => {
                let arg_sort = self.verify_impl(arg_ty_cert, arg_ty)?;
                let l1 = match self.whnf_impl(&arg_sort)? {
                    MicroExpr::Sort(l) => l,
                    other => return Err(MicroError::ExpectedSort(other)),
                };
                if !self.universe_blind && !l1.level_eq(arg_level) {
                    return Err(MicroError::LevelMismatch {
                        expected: arg_level.clone(),
                        actual: l1,
                    });
                }
                self.context.push(arg_ty.as_ref().clone());
                let body_sort = self.verify_impl(body_ty_cert, body_ty);
                self.context.pop();
                let body_sort = body_sort?;
                let l2 = match self.whnf_impl(&body_sort)? {
                    MicroExpr::Sort(l) => l,
                    other => return Err(MicroError::ExpectedSort(other)),
                };
                if !self.universe_blind && !l2.level_eq(body_level) {
                    return Err(MicroError::LevelMismatch {
                        expected: body_level.clone(),
                        actual: l2,
                    });
                }
                Ok(MicroExpr::Sort(MicroLevel::imax(
                    arg_level.clone(),
                    body_level.clone(),
                )))
            }
            (
                MicroCert::Let {
                    ty_cert,
                    val_cert,
                    body_cert,
                    result_ty,
                },
                MicroExpr::Let(ty, val, body),
            ) => {
                let ty_sort = self.verify_impl(ty_cert, ty)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort)?;
                if !matches!(ty_sort_whnf, MicroExpr::Sort(_)) {
                    return Err(MicroError::ExpectedSort(ty_sort_whnf));
                }
                let val_ty = self.verify_impl(val_cert, val)?;
                if !self.def_eq_impl(&val_ty, ty)? {
                    return Err(MicroError::TypeMismatch {
                        expected: ty.as_ref().clone(),
                        actual: val_ty,
                    });
                }
                self.context.push(ty.as_ref().clone());
                let body_ty = self.verify_impl(body_cert, body);
                self.context.pop();
                let body_ty = body_ty?;
                let expected_result = body_ty.instantiate(val);
                if !self.def_eq_impl(result_ty.as_ref(), &expected_result)? {
                    return Err(MicroError::TypeMismatch {
                        expected: expected_result,
                        actual: result_ty.as_ref().clone(),
                    });
                }
                Ok(result_ty.as_ref().clone())
            }
            (MicroCert::Lit { lit, ty }, MicroExpr::Lit(l)) => {
                if lit != l {
                    return Err(MicroError::StructureMismatch);
                }
                Ok(ty.as_ref().clone())
            }
            (
                MicroCert::Proj {
                    idx,
                    expr_cert,
                    field_ty,
                },
                MicroExpr::Proj(i, e),
            ) => {
                if *idx != *i {
                    return Err(MicroError::StructureMismatch);
                }
                let _expr_ty = self.verify_impl(expr_cert, e)?;
                Ok(field_ty.as_ref().clone())
            }
            _ => Err(MicroError::StructureMismatch),
        }
    }
}

#[no_mangle]
pub extern "C" fn __root_verify_impl(
    chk: &mut MicroChecker<'_>,
    cert: &MicroCert,
    expr: &MicroExpr,
) -> u64 {
    match chk.verify_impl(cert, expr) {
        Ok(_) => 1,
        Err(_) => 0,
    }
}
