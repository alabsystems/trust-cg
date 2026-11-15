// trust-cg-verify/wasm_body_fold_tests.rs - negative controls of the
// identical-body fold checker over hand-built relocatable objects.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The live lane's folds are checked in trust-cg-codegen's
// `tests/wasm_r16_sections.rs`; here every rule of `check_body_folds` has a
// control that breaks exactly it on a three-function object.
// `check_body_folds` is a provisional surface pending the owner's sign-off
// (docs/wasm32_perf_roadmap.md, "Pending owner sign-off"): these tests
// follow it if it changes, and are not a contract for its shape.

use super::*;

/// One defined function: its type index, body bytes (local declarations,
/// instructions and `end`), call relocations (offset in the body, symbol)
/// and other code relocations (type, offset in the body, index).
#[derive(Clone)]
struct F {
    ty: u32,
    body: Vec<u8>,
    calls: Vec<(u32, u32)>,
    other: Vec<(u8, u32, u32)>,
}

fn uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn padded(v: u32) -> Vec<u8> {
    let mut out = Vec::new();
    let mut v = v;
    for i in 0..5 {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        out.push(if i < 4 { b | 0x80 } else { b });
    }
    out
}

fn section(out: &mut Vec<u8>, id: u8, payload: &[u8]) {
    out.push(id);
    uleb(out, payload.len() as u64);
    out.extend_from_slice(payload);
}

fn name(out: &mut Vec<u8>, s: &str) {
    uleb(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

/// An object with types `(i32, i32) -> i32` (0) and `(i32) -> i32` (1), the
/// functions `fs` named `f0, f1, ...` with symbol flags `flags[i]`, and
/// `exports` (function export names and indices).
fn object(fs: &[F], flags: &[u32], exports: &[(&str, u32)]) -> Vec<u8> {
    object_with(fs, flags, exports, &[])
}

/// [`object`], plus a `reloc.DATA` section with an `R_WASM_TABLE_INDEX_I32`
/// relocation of each symbol of `data_refs` (functions whose address the
/// object's data takes).
fn object_with(fs: &[F], flags: &[u32], exports: &[(&str, u32)], data_refs: &[u32]) -> Vec<u8> {
    let mut out = b"\0asm\x01\0\0\0".to_vec();
    section(
        &mut out,
        1,
        &[2, 0x60, 2, 0x7f, 0x7f, 1, 0x7f, 0x60, 1, 0x7f, 1, 0x7f],
    );
    let mut func = Vec::new();
    uleb(&mut func, fs.len() as u64);
    for f in fs {
        uleb(&mut func, u64::from(f.ty));
    }
    section(&mut out, 3, &func);
    if !exports.is_empty() {
        let mut ex = Vec::new();
        uleb(&mut ex, exports.len() as u64);
        for (n, i) in exports {
            name(&mut ex, n);
            ex.push(0);
            uleb(&mut ex, u64::from(*i));
        }
        section(&mut out, 7, &ex);
    }
    let mut code = Vec::new();
    uleb(&mut code, fs.len() as u64);
    let mut relocs = Vec::new();
    for f in fs {
        uleb(&mut code, f.body.len() as u64);
        let start = code.len() as u32;
        code.extend_from_slice(&f.body);
        for &(at, sym) in &f.calls {
            relocs.push((0, start + at, sym));
        }
        for &(ty, at, index) in &f.other {
            relocs.push((ty, start + at, index));
        }
    }
    section(&mut out, 10, &code);
    let mut symtab = Vec::new();
    uleb(&mut symtab, fs.len() as u64);
    for (i, _) in fs.iter().enumerate() {
        symtab.push(0);
        uleb(&mut symtab, u64::from(flags[i]));
        uleb(&mut symtab, i as u64);
        name(&mut symtab, &format!("f{i}"));
    }
    let mut linking = Vec::new();
    name(&mut linking, "linking");
    linking.push(2);
    linking.push(8);
    uleb(&mut linking, symtab.len() as u64);
    linking.extend_from_slice(&symtab);
    section(&mut out, 0, &linking);
    if !relocs.is_empty() {
        let code_index = 2 + u64::from(!exports.is_empty());
        let mut rel = Vec::new();
        name(&mut rel, "reloc.CODE");
        uleb(&mut rel, code_index);
        uleb(&mut rel, relocs.len() as u64);
        for (ty, at, sym) in relocs {
            rel.push(ty);
            uleb(&mut rel, u64::from(at));
            uleb(&mut rel, u64::from(sym));
        }
        section(&mut out, 0, &rel);
    }
    if !data_refs.is_empty() {
        let mut rel = Vec::new();
        name(&mut rel, "reloc.DATA");
        uleb(&mut rel, 0);
        uleb(&mut rel, data_refs.len() as u64);
        for (i, &sym) in data_refs.iter().enumerate() {
            rel.push(2);
            uleb(&mut rel, 4 * i as u64);
            uleb(&mut rel, u64::from(sym));
        }
        section(&mut out, 0, &rel);
    }
    out
}

/// `local.get 0; local.get 1; i32.add; call <sym's function>; end`.
fn adder(callee: u32, sym: u32) -> F {
    let mut body = vec![0, 0x20, 0, 0x20, 1, 0x6a, OP_CALL];
    let at = body.len() as u32;
    body.extend(padded(callee));
    body.push(OP_END);
    F {
        ty: 0,
        body,
        calls: vec![(at, sym)],
        other: Vec::new(),
    }
}

/// `local.get 0; end` of type 0.
fn first() -> F {
    F {
        ty: 0,
        body: vec![0, 0x20, 0, OP_END],
        calls: Vec::new(),
        other: Vec::new(),
    }
}

/// The forwarder of a function of `params` parameters to `kept` (symbol
/// `sym`).
fn forwarder(params: u32, kept: u32, sym: u32) -> F {
    let mut body = vec![0];
    for p in 0..params {
        body.extend([0x20, p as u8]);
    }
    body.push(OP_CALL);
    let at = body.len() as u32;
    body.extend(padded(kept));
    body.push(OP_END);
    F {
        ty: 0,
        body,
        calls: vec![(at, sym)],
        other: Vec::new(),
    }
}

fn before() -> Vec<F> {
    vec![adder(2, 2), adder(2, 2), first()]
}

fn folded() -> Vec<F> {
    vec![adder(2, 2), forwarder(2, 0, 0), first()]
}

const STRONG: [u32; 3] = [0, 0, 0];

#[test]
fn a_forwarder_to_an_identical_body_holds() {
    let b = object(&before(), &STRONG, &[("e", 1)]);
    let a = object(&folded(), &STRONG, &[("e", 1)]);
    assert_eq!(check_body_folds(&b, &a, &[(1, 0)]), Ok(1));
}

#[test]
fn a_forwarder_may_bring_the_first_code_relocation() {
    // Bodies without calls: the object before the fold has no reloc.CODE.
    let plain = || F {
        ty: 0,
        body: vec![0, 0x20, 0, 0x20, 1, 0x6a, 0x20, 1, 0x6c, OP_END],
        calls: Vec::new(),
        other: Vec::new(),
    };
    let b = object(&[plain(), plain(), first()], &STRONG, &[]);
    let a = object(&[plain(), forwarder(2, 0, 0), first()], &STRONG, &[]);
    assert_eq!(check_body_folds(&b, &a, &[(1, 0)]), Ok(1));
}

#[test]
fn an_empty_witness_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    assert!(check_body_folds(&b, &b, &[]).is_err());
}

#[test]
fn bodies_that_differ_by_one_byte_are_refused() {
    let mut fs = before();
    fs[1].body[5] = 0x6b; // i32.sub
    let b = object(&fs, &STRONG, &[]);
    let a = object(&folded(), &STRONG, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("differs"), "{err}");
}

#[test]
fn bodies_whose_call_relocations_name_different_symbols_are_refused() {
    let mut fs = before();
    fs[1] = adder(2, 1);
    let b = object(&fs, &STRONG, &[]);
    let a = object(&folded(), &STRONG, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("differs"), "{err}");
}

#[test]
fn a_forwarder_to_another_function_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    let mut fs = folded();
    fs[1] = forwarder(2, 2, 2);
    let a = object(&fs, &STRONG, &[]);
    assert!(check_body_folds(&b, &a, &[(1, 0)]).is_err());
}

#[test]
fn a_forwarder_whose_relocation_names_another_symbol_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    let mut fs = folded();
    fs[1].calls = vec![(fs[1].calls[0].0, 2)];
    let a = object(&fs, &STRONG, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("symbol"), "{err}");
}

#[test]
fn a_forwarder_that_drops_a_parameter_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    let mut fs = folded();
    fs[1] = forwarder(1, 0, 0);
    let a = object(&fs, &STRONG, &[]);
    assert!(check_body_folds(&b, &a, &[(1, 0)]).is_err());
}

#[test]
fn a_forwarder_with_a_local_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    let mut fs = folded();
    let mut body = vec![1, 1, 0x7f];
    body.extend_from_slice(&fs[1].body[1..]);
    fs[1].calls[0].0 += 2;
    fs[1].body = body;
    let a = object(&fs, &STRONG, &[]);
    assert!(check_body_folds(&b, &a, &[(1, 0)]).is_err());
}

#[test]
fn a_change_to_an_unfolded_body_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    let mut fs = folded();
    fs[2].body[2] = 1; // local.get 1
    let a = object(&fs, &STRONG, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("not folded"), "{err}");
}

#[test]
fn a_weak_kept_symbol_is_refused() {
    let flags = [SYM_WEAK, 0, 0];
    let b = object(&before(), &flags, &[]);
    let a = object(&folded(), &flags, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("non-weak"), "{err}");
}

#[test]
fn functions_of_different_types_are_refused() {
    let mut fs = before();
    fs[1].ty = 1;
    let b = object(&fs, &STRONG, &[]);
    let mut gs = folded();
    gs[1] = forwarder(1, 0, 0);
    gs[1].ty = 1;
    let a = object(&gs, &STRONG, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("type"), "{err}");
}

#[test]
fn malformed_witnesses_are_refused() {
    let b = object(&before(), &STRONG, &[]);
    let a = object(&folded(), &STRONG, &[]);
    for (witness, why) in [
        (vec![(0, 0)], "itself"),
        (vec![(1, 0), (1, 0)], "twice"),
        (vec![(1, 0), (0, 1)], "itself folded"),
        (vec![(1, 7)], "not a defined function"),
    ] {
        let err = check_body_folds(&b, &a, &witness).unwrap_err();
        assert!(err.contains(why), "{witness:?}: {err}");
    }
}

#[test]
fn an_unwitnessed_fold_is_refused() {
    let b = object(&before(), &STRONG, &[]);
    let a = object(&folded(), &STRONG, &[]);
    // Function 1 changed, but the witness names only a fold of function 2.
    let mut fs = before();
    fs[2] = adder(2, 2);
    let b2 = object(&fs, &STRONG, &[]);
    assert!(check_body_folds(&b, &a, &[]).is_err());
    assert!(check_body_folds(&b2, &a, &[(2, 0)]).is_err());
}

#[test]
fn a_change_outside_the_code_section_is_refused() {
    let b = object(&before(), &STRONG, &[("e", 1)]);
    let a = object(&folded(), &STRONG, &[("e", 2)]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("section other than"), "{err}");
}

#[test]
fn a_forwarder_on_a_self_call_cycle_is_refused_and_the_called_member_is_kept() {
    // Both bodies call f1: folding f1 onto f0 would run f1's forwarder at
    // every recursion level; folding f0 onto f1 keeps the recursion on f1.
    let fs = vec![adder(1, 1), adder(1, 1), first()];
    let b = object(&fs, &STRONG, &[]);
    let a = object(&[adder(1, 1), forwarder(2, 0, 0), first()], &STRONG, &[]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("reachable"), "{err}");
    let a = object(&[forwarder(2, 1, 1), adder(1, 1), first()], &STRONG, &[]);
    assert_eq!(check_body_folds(&b, &a, &[(0, 1)]), Ok(1));
}

#[test]
fn a_forwarder_an_indirect_call_can_reach_is_refused() {
    // `local.get 0; local.get 1; call_indirect (type 0) 0; end`: the type
    // immediate carries an `R_WASM_TYPE_INDEX_LEB`.
    let indirect = || {
        let mut body = vec![0, 0x20, 0, 0x20, 1, 0x11];
        let at = body.len() as u32;
        body.extend(padded(0));
        body.extend([0, OP_END]);
        F {
            ty: 0,
            body,
            calls: Vec::new(),
            other: vec![(R_TYPE_INDEX_LEB, at, 0)],
        }
    };
    let fs = vec![indirect(), indirect(), first()];
    let folded = vec![indirect(), forwarder(2, 0, 0), first()];
    // f1 is local and no address of it is taken: the indirect call cannot
    // reach it.
    let local = [SYM_LOCAL; 3];
    let b = object(&fs, &local, &[]);
    let a = object(&folded, &local, &[]);
    assert_eq!(check_body_folds(&b, &a, &[(1, 0)]), Ok(1));
    // The data takes f1's address: f0's indirect call may reach f1.
    let b = object_with(&fs, &local, &[], &[1]);
    let a = object_with(&folded, &local, &[], &[1]);
    let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
    assert!(err.contains("reachable"), "{err}");
}

#[test]
fn a_forwarder_another_object_can_hand_to_an_indirect_call_is_refused() {
    // This object never takes f1's address, but f1's symbol is not local:
    // another object (another codegen unit) can take it and hand it to f0's
    // indirect call, so f0 -> f1 -> f0 is a cycle of this object's own
    // functions that would run f1's forwarder at every level.
    let indirect = || {
        let mut body = vec![0, 0x20, 0, 0x20, 1, 0x11];
        let at = body.len() as u32;
        body.extend(padded(0));
        body.extend([0, OP_END]);
        F {
            ty: 0,
            body,
            calls: Vec::new(),
            other: vec![(R_TYPE_INDEX_LEB, at, 0)],
        }
    };
    let fs = vec![indirect(), indirect(), first()];
    let folded = vec![indirect(), forwarder(2, 0, 0), first()];
    for flags in [
        [SYM_LOCAL, 0, SYM_LOCAL],
        [0, 0, 0],
        [SYM_LOCAL, SYM_WEAK, 0],
    ] {
        let b = object(&fs, &flags, &[]);
        let a = object(&folded, &flags, &[]);
        let err = check_body_folds(&b, &a, &[(1, 0)]).unwrap_err();
        assert!(err.contains("reachable"), "{flags:?}: {err}");
    }
    // A body without an indirect call reaches no global function it does
    // not name: the plain fold over strong symbols still holds.
    let b = object(&before(), &STRONG, &[]);
    let a = object(&self::folded(), &STRONG, &[]);
    assert_eq!(check_body_folds(&b, &a, &[(1, 0)]), Ok(1));
}
