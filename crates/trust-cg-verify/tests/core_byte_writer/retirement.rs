// Copyright 2026 Andrew Yates | Apache-2.0

//! Untrusted proof assembly for allocation-row preservation at root exit.
//! Elaboration reads the immutable ByteV1 environment; it adds no declarations.

use super::*;

struct RetirementLaw;
impl SourceTranslationModel for RetirementLaw {
    type Source = bool;
    fn build_environment() -> Result<Environment, String> {
        WriterModel::build_environment()
    }
    fn reconstruct(erase_history: &bool, _: &Module) -> Result<Expr, String> {
        // This helper is a memory law, independent of the target module. It
        // supplies no instruction, function or native-publication theorem.
        let mut scope = LocalScope::new();
        let rows = scope
            .try_local(app("IRList", [c("IRByteAllocationV1")]))
            .unwrap();
        let bytes = scope.try_local(bytes_type()).unwrap();
        let cursor = scope.try_local(c("Nat")).unwrap();
        let next = scope.try_local(c("Nat")).unwrap();
        let admitted = scope
            .try_local(eq(
                c("Bool"),
                app(
                    "ir_byte_memory_owners_v1",
                    [
                        app(
                            "IRByteMemoryV1.mk",
                            [
                                rows.term().clone(),
                                bytes.term().clone(),
                                cursor.term().clone(),
                            ],
                        ),
                        list("Nat", &[]),
                        next.term().clone(),
                    ],
                ),
                c("Bool.true"),
            ))
            .unwrap();
        let mut claim = eq(
            app("IRList", [c("IRByteAllocationV1")]),
            app(
                "ir_byte_retire_allocs_v1",
                [next.term().clone(), rows.term().clone()],
            ),
            if *erase_history {
                list("IRByteAllocationV1", &[])
            } else {
                rows.term().clone()
            },
        );
        for local in [&admitted, &next, &cursor, &bytes, &rows] {
            claim = local.pi(claim);
        }
        scope.close(&claim).map_err(|e| e.to_string())
    }
}

pub(super) fn proof_term() -> Expr {
    static TERM: std::sync::OnceLock<Expr> = std::sync::OnceLock::new();
    TERM.get_or_init(|| {
        let spec = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
        clean_verify::spec::SpecExpr::new(PROOF)
            .elaborate(spec.env())
            .unwrap()
            .clone()
    })
    .clone()
}

#[test]
fn entry_retirement_preserves_all_caller_rows() {
    let module = module();
    let proof = trust_ir::proof::encode_clean_expr_dag_v2(&proof_term()).unwrap();
    let checker = TranslationRechecker::<RetirementLaw>::new(Default::default()).unwrap();
    let checked = checker.recheck_dag_v2(&false, &module, &proof).unwrap();
    export(
        "caller-retirement",
        checked.proof_term(),
        serde_json::json!({
            "proof_bytes":proof.len(),
            "quantified":"allocation rows, bytes, cursor, owner bound",
            "premise":"actual ByteV1 memory ownership admission with an empty active owner list",
            "claim":"retiring the owner bound preserves every input allocation row"
        }),
    );
    let error = checker
        .recheck_dag_v2(&true, &module, &proof)
        .expect_err("erased history");
    assert_eq!(error.stage(), "kernel audit");
    assert!(error.reason().contains("TypeMismatch"), "{error}");
    for resource in [
        "heartbeat",
        "budget",
        "timeout",
        "fuel exhausted",
        "recursion limit",
    ] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "{error}"
        );
    }
    if let Some(directory) = std::env::var_os("TCG_CORE_BYTE_WRITER_EXPORT") {
        let directory = std::path::Path::new(&directory);
        let label = "caller-retirement-erased-history";
        std::fs::write(
            directory.join(format!("reject-{label}.json")),
            serde_json::to_vec_pretty(&serde_json::json!({
                "label":label, "stage":error.stage(), "reason":error.reason()
            }))
            .unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join(format!("{label}.rejected-dag")), &proof).unwrap();
    }
}

const PROOF: &str = r"fun (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat) (cursor next : Nat)
  (admitted : Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk allocs bytes cursor) (IRList.nil Nat) next) Bool.true) =>
let different : forall (a b : Nat), Eq Bool (ir_nat_ltb a b) Bool.true -> Eq Bool (ir_nat_eqb b a) Bool.false :=
  fun (a b : Nat) (below : Eq Bool (ir_nat_ltb a b) Bool.true) =>
  Eq.trans Bool (ir_nat_eqb b a) (ir_nat_eqb_walk b a) Bool.false
    (ir_nat_eqb_walk_eq b a)
    (Nat.rec
      (fun (x : Nat) => forall (y : Nat), Eq Bool (ir_nat_ltb_walk x y) Bool.true -> Eq Bool (ir_nat_eqb_walk y x) Bool.false)
      (fun (y : Nat) => Nat.rec
        (fun (z : Nat) => Eq Bool (ir_nat_ltb_walk 0 z) Bool.true -> Eq Bool (ir_nat_eqb_walk z 0) Bool.false)
        (fun (bad : Eq Bool Bool.false Bool.true) => False.elim (Eq Bool Bool.true Bool.false) (ir_byte_world_false_true_v1 bad))
        (fun (z : Nat) (_ : Eq Bool (ir_nat_ltb_walk 0 z) Bool.true -> Eq Bool (ir_nat_eqb_walk z 0) Bool.false) =>
          fun (_ : Eq Bool Bool.true Bool.true) => Eq.refl Bool Bool.false) y)
      (fun (x : Nat) (ih : forall (y : Nat), Eq Bool (ir_nat_ltb_walk x y) Bool.true -> Eq Bool (ir_nat_eqb_walk y x) Bool.false) =>
        fun (y : Nat) => Nat.rec
          (fun (z : Nat) => Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true -> Eq Bool (ir_nat_eqb_walk z (Nat.succ x)) Bool.false)
          (fun (_ : Eq Bool Bool.false Bool.true) => Eq.refl Bool Bool.false)
          (fun (z : Nat) (_ : Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true -> Eq Bool (ir_nat_eqb_walk z (Nat.succ x)) Bool.false) =>
            fun (h : Eq Bool (ir_nat_ltb_walk x z) Bool.true) => ih z h) y)
      a b (Eq.trans Bool (ir_nat_ltb_walk a b) (ir_nat_ltb a b) Bool.true
        (Eq.symm Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) (ir_nat_ltb_walk_eq a b)) below));
let rowIdentity : forall (row : IRByteAllocationV1), Eq Bool (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) Bool.true ->
  Eq IRByteAllocationV1
    (IRByteAllocationV1.mk (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row) (ir_byte_alloc_owner_v1 row)
      (Bool.and (ir_byte_alloc_live_v1 row) (Bool.not (ir_nat_eqb next (ir_byte_alloc_owner_v1 row))))) row :=
  IRByteAllocationV1.rec
    (fun (row : IRByteAllocationV1) => Eq Bool (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) Bool.true ->
      Eq IRByteAllocationV1
        (IRByteAllocationV1.mk (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row) (ir_byte_alloc_owner_v1 row)
          (Bool.and (ir_byte_alloc_live_v1 row) (Bool.not (ir_nat_eqb next (ir_byte_alloc_owner_v1 row))))) row)
    (fun (base size owner : Nat) (live : Bool) (below : Eq Bool (ir_nat_ltb owner next) Bool.true) =>
      Eq.trans IRByteAllocationV1
        (IRByteAllocationV1.mk base size owner (Bool.and live (Bool.not (ir_nat_eqb next owner))))
        (IRByteAllocationV1.mk base size owner (Bool.and live Bool.true))
        (IRByteAllocationV1.mk base size owner live)
        (ir_eq_cong Bool IRByteAllocationV1
          (fun (same : Bool) => IRByteAllocationV1.mk base size owner (Bool.and live (Bool.not same)))
          (ir_nat_eqb next owner) Bool.false (different owner next below))
        (ir_eq_cong Bool IRByteAllocationV1 (fun (flag : Bool) => IRByteAllocationV1.mk base size owner flag)
          (Bool.and live Bool.true) live
          (Bool.rec (fun (flag : Bool) => Eq Bool (Bool.and flag Bool.true) flag)
            (Eq.refl Bool Bool.false) (Eq.refl Bool Bool.true) live)));
IRList.rec IRByteAllocationV1
  (fun (xs : IRList IRByteAllocationV1) =>
    Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk xs bytes cursor) (IRList.nil Nat) next) Bool.true ->
    Eq (IRList IRByteAllocationV1) (ir_byte_retire_allocs_v1 next xs) xs)
  (fun (_ : Eq Bool Bool.true Bool.true) => Eq.refl (IRList IRByteAllocationV1) (IRList.nil IRByteAllocationV1))
  (fun (row : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
    (ih : Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail bytes cursor) (IRList.nil Nat) next) Bool.true ->
      Eq (IRList IRByteAllocationV1) (ir_byte_retire_allocs_v1 next tail) tail)
    (h : Eq Bool (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk (IRList.cons IRByteAllocationV1 row tail) bytes cursor) (IRList.nil Nat) next) Bool.true) =>
    let rowGuard : Eq Bool (Bool.and (ir_byte_alloc_valid_v1 row) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 row)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 row) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 row) (IRList.nil Nat)))))) Bool.true := ir_byte_world_and_right_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail bytes cursor) (IRList.nil Nat) next) (Bool.and (ir_byte_alloc_valid_v1 row) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 row)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 row) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 row) (IRList.nil Nat)))))) h;
    let boundGuard : Eq Bool (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) Bool.true := ir_byte_world_and_left_v1 (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 row)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 row) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 row) (IRList.nil Nat))))
      (ir_byte_world_and_right_v1 (ir_byte_alloc_valid_v1 row) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 row)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 row) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 row) (IRList.nil Nat))))) rowGuard);
    Eq.trans (IRList IRByteAllocationV1)
      (IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row) (ir_byte_alloc_owner_v1 row) (Bool.and (ir_byte_alloc_live_v1 row) (Bool.not (ir_nat_eqb next (ir_byte_alloc_owner_v1 row))))) (ir_byte_retire_allocs_v1 next tail))
      (IRList.cons IRByteAllocationV1 row (ir_byte_retire_allocs_v1 next tail))
      (IRList.cons IRByteAllocationV1 row tail)
      (ir_eq_cong IRByteAllocationV1 (IRList IRByteAllocationV1)
        (fun (head : IRByteAllocationV1) => IRList.cons IRByteAllocationV1 head (ir_byte_retire_allocs_v1 next tail))
        (IRByteAllocationV1.mk (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row) (ir_byte_alloc_owner_v1 row) (Bool.and (ir_byte_alloc_live_v1 row) (Bool.not (ir_nat_eqb next (ir_byte_alloc_owner_v1 row))))) row (rowIdentity row boundGuard))
      (ir_eq_cong (IRList IRByteAllocationV1) (IRList IRByteAllocationV1)
        (fun (xs : IRList IRByteAllocationV1) => IRList.cons IRByteAllocationV1 row xs)
        (ir_byte_retire_allocs_v1 next tail) tail
        (ih (ir_byte_world_and_left_v1 (ir_byte_memory_owners_v1 (IRByteMemoryV1.mk tail bytes cursor) (IRList.nil Nat) next) (Bool.and (ir_byte_alloc_valid_v1 row) (Bool.and (ir_nat_ltb (ir_byte_alloc_owner_v1 row) next) (Bool.or (Bool.not (ir_byte_alloc_live_v1 row)) (Bool.or (ir_nat_eqb (ir_byte_alloc_owner_v1 row) 0) (ir_byte_owner_member_v1 (ir_byte_alloc_owner_v1 row) (IRList.nil Nat)))))) h)))) allocs admitted
";
