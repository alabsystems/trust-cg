// Host-side guards for the rustc_codegen_trust_cg MIR coverage inventory.
//
// These tests intentionally inspect the rustc-private backend source as text so
// they can run from the normal Trust Codegen workspace without rustc-dev.

use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("trust-cg-test crate lives two levels below the repo root")
        .to_owned()
}

fn read_repo_file(path: &str) -> String {
    let path = repo_root().join(path);
    std::fs::read_to_string(&path).unwrap_or_else(|err| {
        panic!("failed to read {}: {err}", path.display());
    })
}

#[test]
fn statement_intrinsic_admits_only_the_bounded_slice() {
    // `lower_statement` admits `StatementKind::Intrinsic` ONLY for the bounded
    // `NonDivergingIntrinsic` slice: `Assume` (a sound no-op — an assume states
    // a UB precondition the compiled code need not check) and
    // `CopyNonOverlapping` (via `lower_copy_nonoverlapping`, which fails closed
    // on unmodeled shapes). The inner match must stay EXHAUSTIVE over
    // `NonDivergingIntrinsic` (no wildcard) so a future rustc variant is a
    // compile error, never a silent no-op; every other `StatementKind` still
    // routes through the single fail-closed fallback naming the variant.
    let source = read_repo_file("crates/rustc-codegen-trust-cg/src/lib.rs");

    let lower_statement = source
        .split("fn lower_statement<'tcx>(")
        .nth(1)
        .expect("lower_statement must exist")
        .split("\nfn ")
        .next()
        .expect("lower_statement body must be bounded");

    // The modeled statement arms.
    assert!(
        lower_statement
            .contains("StatementKind::StorageLive(local) | StatementKind::StorageDead(local)")
            && lower_statement.contains("StatementKind::Assign(boxed)"),
        "lower_statement must keep the modeled StorageLive/StorageDead/Assign arms"
    );
    // Every unmodeled StatementKind hits the fail-closed fallback that names
    // the variant — there is no silent no-op fall-through.
    assert!(
        lower_statement
            .contains("other => Err(format!(\"StatementKind::{}\", statement_kind_name(other)))"),
        "lower_statement must fail closed for unmodeled statements, naming the StatementKind variant"
    );
    // The Intrinsic arm is the bounded slice: exhaustive inner match with
    // exactly the Assume no-op and the fail-closed-inside copy lowering. A
    // wildcard in the inner match would let a future intrinsic silently no-op.
    let intrinsic_arm = lower_statement
        .split("StatementKind::Intrinsic(intrinsic) => match &**intrinsic {")
        .nth(1)
        .expect("lower_statement must have the bounded Intrinsic slice arm")
        .split("},")
        .next()
        .expect("Intrinsic arm must be bounded");
    assert!(
        intrinsic_arm.contains("NonDivergingIntrinsic::Assume(_) => Ok(())")
            && intrinsic_arm.contains("NonDivergingIntrinsic::CopyNonOverlapping(copy)")
            && intrinsic_arm.contains("lower_copy_nonoverlapping"),
        "Intrinsic slice must admit exactly Assume (no-op) and CopyNonOverlapping (fail-closed lowering)"
    );
    assert!(
        !intrinsic_arm.contains("=> Ok(())\n            _")
            && !intrinsic_arm.contains("_ => Ok(())"),
        "Intrinsic inner match must not wildcard-admit unmodeled intrinsics as no-ops"
    );
}

#[test]
fn statement_intrinsic_inventory_doc_names_the_same_blocker() {
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    assert!(
        doc.contains(
            "| `Intrinsic` | partial | `StatementKind::Intrinsic` | Bounded slice: `Assume` is a sound no-op; `CopyNonOverlapping` lowers via `lower_copy_nonoverlapping` and fails closed on unmodeled shapes."
        ),
        "MIR coverage doc must describe the bounded StatementKind::Intrinsic slice"
    );
}

#[test]
fn statement_retag_fail_closed_blocker_is_explicit_in_frontend_and_docs() {
    let source = read_repo_file("crates/rustc-codegen-trust-cg/src/lib.rs");
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    let lower_statement = source
        .split("fn lower_statement<'tcx>(")
        .nth(1)
        .expect("lower_statement must exist")
        .split("\nfn ")
        .next()
        .expect("lower_statement body must be bounded");

    // `Retag` carries Rust provenance/alias semantics that the scalar lowering
    // does not model. It must never be admitted (which would silently treat it
    // as a no-op); instead it reaches the fail-closed fallback that names the
    // variant, so a required root aborts codegen rather than miscompiling.
    assert!(
        !lower_statement.contains("StatementKind::Retag"),
        "lower_statement must not admit StatementKind::Retag; it must reach the fail-closed fallback"
    );
    assert!(
        lower_statement
            .contains("other => Err(format!(\"StatementKind::{}\", statement_kind_name(other)))"),
        "lower_statement must fail closed for unmodeled statements such as Retag"
    );
    assert!(
        source.contains("StatementKind::Retag(_, _) => \"Retag\""),
        "statement_kind_name must surface Retag so the fail-closed diagnostic names the blocker"
    );
    assert!(
        doc.contains(
            "| `Retag` | fail-closed | `StatementKind::Retag` | Rust provenance/alias retag semantics are not modeled by scalar side tables. |"
        ),
        "MIR coverage doc must preserve the executable StatementKind::Retag blocker"
    );
}

#[test]
fn replacement_ledger_forbids_full_replacement_overclaiming() {
    let ledger = read_repo_file("trust-cg-full-replacement-ledger.md");

    for required in [
        "trust-cg is **not** ready to replace LLVM, rustc's production codegen backends",
        "v0.1.0 is a source-only research",
        "It does not mean complete language, target, ABI, object, or proof",
        "| Rust frontend bridge | Experimental and partial |",
        "| AArch64 backend | Useful partial path |",
        "| x86-64 backend | Useful partial path |",
        "Replacement remains blocked on at least:",
        "This ledger can move from **blocked** only after all of the following are true:",
        "describe trust-cg as a **proof-oriented research backend**",
        "verified replacement compiler.",
    ] {
        assert!(
            ledger.contains(required),
            "full replacement ledger must preserve stale-overclaim guard: {required}"
        );
    }

    for forbidden in [
        "Current replacement readiness: **ready**",
        "trust-cg is **ready** to replace LLVM",
        "Trust-CG is full Rust frontend replacement-ready",
        "Trust-CG is full `trust-ir` replacement-ready",
        "Trust-CG is AArch64/x86_64 backend parity replacement-ready",
    ] {
        assert!(
            !ledger.contains(forbidden),
            "full replacement ledger must not claim replacement readiness while blockers remain: {forbidden}"
        );
    }
}

#[test]
fn mir_inventory_keeps_blocked_replacement_anchors() {
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    for required in [
        "Readiness invariant: this inventory is not evidence that Trust-CG is full Rust frontend replacement-ready or full `trust-ir` replacement-ready.",
        "It is a stale-overclaim guard.",
        "| Rust frontend parity | blocked |",
        "| trust-ir semantic parity | blocked |",
        "| AArch64 backend parity | blocked |",
        "| x86_64 backend parity | blocked |",
        "Rows marked `supported` or `partial` describe only the current admitted slice",
        "replacement remains blocked on rustc layout/ABI coverage",
        "complete `trust-ir` semantics",
        "AArch64/x86_64 backend parity",
    ] {
        assert!(
            doc.contains(required),
            "MIR inventory must preserve replacement blocker anchor: {required}"
        );
    }
}

#[test]
fn rustc_custom_boundary_spine_and_fnabi_blocker_are_explicit_in_frontend_and_docs() {
    // The native-fused frontend derives function-boundary signatures from rustc
    // `fn_sig` (read per callable shape: `FnDef`/`FnPtr` directly, closures via
    // the closure substs) and routes aggregate/fat-pointer arguments and returns
    // through the backend's *verified* SysV eightbyte classification. The
    // soundness contract the test guards is the fail-closed perimeter:
    //   * any remaining callable shape without a directly-derivable signature
    //     returns `Err`, never an ICE or a guessed signature;
    //   * a scalar Rust type that is not representable as a trust-ir scalar
    //     fails closed in `rust_ty_to_trust_ir_ty` rather than being widened
    //     silently.
    let source = read_repo_file("crates/rustc-codegen-trust-cg/src/lib.rs");
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    // This is a custom signature/layout classifier, not rustc `FnAbi` /
    // `PassMode` consumption. If the frontend starts consuming those APIs, this
    // guard and the inventory must be updated together rather than silently
    // retaining the narrower claim.
    assert!(
        !source.contains("PassMode::"),
        "frontend gained rustc PassMode consumption; update the ABI inventory and this guard"
    );
    assert!(
        doc.contains("does **not** consume rustc `FnAbi` or `PassMode`")
            && doc.contains("Complete `FnAbi`, pass-mode, calling-")
            && doc.contains("convention, and attribute integration remains a replacement blocker"),
        "MIR coverage doc must distinguish the custom boundary classifier from missing rustc FnAbi/PassMode integration"
    );

    let func_ty = source
        .split("fn func_ty_for_instance(")
        .nth(1)
        .expect("func_ty_for_instance must exist")
        .split("\n    fn extern_callee(")
        .next()
        .expect("func_ty_for_instance body must be bounded");

    // Signatures are read per callable shape from rustc `fn_sig`/closure substs.
    assert!(
        func_ty.contains("ty::FnDef(..) | ty::FnPtr(..) => instance_ty.fn_sig(self.tcx)")
            && func_ty.contains("ty::Closure(_, args)"),
        "func_ty_for_instance must read rustc fn_sig per callable shape (FnDef/FnPtr/Closure)"
    );
    // Any other callable shape (coroutines, etc.) fails closed instead of ICEing.
    assert!(
        func_ty.contains("unsupported callable shape for signature"),
        "func_ty_for_instance must fail closed (not ICE) for unsupported callable shapes"
    );
    // Aggregate / fat-pointer ABI is routed through the verified SysV classifier,
    // not guessed at the frontend.
    assert!(
        func_ty.contains("fat_ptr_or_memory_aggregate_layout(self.tcx, input)?")
            && func_ty.contains("fat_ptr_or_memory_aggregate_layout(self.tcx, output)?"),
        "function-boundary aggregate/fat-pointer ABI must route through fat_ptr_or_memory_aggregate_layout for both params and returns"
    );
    assert!(
        source.contains("verified SysV"),
        "frontend must document that the aggregate ABI relies on the backend's verified SysV classification"
    );
    // Scalar types that have no trust-ir representation fail closed at the
    // scalar conversion, so a Rust scalar is never silently widened/reshaped.
    assert!(
        source.contains("fn rust_ty_to_trust_ir_ty"),
        "scalar argument/return types must flow through rust_ty_to_trust_ir_ty, which fails closed on unrepresentable scalars"
    );
    // The doc still records `FnAbi`/`TyAndLayout`/ABI coverage as a hard
    // replacement blocker: the current slice is admitted, not replacement-ready.
    assert!(
        doc.contains("Complete rustc MIR, mono item, `FnAbi`")
            && doc.contains("replacement remains blocked on rustc layout/ABI coverage"),
        "MIR coverage doc must keep full rustc FnAbi/layout/ABI coverage as a replacement blocker"
    );
    assert!(
        doc.contains(
            "| `AggregateAbiClassification` | partial | `classify_func_ty` / `fat_ptr_or_memory_aggregate_layout` | Selected struct, tuple, array, enum, union, closure, and fat-pointer boundaries use layout-derived carriers plus the backend's bounded SysV register-pair/stack/sret classifier."
        ),
        "MIR coverage doc must describe the bounded aggregate ABI lane without claiming rustc FnAbi parity"
    );
}

#[test]
fn static_inventory_tracks_the_identity_safe_partial_slice() {
    let source = read_repo_file("crates/rustc-codegen-trust-cg/src/lib.rs");
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    let emit_const_alloc_global = source
        .split("fn emit_const_alloc_global(")
        .nth(1)
        .expect("emit_const_alloc_global must exist")
        .split("\nfn emit_thread_local_global(")
        .next()
        .expect("emit_const_alloc_global must be bounded");
    let static_arm = emit_const_alloc_global
        .split("GlobalAlloc::Static(def_id) => {")
        .nth(1)
        .expect("const-allocation lowering must handle static targets explicitly")
        .split("GlobalAlloc::VTable(..)")
        .next()
        .expect("static target arm must be bounded before vtable/type-id rejection");

    assert!(
        static_arm.contains("if ctx.tcx.is_thread_local_static(def_id)")
            && static_arm.contains("const reference to thread-local static"),
        "ordinary const-allocation lowering must reject a TLS static address rather than emit a non-TLS reference"
    );

    let mutable_arm = static_arm
        .split("if global_alloc.mutability")
        .nth(1)
        .expect("static target arm must classify mutability")
        .split("\n            let evaluated =")
        .next()
        .expect("mutable static arm must be bounded before immutable evaluation");
    for required in [
        "== rustc_hir::Mutability::Mut",
        "symbol_name(Instance::mono(ctx.tcx, def_id))",
        "mutable: true",
        "initializer: None",
        "linkage: Linkage::External",
        "return Ok(canonical);",
    ] {
        assert!(
            mutable_arm.contains(required),
            "mutable static readers must import the canonical writable symbol; missing `{required}`"
        );
    }

    let local_immutable_arm = static_arm
        .split("if def_id.is_local() {")
        .nth(1)
        .expect("local immutable static target must have a canonical-symbol path")
        .split("\n                return Ok(canonical);")
        .next()
        .expect("local immutable static arm must return the canonical symbol");
    for required in [
        "symbol_name(Instance::mono(ctx.tcx, def_id))",
        "mutable: false",
        "initializer: None",
        "linkage: Linkage::External",
    ] {
        assert!(
            local_immutable_arm.contains(required),
            "local immutable static readers must import one canonical symbol; missing `{required}`"
        );
    }

    assert!(
        doc.contains("| `Static` | partial | `MonoItem::Static` / `compile_static_data_object` |")
            && doc.contains("canonical symbol")
            && doc.contains("unsupported-target TLS still fail closed"),
        "MIR inventory must describe the bounded, identity-safe static slice and its fail-closed perimeter"
    );
    assert!(
        !doc.contains("| `Static` | fail-closed |"),
        "MIR inventory must not claim the implemented static slice is wholly fail-closed"
    );
}

#[test]
fn rust_mono_item_driver_admits_no_unverified_variant() {
    let source = read_repo_file("crates/rustc-codegen-trust-cg/src/lib.rs");
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    // The mono-item driver handles every `MonoItem` variant EXPLICITLY, and
    // admits object emission only through verified envelopes:
    //   - `MonoItem::Fn` bodies via MIR lowering (fail-closed per body);
    //   - `MonoItem::Static` solely via `compile_static_data_object`, whose
    //     `Err` pushes a failed root — never silent, never guessed bytes;
    //   - `MonoItem::GlobalAsm` is refusal-ONLY: raw module-level assembly
    //     cannot be parsed/modeled/verified, so the arm pushes a
    //     `[TCG-GLOBAL-ASM]` failed root and emits nothing. A silent
    //     fall-through here is the hazard this test pins against: asm whose
    //     effect is not via a referenced symbol would be dropped with zero
    //     diagnostic.
    let driver = source
        .split("for cgu in tcx.collect_and_partition_mono_items(()).codegen_units {")
        .nth(1)
        .expect("mono-item codegen-unit driver must exist")
        .split("\n    if !failed_roots.is_empty()")
        .next()
        .expect("mono-item driver body must be bounded");

    assert!(
        driver.contains("if let MonoItem::Fn(instance) = mono_item {"),
        "mono-item driver must admit MonoItem::Fn bodies through MIR lowering"
    );
    // Static admission goes solely through the fail-closed
    // `compile_static_data_object` envelope, with the Err path a failed root.
    assert!(
        driver.contains("else if let MonoItem::Static(def_id) = mono_item {")
            && driver.contains("compile_static_data_object"),
        "MonoItem::Static must be admitted solely via compile_static_data_object's fail-closed envelope"
    );
    // GlobalAsm must be present AND refusal-only: a tagged failed-roots push
    // with no module emission in its arm.
    let global_asm_arm = driver
        .split("else if let MonoItem::GlobalAsm(item_id) = mono_item {")
        .nth(1)
        .expect("mono-item driver must have an explicit MonoItem::GlobalAsm refusal arm (silent drop is the hazard)")
        .split("\n            }")
        .next()
        .expect("GlobalAsm arm must be bounded");
    assert!(
        global_asm_arm.contains("[TCG-GLOBAL-ASM]") && global_asm_arm.contains("failed_roots.push"),
        "GlobalAsm arm must fail closed with a [TCG-GLOBAL-ASM] failed-roots push"
    );
    assert!(
        !global_asm_arm.contains("modules.push")
            && !global_asm_arm.contains("deferred_unlowerable"),
        "GlobalAsm arm must be refusal-only: no object emission, and never GC-deferred (its effect is invisible to the reference graph)"
    );
    // The fail-closed-by-link contract must be documented at the driver so the
    // shape of the admission perimeter is intentional, not an oversight.
    assert!(
        source.contains("link surfaces an undefined symbol") || source.contains("undefined symbol"),
        "frontend must document that unlowered/unadmitted symbols fail closed at link, never miscompile"
    );
    assert!(
        doc.contains("[TCG-GLOBAL-ASM]"),
        "MIR coverage doc's GlobalAsm row must name the [TCG-GLOBAL-ASM] refusal tag"
    );
}

#[test]
fn rustc_direct_aggregate_abi_gate_remains_exact_after_lower_aarch64_formal_result_materialization()
{
    // By-value aggregate function boundaries are admitted only through a
    // *layout-driven* path: `memory_aggregate_layout` consults rustc
    // `tcx.layout_of`, walks variants/tag-encoding/field offsets, and requires
    // every field leaf to be a supported scalar (`validate_memory_aggregate_field_leaves`).
    // Anything the layout walk cannot model — unsized aggregates, non-scalar
    // niche fields, nested aggregate leaves, layout query failure — fails closed
    // (`Err`/`Ok(None)` keeping the conservative scalar path) rather than being
    // passed with a guessed ABI. The verified SysV eightbyte classifier then
    // places the slot in a register pair / via sret, matching rustc. This test
    // guards that the aggregate ABI gate stays layout-driven and fail-closed.
    let source = read_repo_file("crates/rustc-codegen-trust-cg/src/lib.rs");
    let doc = read_repo_file("rustc-mir-coverage-inventory.md");

    let agg_layout = source
        .split("fn memory_aggregate_layout<'tcx>(")
        .nth(1)
        .expect("memory_aggregate_layout must remain the aggregate ABI gate")
        .split("\nfn ")
        .next()
        .expect("memory_aggregate_layout body must be bounded");

    // The aggregate ABI is derived from rustc layout, not guessed.
    assert!(
        agg_layout.contains(".layout_of(")
            && agg_layout.contains("memory aggregate layout_of failed"),
        "aggregate ABI must consume rustc TyAndLayout (layout_of) and fail closed when the layout query fails"
    );
    // Only sized, non-ZST named ADTs are admitted; everything else keeps the
    // conservative scalar path (Ok(None)) and is never given a guessed agg ABI.
    assert!(
        agg_layout.contains("if !layout.is_sized() {") && agg_layout.contains("return Ok(None);"),
        "unsized aggregates must fail closed out of the by-value aggregate ABI path"
    );
    // Variant/tag-encoding classification is explicit, and a niche over a
    // non-scalar field fails closed.
    assert!(
        agg_layout.contains("Variants::Multiple")
            && agg_layout.contains("TagEncoding::Direct")
            && agg_layout.contains("TagEncoding::Niche")
            && agg_layout.contains("niche field is not a single scalar"),
        "enum aggregate ABI must classify Direct/Niche tag encodings and fail closed on non-scalar niche fields"
    );
    // Every field leaf must be a supported scalar — nested aggregate leaves fail
    // closed via the leaf validator.
    assert!(
        source.contains("fn validate_memory_aggregate_field_leaves")
            && agg_layout
                .contains("validate_memory_aggregate_field_leaves(tcx, &cx, &field_layout)?"),
        "aggregate ABI must validate every field leaf is a supported scalar (nested aggregates fail closed)"
    );
    // The doc records the admitted aggregate ABI slice as partial while keeping
    // full rustc FnAbi/pass-mode parity a replacement blocker.
    assert!(
        doc.contains(
            "| `AggregateAbiClassification` | partial | `classify_func_ty` / `fat_ptr_or_memory_aggregate_layout` | Selected struct, tuple, array, enum, union, closure, and fat-pointer boundaries use layout-derived carriers plus the backend's bounded SysV register-pair/stack/sret classifier."
        ) && doc.contains(
            "| `FnAbiPassMode` | fail-closed | `func_ty_for_instance` / `classify_func_ty` | rustc `FnAbi` and its `Ignore`/`Direct`/`Pair`/`Cast`/`Indirect` pass modes are not consumed."
        ),
        "rustc MIR inventory must describe the partial aggregate lane and preserve full FnAbi/pass-mode integration as a blocker"
    );
}
