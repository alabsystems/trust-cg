// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual parsed-type controls for the scalarized aggregate eligibility walk.
//! These exercise its existing depth-eight boundary, not ABI, source lowering,
//! native execution or proof admission. No rustc type or layout is fabricated.

use super::*;

include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

const CHILD: &str = "BRIDGE_PRIMITIVE_FIELD_DEPTH_TEST_CHILD";
const TEST: &str =
    "primitive_field_aggregate_tests::actual_array_struct_and_mixed_depth_bound_is_conservative";
const MARKER: &str = "primitive aggregate actual depth consumers checked: 19";

const SOURCE: &str = r#"
pub struct Carrier<T>(pub T);
pub enum LocalEnum { First(u64), Second(u64) }
pub union LocalUnion { pub unsigned: u64, pub signed: i64 }
pub type A1 = [u64; 1];
pub type A2 = [A1; 1];
pub type A3 = [A2; 1];
pub type A4 = [A3; 1];
pub type A5 = [A4; 1];
pub type A6 = [A5; 1];
pub type A7 = [A6; 1];
pub type A8 = [A7; 1];
pub type A9 = [A8; 1];
pub type S1 = Carrier<u64>;
pub type S2 = Carrier<S1>;
pub type S3 = Carrier<S2>;
pub type S4 = Carrier<S3>;
pub type S5 = Carrier<S4>;
pub type S6 = Carrier<S5>;
pub type S7 = Carrier<S6>;
pub type S8 = Carrier<S7>;
pub type S9 = Carrier<S8>;
pub type M1 = [u64; 1];
pub type M2 = Carrier<M1>;
pub type M3 = [M2; 1];
pub type M4 = Carrier<M3>;
pub type M5 = [M4; 1];
pub type M6 = Carrier<M5>;
pub type M7 = [M6; 1];
pub type M8 = Carrier<M7>;
pub type M9 = [M8; 1];
pub fn primitives(_: (bool, char, i8, u8, i64, u128, f32, f64)) {}
pub fn shallow_aggregate(_: Carrier<(u8, i64)>) {}
pub fn arrays_at_bound(_: Carrier<A8>) {}
pub fn arrays_beyond_bound(_: Carrier<A9>) {}
pub fn structs_at_bound(_: Carrier<S8>) {}
pub fn structs_beyond_bound(_: Carrier<S9>) {}
pub fn mixed_at_bound(_: Carrier<M8>) {}
pub fn mixed_beyond_bound(_: Carrier<M9>) {}
pub fn pointer_leaf(_: Carrier<*const u8>) {}
pub fn enum_leaf(_: Carrier<LocalEnum>) {}
pub fn union_leaf(_: Carrier<LocalUnion>) {}
pub fn primitive_root(_: u64) {}
pub fn array_root(_: A1) {}
pub fn empty_root(_: ()) {}
pub fn skipped_zero_sized_field(_: Carrier<[A9; 0]>) {}
"#;

#[test]
fn actual_array_struct_and_mixed_depth_bound_is_conservative() {
    const ROWS: &[(&str, bool)] = &[
        ("primitives", true),
        ("shallow_aggregate", true),
        ("arrays_at_bound", true),
        ("arrays_beyond_bound", false),
        ("structs_at_bound", true),
        ("structs_beyond_bound", false),
        ("mixed_at_bound", true),
        ("mixed_beyond_bound", false),
        ("pointer_leaf", false),
        ("enum_leaf", false),
        ("union_leaf", false),
        ("primitive_root", false),
        ("array_root", false),
        ("empty_root", false),
        ("skipped_zero_sized_field", true),
    ];

    if std::env::var_os(CHILD).is_some() {
        extern crate rustc_interface;

        struct Callbacks;
        impl rustc_driver::Callbacks for Callbacks {
            fn config(&mut self, config: &mut rustc_interface::interface::Config) {
                config.input = rustc_session::config::Input::Str {
                    name: rustc_span::FileName::Custom("primitive_field_depth_control.rs".into()),
                    input: SOURCE.into(),
                };
            }

            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let actual_type = |name: &str| {
                    let id = tcx
                        .hir_body_owners()
                        .find(|id| {
                            tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == name
                        })
                        .unwrap_or_else(|| panic!("actual source function {name}"));
                    let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                    tcx.erase_and_anonymize_regions(signature.inputs()[0])
                };
                let mut checked = 0;
                for &(name, expected) in ROWS {
                    let ty = actual_type(name);
                    assert_eq!(
                        is_primitive_field_aggregate(tcx, ty, 0),
                        expected,
                        "actual parsed {name}: {ty:?}"
                    );
                    checked += 1;
                }
                // Preserve the original aggregate-arm boundary too; arrays do
                // not receive a separate/reset budget when the walk starts deep.
                let primitives = actual_type("primitives");
                assert!(is_primitive_field_aggregate(tcx, primitives, 8));
                assert!(!is_primitive_field_aggregate(tcx, primitives, 9));
                assert!(!is_primitive_field_aggregate(tcx, primitives, u32::MAX));
                let arrays = actual_type("arrays_at_bound");
                assert!(!is_primitive_field_aggregate(tcx, arrays, 1));
                checked += 4;
                assert_eq!(checked, 19);
                eprintln!("primitive aggregate actual depth consumers checked: {checked}");
                rustc_driver::Compilation::Stop
            }
        }

        let sysroot = std::process::Command::new(BUILD_COMPILER)
            .args(["--print", "sysroot"])
            .output()
            .expect("resolve exact build compiler sysroot");
        assert!(
            sysroot.status.success(),
            "{}",
            String::from_utf8_lossy(&sysroot.stderr)
        );
        let args = vec![
            "trustc".to_owned(),
            "--crate-type=lib".to_owned(),
            "--emit=metadata".to_owned(),
            "--sysroot".to_owned(),
            String::from_utf8(sysroot.stdout).unwrap().trim().to_owned(),
            // Discarded parsed-type probe only; no verified build claim.
            "-Ztrust-verify=off".to_owned(),
            "-".to_owned(),
        ];
        rustc_driver::run_compiler(&args, &mut Callbacks);
        return;
    }

    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", TEST, "--nocapture"])
        .env(CHILD, "1")
        .output()
        .expect("run isolated actual aggregate depth consumers");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains(MARKER),
        "consumer controls never ran: {stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}
