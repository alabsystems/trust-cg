// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual rustc type-context consumers of the stride-state layout checker.
//! These are structural helper controls, not intercepted-source, native,
//! coverage or proof claims. No rustc ADT or layout is fabricated.

use super::*;

// The same build-script-owned compiler identity used by the existing isolated
// rustc type-context controls; do not search PATH for a different sysroot.
include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

const CHILD: &str = "BRIDGE_STRIDE_LAYOUT_TEST_CHILD";
const TEST: &str = "stride_iter_layout_tests::actual_std_layouts_survive_and_other_real_types_refuse_without_panicking";
const MARKER: &str = "stride layout actual consumers checked: 7";

const SOURCE: &str = r#"
pub enum LocalEnum { First(u64), Second(u64) }
pub union LocalUnion { pub unsigned: u64, pub signed: i64 }
pub struct WrongFields { pub v: &'static [u64], pub other: usize }
pub fn enum_type(_: LocalEnum) {}
pub fn union_type(_: LocalUnion) {}
pub fn primitive_type(_: u64) {}
pub fn wrong_fields(_: WrongFields) {}
pub fn chunks_type(_: std::slice::Chunks<'static, u64>) {}
pub fn exact_type(_: std::slice::ChunksExact<'static, u64>) {}
pub fn windows_type(_: std::slice::Windows<'static, u64>) {}
"#;

#[test]
fn actual_std_layouts_survive_and_other_real_types_refuse_without_panicking() {
    if std::env::var_os(CHILD).is_some() {
        extern crate rustc_interface;

        struct Callbacks;
        impl rustc_driver::Callbacks for Callbacks {
            fn config(&mut self, config: &mut rustc_interface::interface::Config) {
                config.input = rustc_session::config::Input::Str {
                    name: rustc_span::FileName::Custom("stride_layout_control.rs".into()),
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
                        .find(|id| tcx.item_name(id.to_def_id()).as_str() == name)
                        .unwrap_or_else(|| panic!("actual source function {name}"));
                    let signature = tcx.fn_sig(id).instantiate_identity().skip_binder();
                    tcx.erase_and_anonymize_regions(signature.inputs()[0])
                };
                for name in ["enum_type", "union_type", "wrong_fields"] {
                    let ty = actual_type(name);
                    assert!(slice_stride_iter_element_ty(tcx, ty).is_none());
                    let reason = slice_stride_iter_layout(tcx, ty, SliceStrideIter::Chunks)
                        .err()
                        .expect("unsupported actual ADT must return an error, not panic");
                    assert!(
                        reason.contains("is not a sized single-variant struct with exactly"),
                        "{name}: {reason}"
                    );
                }
                let primitive = slice_stride_iter_layout(
                    tcx,
                    actual_type("primitive_type"),
                    SliceStrideIter::Chunks,
                )
                .err()
                .expect("existing non-ADT refusal");
                assert!(primitive.ends_with("is not a struct"), "{primitive}");

                for (name, kind) in [
                    ("chunks_type", SliceStrideIter::Chunks),
                    ("exact_type", SliceStrideIter::ChunksExact),
                    ("windows_type", SliceStrideIter::Windows),
                ] {
                    let ty = actual_type(name);
                    let (recognized, _) = slice_stride_iter_element_ty(tcx, ty)
                        .expect("actual authenticated std iterator");
                    assert!(recognized == kind);
                    let state = slice_stride_iter_layout(tcx, ty, kind)
                        .expect("successful actual std state layout remains admitted");
                    // Independently read the offsets from rustc's actual fields.
                    let cx = LayoutCx(tcx);
                    let outer = tcx
                        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
                        .unwrap();
                    let v = outer.field(&cx, 0);
                    let base = outer.fields.offset(0).bytes();
                    assert_eq!(state.v_data, base + v.fields.offset(0).bytes());
                    assert_eq!(state.v_len, base + v.fields.offset(1).bytes());
                    if kind == SliceStrideIter::ChunksExact {
                        let rem = outer.field(&cx, 1);
                        let base = outer.fields.offset(1).bytes();
                        assert_eq!(
                            state.rem,
                            Some((
                                base + rem.fields.offset(0).bytes(),
                                base + rem.fields.offset(1).bytes(),
                            ))
                        );
                        assert_eq!(state.size, outer.fields.offset(2).bytes());
                    } else {
                        assert!(state.rem.is_none());
                        assert_eq!(state.size, outer.fields.offset(1).bytes());
                    }
                }
                eprintln!("{MARKER}");
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
            // Discarded type-context probe only; no verified build claim.
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
        .expect("run isolated actual stride-layout consumers");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    // A child that never reached the real consumer also exits successfully.
    assert!(
        stderr.contains(MARKER),
        "consumer controls never ran: {stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}
