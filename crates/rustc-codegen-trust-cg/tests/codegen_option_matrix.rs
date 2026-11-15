//! The codegen option matrix (ledger L06-P7): every option the bridge reads
//! but does not honour gets exactly one named verdict, and the honoured lane
//! gets none.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! Pure policy (`src/codegen_options.rs` compiled in by path), so it runs on
//! every host. The native compiles that show the bridge printing these
//! verdicts are `debuginfo_dwarf_aarch64` and `linkage_macho_aarch64`.
#[path = "../src/codegen_options.rs"]
mod codegen_options;

use codegen_options::{
    DebugInfoLevel, LtoMode, OptionRequest, Plan, Severity, explicit_embed_bitcode, plan,
};

/// The honoured default: no option asks for anything the bridge refuses.
fn baseline() -> OptionRequest {
    OptionRequest {
        target_triple: codegen_options::DARWIN_TARGET.to_owned(),
        debuginfo: DebugInfoLevel::None,
        dwarf_version: codegen_options::EMITTED_DWARF_VERSION,
        lto: LtoMode::No,
        linker_plugin_lto: false,
        embed_bitcode_explicit_yes: false,
        profile_generate: false,
        profile_use: false,
        profile_sample_use: None,
        instrument_coverage: false,
        llvm_only: Vec::new(),
        sanitizers: String::new(),
        stack_protector: None,
        branch_protection: false,
        profiling_hooks: Vec::new(),
        min_function_alignment: None,
        code_model: None,
        jump_tables_off: false,
        frame_pointers_always: false,
        link_dead_code_in_executable: false,
        relocation_model_not_pic: None,
        proof_certificates: true,
    }
}

/// The one verdict of `plan`, by code and severity.
fn only(plan: &Plan) -> (&'static str, Severity) {
    assert_eq!(plan.verdicts.len(), 1, "{plan:#?}");
    (plan.verdicts[0].code, plan.verdicts[0].severity)
}

#[test]
fn the_honoured_lane_prints_nothing() {
    let quiet = plan(&baseline());
    assert!(quiet.verdicts.is_empty(), "{quiet:#?}");
    assert!(!quiet.emit_debug_lines);
    // rustc's own implicit choice of local ThinLTO is the same no-op.
    let implicit = plan(&OptionRequest {
        lto: LtoMode::ThinLocal { explicit: false },
        ..baseline()
    });
    assert!(implicit.verdicts.is_empty(), "{implicit:#?}");
}

#[test]
fn every_lto_mode_is_honoured_noted_or_refused_by_name() {
    let local = plan(&OptionRequest {
        lto: LtoMode::ThinLocal { explicit: true },
        ..baseline()
    });
    assert_eq!(
        only(&local),
        (codegen_options::THINLTO_LOCAL, Severity::Note)
    );
    assert!(!local.refused());
    for (mode, spelling) in [(LtoMode::Thin, "(thin)"), (LtoMode::Fat, "(fat)")] {
        let refused = plan(&OptionRequest {
            lto: mode,
            ..baseline()
        });
        assert_eq!(only(&refused), (codegen_options::LTO, Severity::Refusal));
        assert!(refused.refused());
        assert!(refused.verdicts[0].message.contains(spelling));
        assert!(
            refused.verdicts[0]
                .render()
                .starts_with("[TCG-OPT-LTO] rustc_codegen_trust_cg: ")
        );
    }
    let plugin = plan(&OptionRequest {
        linker_plugin_lto: true,
        ..baseline()
    });
    assert_eq!(
        only(&plugin),
        (codegen_options::LINKER_PLUGIN_LTO, Severity::Refusal)
    );
}

#[test]
fn profiling_and_coverage_instrumentation_are_refused_by_name() {
    for (generate, profile_use, profile_sample_use, needle) in [
        (true, false, false, "`-C profile-generate`:"),
        (false, true, false, "`-C profile-use`:"),
        (
            true,
            true,
            false,
            "`-C profile-generate` and `-C profile-use`:",
        ),
        // Sample-based PGO is the same class: refused, never ignored.
        (false, false, true, "`-Z profile-sample-use`:"),
        (
            false,
            true,
            true,
            "`-C profile-use` and `-Z profile-sample-use`:",
        ),
    ] {
        let refused = plan(&OptionRequest {
            profile_generate: generate,
            profile_use,
            profile_sample_use: profile_sample_use.then_some("`-Z profile-sample-use`"),
            ..baseline()
        });
        assert_eq!(only(&refused), (codegen_options::PGO, Severity::Refusal));
        assert!(
            refused.verdicts[0].message.starts_with(needle),
            "{refused:#?}"
        );
    }
    for spelling in ["`-Z profile-sample-use`", "`-C profile-sample-use`"] {
        let refused = plan(&OptionRequest {
            profile_sample_use: Some(spelling),
            ..baseline()
        });
        assert_eq!(only(&refused), (codegen_options::PGO, Severity::Refusal));
        assert!(
            refused.verdicts[0]
                .message
                .starts_with(&format!("{spelling}:"))
        );
    }
    let coverage = plan(&OptionRequest {
        instrument_coverage: true,
        ..baseline()
    });
    assert_eq!(
        only(&coverage),
        (codegen_options::COVERAGE, Severity::Refusal)
    );
}

#[test]
fn hardening_and_profiling_instrumentation_is_refused_by_name() {
    let rows: [(OptionRequest, &str, &str); 8] = [
        (
            OptionRequest {
                sanitizers: "address".to_owned(),
                ..baseline()
            },
            codegen_options::SANITIZER,
            "`-Z sanitizer=address`",
        ),
        (
            OptionRequest {
                stack_protector: Some("all"),
                ..baseline()
            },
            codegen_options::STACK_PROTECTOR,
            "`-Z stack-protector=all`",
        ),
        (
            OptionRequest {
                branch_protection: true,
                ..baseline()
            },
            codegen_options::BRANCH_PROTECTION,
            "`-Z branch-protection`",
        ),
        (
            OptionRequest {
                profiling_hooks: vec!["-Z instrument-mcount", "-Z instrument-xray"],
                ..baseline()
            },
            codegen_options::PROFILING_HOOK,
            "`-Z instrument-mcount` and `-Z instrument-xray`",
        ),
        // A NOP sled a runtime patcher overwrites: without it the patcher
        // would overwrite the function's real first instructions.
        (
            OptionRequest {
                profiling_hooks: vec!["-Z patchable-function-entry"],
                ..baseline()
            },
            codegen_options::PROFILING_HOOK,
            "`-Z patchable-function-entry`",
        ),
        (
            OptionRequest {
                min_function_alignment: Some(64),
                ..baseline()
            },
            codegen_options::FUNCTION_ALIGNMENT,
            "`-Z min-function-alignment=64`",
        ),
        (
            OptionRequest {
                code_model: Some("large"),
                ..baseline()
            },
            codegen_options::CODE_MODEL,
            "`-C code-model=large`",
        ),
        (
            OptionRequest {
                jump_tables_off: true,
                ..baseline()
            },
            codegen_options::JUMP_TABLES,
            "`-C jump-tables=no`",
        ),
    ];
    for (request, code, spelling) in rows {
        let refused = plan(&request);
        assert_eq!(only(&refused), (code, Severity::Refusal));
        assert!(
            refused.verdicts[0].message.contains(spelling),
            "{refused:#?}"
        );
    }
}

#[test]
fn a_minimum_function_alignment_is_honoured_only_up_to_the_guaranteed_one() {
    // Every AArch64 function starts on a four-byte boundary.
    for align in [1, 2, 4] {
        let honoured = plan(&OptionRequest {
            min_function_alignment: Some(align),
            ..baseline()
        });
        assert!(honoured.verdicts.is_empty(), "{align}: {honoured:#?}");
    }
    let refused = plan(&OptionRequest {
        min_function_alignment: Some(8),
        ..baseline()
    });
    assert_eq!(
        only(&refused),
        (codegen_options::FUNCTION_ALIGNMENT, Severity::Refusal)
    );
    // No other target's emission is audited for an alignment above a byte.
    let other = plan(&OptionRequest {
        target_triple: "x86_64-apple-darwin".to_owned(),
        min_function_alignment: Some(2),
        ..baseline()
    });
    assert_eq!(
        only(&other),
        (codegen_options::FUNCTION_ALIGNMENT, Severity::Refusal)
    );
}

#[test]
fn frame_pointers_dead_code_and_relocation_models_are_warned_or_noted() {
    let frames = plan(&OptionRequest {
        frame_pointers_always: true,
        ..baseline()
    });
    assert_eq!(
        only(&frames),
        (codegen_options::FRAME_POINTERS, Severity::Warning)
    );
    let dead = plan(&OptionRequest {
        link_dead_code_in_executable: true,
        ..baseline()
    });
    assert_eq!(
        only(&dead),
        (codegen_options::LINK_DEAD_CODE, Severity::Warning)
    );
    let static_model = plan(&OptionRequest {
        relocation_model_not_pic: Some("static"),
        ..baseline()
    });
    assert_eq!(
        only(&static_model),
        (codegen_options::RELOC_MODEL, Severity::Note)
    );
    assert!(
        static_model.verdicts[0]
            .message
            .contains("`-C relocation-model=static`")
    );
    // Off Darwin the relocation model is the target route's own business.
    let elsewhere = plan(&OptionRequest {
        target_triple: "aarch64-unknown-linux-gnu".to_owned(),
        relocation_model_not_pic: Some("static"),
        ..baseline()
    });
    assert!(elsewhere.verdicts.is_empty(), "{elsewhere:#?}");
}

#[test]
fn bitcode_and_llvm_pass_options_are_warned_not_dropped() {
    let bitcode = plan(&OptionRequest {
        embed_bitcode_explicit_yes: true,
        ..baseline()
    });
    assert_eq!(
        only(&bitcode),
        (codegen_options::EMBED_BITCODE, Severity::Warning)
    );
    assert!(!bitcode.refused());
    let one = plan(&OptionRequest {
        llvm_only: vec!["-C llvm-args"],
        ..baseline()
    });
    assert_eq!(only(&one), (codegen_options::LLVM_ONLY, Severity::Warning));
    assert!(
        one.verdicts[0]
            .message
            .contains("`-C llvm-args` configures")
    );
    assert!(one.verdicts[0].message.contains("it is not honoured"));
    let two = plan(&OptionRequest {
        llvm_only: vec!["-C passes", "-C remark"],
        ..baseline()
    });
    assert!(
        two.verdicts[0]
            .message
            .contains("`-C passes`, `-C remark` configure")
    );
    assert!(two.verdicts[0].message.contains("they are not honoured"));
}

#[test]
fn debuginfo_levels_are_emitted_noted_or_refused_by_name() {
    let proofs_off = |debuginfo| OptionRequest {
        debuginfo,
        proof_certificates: false,
        ..baseline()
    };
    let lines = plan(&proofs_off(DebugInfoLevel::LineTablesOnly));
    assert!(lines.verdicts.is_empty(), "{lines:#?}");
    assert!(lines.emit_debug_lines);
    for level in [DebugInfoLevel::LineDirectivesOnly, DebugInfoLevel::Limited] {
        let noted = plan(&proofs_off(level));
        assert_eq!(
            only(&noted),
            (codegen_options::DEBUGINFO_LINES, Severity::Note)
        );
        assert!(noted.emit_debug_lines);
        assert!(noted.verdicts[0].message.contains(level.spelling()));
    }
    let full = plan(&proofs_off(DebugInfoLevel::Full));
    assert_eq!(only(&full), (codegen_options::DEBUGINFO, Severity::Refusal));
    assert!(
        full.verdicts[0]
            .message
            .contains("variable and type information")
    );
    assert!(!full.emit_debug_lines);
}

#[test]
fn debuginfo_outside_the_implemented_lane_is_refused_before_emission() {
    // Proof certificates on: the certified-object relocation inventory refuses
    // every object with DWARF sections, so the request is refused up front.
    let certified = plan(&OptionRequest {
        debuginfo: DebugInfoLevel::LineTablesOnly,
        ..baseline()
    });
    assert_eq!(
        only(&certified),
        (codegen_options::DEBUGINFO, Severity::Refusal)
    );
    assert!(certified.verdicts[0].message.contains("no-proof-certs"));
    assert!(!certified.emit_debug_lines);
    // Another target: no DWARF lane is implemented there.
    let elsewhere = plan(&OptionRequest {
        target_triple: "x86_64-unknown-linux-gnu".to_owned(),
        debuginfo: DebugInfoLevel::LineTablesOnly,
        proof_certificates: false,
        ..baseline()
    });
    assert_eq!(
        only(&elsewhere),
        (codegen_options::DEBUGINFO, Severity::Refusal)
    );
    assert!(
        elsewhere.verdicts[0]
            .message
            .contains("x86_64-unknown-linux-gnu")
    );
    // Another DWARF version than the emitted one.
    let version = plan(&OptionRequest {
        debuginfo: DebugInfoLevel::LineTablesOnly,
        dwarf_version: 5,
        proof_certificates: false,
        ..baseline()
    });
    assert_eq!(
        only(&version),
        (codegen_options::DWARF_VERSION, Severity::Refusal)
    );
    assert!(!version.emit_debug_lines);
    // A DWARF version request without debug info asks for nothing.
    let unused = plan(&OptionRequest {
        dwarf_version: 5,
        ..baseline()
    });
    assert!(unused.verdicts.is_empty());
}

#[test]
fn every_refusal_is_printed_and_turns_debug_lines_off() {
    let many = plan(&OptionRequest {
        lto: LtoMode::Fat,
        embed_bitcode_explicit_yes: true,
        profile_generate: true,
        instrument_coverage: true,
        llvm_only: vec!["-C llvm-args"],
        debuginfo: DebugInfoLevel::LineTablesOnly,
        proof_certificates: false,
        ..baseline()
    });
    let codes: Vec<_> = many.verdicts.iter().map(|verdict| verdict.code).collect();
    assert_eq!(
        codes,
        [
            codegen_options::LTO,
            codegen_options::EMBED_BITCODE,
            codegen_options::PGO,
            codegen_options::COVERAGE,
            codegen_options::LLVM_ONLY,
        ]
    );
    assert!(many.refused());
    assert!(!many.emit_debug_lines);
    // Every code a verdict can carry is listed once, and spelled as a TCG code.
    let mut all = codegen_options::ALL_CODES.to_vec();
    all.sort_unstable();
    all.dedup();
    assert_eq!(all.len(), codegen_options::ALL_CODES.len());
    assert!(
        all.iter()
            .all(|code| code.starts_with("[TCG-OPT-") && code.ends_with(']'))
    );
}

#[test]
fn explicit_embed_bitcode_reads_every_spelling_and_the_last_one_wins() {
    for args in [
        &["-Cembed-bitcode=yes"][..],
        &["-C", "embed-bitcode"],
        &["--codegen", "embed_bitcode=on"],
        &["--codegen=embed-bitcode=y"],
        &["-Cembed-bitcode=no", "-Cembed-bitcode=true"],
    ] {
        assert!(explicit_embed_bitcode(args), "{args:?}");
    }
    for args in [
        &[][..],
        &["-Cembed-bitcode=no"],
        &["-Cembed-bitcode=yes", "-C", "embed-bitcode=off"],
        &["-Copt-level=3", "embed-bitcode=yes"],
        &["-C"],
    ] {
        assert!(!explicit_embed_bitcode(args), "{args:?}");
    }
}

#[test]
fn explicit_embed_bitcode_expands_argument_files() {
    let dir = TempDir::new("argfile");
    let file = dir.0.join("args");
    std::fs::write(&file, "--crate-type\nlib\n-C\nembed-bitcode=yes\n").expect("write argfile");
    let at = format!("@{}", file.display());
    assert!(explicit_embed_bitcode([at.as_str()]));
    assert!(!explicit_embed_bitcode([at.as_str(), "-Cembed-bitcode=no"]));
    // An unreadable argument file contributes nothing (rustc refuses it).
    assert!(!explicit_embed_bitcode(["@/nonexistent/trust-cg-argfile"]));
}

/// A scratch directory removed when dropped.
struct TempDir(std::path::PathBuf);

impl TempDir {
    fn new(stem: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "tcg_codegen_option_matrix_{stem}_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("create scratch directory");
        Self(path)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
