//! CMPXCHG16B (CPUID.01H:ECX.CX16) on an x86-64 target: the two answers the
//! bridge needs from rustc's target-feature strings, as pure functions so each
//! rule is unit-tested against the flag grammar of the pinned rustc and LLVM.
//!
//! * The test-only `cfg_has_cmpxchg16b` reference models what LLVM reports as
//!   `cfg(target_feature = "cmpxchg16b")`. Production session declarations use
//!   the complete compiler catalog in `target_configuration`; the historical
//!   reference and its discriminating flag/alias tests remain here.
//! * [`cx16_disabling_entry`]: the fail-closed half of the CMPXCHG16B admission
//!   gate. It names a `-feature` entry (target spec or `-C target-feature`)
//!   that removes CX16 from LLVM's effective feature set, or that the bridge
//!   cannot rule out as doing so.
//!
//! The two answer different questions and are deliberately NOT the same
//! function: rustc computes the cfg from its own feature names, while the
//! code LLVM would generate depends on LLVM's names and implications. Measured
//! with the stage-1 `trustc` (LLVM backend) on `x86_64-apple-darwin`:
//! `-C target-feature=-cx8` leaves `cmpxchg16b` in the cfg (rustc does not know
//! `cx8`) but LLVM lowers `AtomicU128::load` to the `__atomic_load_16` libcall,
//! because LLVM's `FeatureCX16` implies `FeatureCX8` (X86.td) and disabling a
//! feature disables every feature that implies it.
//!
//! How the pinned compiler handles the strings (rustc_codegen_ssa
//! `target_features.rs`, rustc_codegen_llvm `llvm_util.rs`):
//!
//! * Entries are split on `,` and NOT trimmed. An entry must begin with `+` or
//!   `-`: in `-C target-feature` anything else is warned about and ignored; in
//!   a target spec it is an error, as is one feature named with both signs.
//! * `+X` enables rustc's implied closure of `X`; `-X` disables every rustc
//!   feature that (transitively) implies `X`. An unknown name is its own
//!   closure. `crt-static` (`RUSTC_SPECIFIC_FEATURES`) is not a target feature
//!   and never reaches LLVM.
//! * The cfg: LLVM's BASE target machine (the CPU's features, then the spec's
//!   entries translated to LLVM names, in order) decides which rustc features
//!   start enabled; then the `-C target-feature` entries are applied in order,
//!   by rustc's rules, to rustc names only. A name rustc does not know (an LLVM
//!   spelling such as `cx16`, or a name with stray whitespace) changes nothing.
//! * Code generation: the spec's and then the `-C target-feature` entries are
//!   passed to LLVM in order, rustc names translated (`cmpxchg16b` -> `cx16`)
//!   and unknown names VERBATIM. LLVM applies them in order; enabling `cx16`
//!   also enables `cx8`, and disabling `cx16` or `cx8` disables `cx16`.

/// What the rules need from rustc's feature table for this target.
pub(crate) trait RustFeatureTable {
    /// Whether enabling rustc feature `feature` enables `cmpxchg16b`
    /// (`cmpxchg16b` is in `implied_target_features(feature)`).
    #[cfg(test)]
    fn enabling_implies_cmpxchg16b(&self, feature: &str) -> bool;
    /// Whether disabling `feature` disables `cmpxchg16b` (`feature` is in
    /// `implied_target_features("cmpxchg16b")`: rustc disables every feature
    /// implying a disabled one).
    fn disabling_disables_cmpxchg16b(&self, feature: &str) -> bool;
    /// Whether rustc recognizes `feature` for this target: a target feature of
    /// its table, or a rustc-specific one that never reaches LLVM.
    fn is_known(&self, feature: &str) -> bool;
}

/// The LLVM names whose disabling removes CX16: `cx16` itself and everything
/// `FeatureCX16` implies (only `FeatureCX8`, X86.td). Neither is a rustc name,
/// so rustc passes them to LLVM verbatim.
const LLVM_NAMES_WHOSE_DISABLE_REMOVES_CX16: [&str; 2] = ["cx16", "cx8"];

/// Whether the LLVM backend reports `target_feature = "cmpxchg16b"`.
///
/// `cpu_has_cx16` is LLVM's answer for the effective CPU alone (its processor
/// table, or the host's CPUID for `native`). `spec_features` is the target
/// spec's `features`, `cg_features` the `-C target-feature` string.
///
/// The spec's entries move LLVM's base target machine, so they are applied
/// with LLVM's names and implications; the `-C target-feature` entries move
/// only the cfg computation, so they are applied with rustc's. An LLVM alias
/// on the command line (`-cx16`, `-cx8`) therefore leaves the cfg set, as it
/// does under LLVM.
#[cfg(test)]
pub(crate) fn cfg_has_cmpxchg16b(
    cpu_has_cx16: bool,
    spec_features: &str,
    cg_features: &str,
    table: &impl RustFeatureTable,
) -> bool {
    let mut has = cpu_has_cx16;
    for entry in spec_features.split(',') {
        if let Some(name) = entry.strip_prefix('+') {
            if table.enabling_implies_cmpxchg16b(name) || name == "cx16" {
                has = true;
            }
        } else if let Some(name) = entry.strip_prefix('-') {
            if table.disabling_disables_cmpxchg16b(name)
                || LLVM_NAMES_WHOSE_DISABLE_REMOVES_CX16.contains(&name)
            {
                has = false;
            }
        }
    }
    for entry in cg_features.split(',') {
        if let Some(name) = entry.strip_prefix('+') {
            if table.enabling_implies_cmpxchg16b(name) {
                has = true;
            }
        } else if let Some(name) = entry.strip_prefix('-') {
            if table.disabling_disables_cmpxchg16b(name) {
                has = false;
            }
        }
    }
    has
}

/// The first `-feature` entry, in the target spec's `features` or in
/// `-C target-feature`, that removes CX16 from what LLVM would compile for,
/// or that the bridge cannot rule out as doing so; `None` when there is none.
///
/// Refused, per entry:
/// * a rustc feature whose disabling disables `cmpxchg16b` (rustc's own
///   closure; with the pinned table only `cmpxchg16b`);
/// * `cx16` or `cx8`: LLVM names, reaching LLVM verbatim, whose disabling
///   removes CX16 (`FeatureCX16` implies `FeatureCX8`);
/// * any other name rustc does not recognize: it too reaches LLVM verbatim,
///   and the bridge has no table of LLVM's implications to rule it out.
///
/// Deliberately conservative, since this half of the gate can only make it
/// refuse: order is ignored (a later `+cmpxchg16b` does not undo a
/// `-cmpxchg16b`), and entries are trimmed (rustc ignores ` -cx8` and LLVM
/// ignores `-cx8 `; both are refused here). A disabled rustc feature that does
/// not imply `cmpxchg16b` is admitted: rustc translates it to an LLVM name,
/// and in the pinned compiler no rustc name other than `cmpxchg16b`
/// translates to `cx16` or `cx8`.
pub(crate) fn cx16_disabling_entry(
    spec_features: &str,
    cg_features: &str,
    table: &impl RustFeatureTable,
) -> Option<String> {
    let lists = [
        ("the target spec's features", spec_features),
        ("`-C target-feature`", cg_features),
    ];
    for (source, list) in lists {
        for entry in list.split(',') {
            let Some(name) = entry.trim().strip_prefix('-') else {
                continue;
            };
            if table.disabling_disables_cmpxchg16b(name) {
                return Some(format!("{source} disables CMPXCHG16B (`-{name}`)"));
            }
            if LLVM_NAMES_WHOSE_DISABLE_REMOVES_CX16.contains(&name) {
                return Some(format!(
                    "{source} passes `-{name}` to LLVM, which removes CX16 (LLVM's `cx16` \
                     implies `cx8`, and disabling a feature disables every feature implying it)"
                ));
            }
            if !table.is_known(name) {
                return Some(format!(
                    "{source} disables `{name}`, which is not a rustc target feature: rustc \
                     passes it to LLVM verbatim, and the bridge cannot rule out that LLVM's \
                     implications remove CX16 with it"
                ));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pinned rustc's x86 table as the rules see it: `cmpxchg16b` implies
    /// nothing and nothing implies it (`("cmpxchg16b", Stable, &[])`, and no
    /// implied list names it), plus the known names these tests use.
    struct PinnedX86;
    impl RustFeatureTable for PinnedX86 {
        fn enabling_implies_cmpxchg16b(&self, feature: &str) -> bool {
            feature == "cmpxchg16b"
        }
        fn disabling_disables_cmpxchg16b(&self, feature: &str) -> bool {
            feature == "cmpxchg16b"
        }
        fn is_known(&self, feature: &str) -> bool {
            [
                "cmpxchg16b",
                "sse3",
                "lahfsahf",
                "popcnt",
                "rdrand",
                "aes",
                "pclmulqdq",
                "rtm",
                "fsgsbase",
                "avx2",
                "crt-static",
            ]
            .contains(&feature)
        }
    }

    /// A table in which `wide` implies `cmpxchg16b` and `cmpxchg16b` implies
    /// `narrow`: rustc's closure rules then move the cfg through them.
    struct Synthetic;
    impl RustFeatureTable for Synthetic {
        fn enabling_implies_cmpxchg16b(&self, feature: &str) -> bool {
            matches!(feature, "cmpxchg16b" | "wide")
        }
        fn disabling_disables_cmpxchg16b(&self, feature: &str) -> bool {
            matches!(feature, "cmpxchg16b" | "narrow")
        }
        fn is_known(&self, feature: &str) -> bool {
            matches!(feature, "cmpxchg16b" | "wide" | "narrow")
        }
    }

    /// Every row was measured with the stage-1 `trustc` (LLVM backend):
    /// `--print cfg` for the target-spec rows (custom `x86_64-apple-darwin`
    /// JSON specs), and for the `-C target-feature` rows `--print cfg` plus the
    /// `cfg_cx16_cpu_override.rs` fixture (exit 61 = cfg set, 62 = not).
    #[test]
    fn cfg_matches_the_llvm_backend() {
        let rows: &[(bool, &str, &str, bool)] = &[
            // x86_64-apple-darwin as shipped: penryn, no spec features.
            (true, "", "", true),
            (true, "", "-cmpxchg16b", false),
            // LLVM spellings on the command line do not move rustc's cfg
            // (they move LLVM's code generation; see the gate).
            (true, "", "-cx16", true),
            (true, "", "-cx8", true),
            (true, "", "+cmpxchg16b,-cx8", true),
            // No trimming: ` -cmpxchg16b` does not start with `-` (warned and
            // ignored) and `cmpxchg16b ` is an unknown feature.
            (true, "", "+sse3, -cmpxchg16b", true),
            (false, "", "+cmpxchg16b ", false),
            (false, "", "+cmpxchg16b", true),
            (false, "", "+cx16", false),
            // In order, last one wins.
            (true, "", "-cmpxchg16b,+cmpxchg16b", true),
            (false, "", "+cmpxchg16b,-cmpxchg16b", false),
            (true, "", "+sse3,-cmpxchg16b", false),
            // Target spec entries: LLVM names and implications.
            (true, "-cmpxchg16b", "", false),
            (true, "-cx16", "", false),
            (true, "-cx8", "", false),
            (true, "+cmpxchg16b,-cx8", "", false),
            (true, "-cx8,+cx16", "", true),
            (true, "-cx8,+cmpxchg16b", "", true),
            (true, "-cx16,+cmpxchg16b", "", true),
            (true, "-cmpxchg16b,+cx16", "", true),
            (false, "+cx16", "", true),
            (false, "+cmpxchg16b", "", true),
            (false, "+cx8", "", false),
            // x86_64h-apple-darwin's own spec, and Windows'.
            (true, "-rdrand,-aes,-pclmulqdq,-rtm,-fsgsbase", "", true),
            (false, "+cmpxchg16b,+sse3,+lahfsahf", "", true),
            (false, "+cmpxchg16b,+sse3,+lahfsahf", "-cmpxchg16b", false),
            // A spec that removes CX16 and a command line that restores it.
            (true, "-cmpxchg16b", "+cmpxchg16b", true),
        ];
        for &(cpu, spec, cg, want) in rows {
            assert_eq!(
                cfg_has_cmpxchg16b(cpu, spec, cg, &PinnedX86),
                want,
                "cpu_has_cx16={cpu} spec={spec:?} -C target-feature={cg:?}"
            );
        }
    }

    #[test]
    fn cfg_follows_rustc_closures_on_the_command_line() {
        assert!(cfg_has_cmpxchg16b(false, "", "+wide", &Synthetic));
        assert!(!cfg_has_cmpxchg16b(true, "", "-narrow", &Synthetic));
        assert!(!cfg_has_cmpxchg16b(false, "+wide,-narrow", "", &Synthetic));
        // Enabling what cmpxchg16b implies does not enable it.
        assert!(!cfg_has_cmpxchg16b(false, "", "+narrow", &Synthetic));
    }

    #[test]
    fn gate_refuses_every_entry_that_removes_cx16() {
        let refused: &[(&str, &str)] = &[
            ("", "-cmpxchg16b"),
            ("", "-cx16"),
            // Measured: LLVM compiles `AtomicU128::load` to `__atomic_load_16`
            // under these (FeatureCX16 implies FeatureCX8).
            ("", "-cx8"),
            ("", "+cmpxchg16b,-cx8"),
            // Order is not modeled: refused even though the last entry enables.
            ("", "-cx8,+cmpxchg16b"),
            // Trimmed: refused although rustc (leading) or LLVM (trailing)
            // would ignore the entry.
            ("", " -cx8"),
            ("", "-cx8 "),
            // A name rustc does not know reaches LLVM verbatim.
            ("", "-sahf"),
            ("", "-not-a-feature"),
            // The same, in the target spec.
            ("-cmpxchg16b", ""),
            ("-cx16", ""),
            ("-cx8", ""),
            ("+cmpxchg16b,-cx8", ""),
            ("-not-a-feature", ""),
        ];
        for &(spec, cg) in refused {
            assert!(
                cx16_disabling_entry(spec, cg, &PinnedX86).is_some(),
                "spec={spec:?} -C target-feature={cg:?} must be refused"
            );
        }
        let reason = cx16_disabling_entry("", "-cx8", &PinnedX86).expect("refused");
        assert!(reason.contains("`-cx8`"), "{reason}");
        let reason = cx16_disabling_entry("-cmpxchg16b", "", &PinnedX86).expect("refused");
        assert!(reason.contains("target spec"), "{reason}");
        assert!(cx16_disabling_entry("", "-narrow", &Synthetic).is_some());
    }

    #[test]
    fn gate_admits_what_leaves_cx16_alone() {
        let admitted: &[(&str, &str)] = &[
            ("", ""),
            ("", "+cmpxchg16b"),
            ("", "+cx16"),
            ("", "-avx2"),
            ("", "+sse3,-popcnt"),
            ("", "-crt-static"),
            // x86_64h-apple-darwin and Windows as shipped.
            ("-rdrand,-aes,-pclmulqdq,-rtm,-fsgsbase", ""),
            ("+cmpxchg16b,+sse3,+lahfsahf", ""),
        ];
        for &(spec, cg) in admitted {
            assert_eq!(
                cx16_disabling_entry(spec, cg, &PinnedX86),
                None,
                "spec={spec:?} -C target-feature={cg:?}"
            );
        }
    }
}
