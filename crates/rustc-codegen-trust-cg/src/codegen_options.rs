//! The rustc codegen options this backend honours, and a named diagnostic for
//! every one it reads but does not honour (ledger L06-P7).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! Pure policy: [`OptionRequest`] is plain data the bridge extracts from the
//! rustc `Session` (`option_request` in `lib.rs`), and [`plan`] returns one
//! [`Verdict`] per option it cannot honour exactly plus whether DWARF line
//! tables are to be emitted. Nothing here touches rustc, so the table has a
//! host-independent test (`tests/codegen_option_matrix.rs`; no gate runs it
//! yet, while `tests/debuginfo_dwarf_aarch64.rs` checks the printed verdicts
//! natively in the Darwin bridge gate). The bridge
//! reports every verdict in `codegen_crate` before lowering anything: a
//! refusal is an error (the compile stops after all of them are printed), a
//! warning or note is printed and the compile continues. rustc only calls
//! `codegen_crate` when it generates code, so this plan emits no verdict for
//! `--emit=metadata` or print requests. The compiler can still reject profile
//! paths or require its profiler runtime before reaching this backend.
//!
//! The honoured lane, which no verdict names:
//!
//! * `-C lto=off` (and rustc's implicit choice of no LTO or local ThinLTO): no
//!   cross-module optimization runs, which is what those modes promise or
//!   permit. An explicit `-Z thinlto=yes` request gets the
//!   [`THINLTO_LOCAL`] note, because nothing is optimized across the crate's
//!   own codegen units either.
//! * `-C debuginfo=line-tables-only` on aarch64-apple-darwin: a DWARF 4 line
//!   table (`__debug_line`) and one subprogram DIE per function
//!   (`__debug_info`/`__debug_abbrev`/`__debug_str`) mapping emitted code to
//!   MIR source spans. `line-directives-only` and `limited` get the same
//!   image with the [`DEBUGINFO_LINES`] note saying how it differs from
//!   LLVM's (a superset for the former, no namespace or inlined-subroutine
//!   scopes for the latter; neither level carries variables or types).
//! * `-C split-debuginfo` on aarch64-apple-darwin: the DWARF lives in each
//!   object's `__DWARF` segment, so every mode is rustc's own Mach-O
//!   handling: `packed` runs dsymutil, `unpacked` keeps the objects the debug
//!   map names, and `off` leaves the debug info in the deleted objects.
//! * `-C embed-bitcode=no`, and `-C codegen-units` (rustc's partitioning
//!   decides symbol placement and internalization; the backend compiles a
//!   unit's functions into one object where it can, and into separate
//!   objects for statics, generated helpers and per-function fallbacks; on
//!   AArch64 a unit-local symbol stays hidden and unit-qualified across them,
//!   `function_linkage`).
//! * The frame-pointer policy short of `always` (Darwin's `non-leaf`: every
//!   function that calls keeps its frame record), `-C jump-tables=yes`, the
//!   small code model, and PIC/PIE relocation.
//! * `-Z min-function-alignment` up to [`guaranteed_function_alignment`]:
//!   every AArch64 function starts on a four-byte boundary.
//!
//! What this table does NOT inspect is listed, with the reason, in
//! `crates/rustc-codegen-trust-cg/README.md` ("Codegen option matrix").
#![allow(dead_code)]

/// Refusal: cross-crate (fat or thin) LTO.
pub(crate) const LTO: &str = "[TCG-OPT-LTO]";
/// Refusal: linker-plugin LTO.
pub(crate) const LINKER_PLUGIN_LTO: &str = "[TCG-OPT-LINKER-PLUGIN-LTO]";
/// Note: explicit `-Z thinlto=yes` is a no-op.
pub(crate) const THINLTO_LOCAL: &str = "[TCG-OPT-THINLTO-LOCAL]";
/// Warning: explicit `-C embed-bitcode=yes`; no bitcode exists.
pub(crate) const EMBED_BITCODE: &str = "[TCG-OPT-EMBED-BITCODE]";
/// Refusal: a debuginfo level or target this backend does not emit.
pub(crate) const DEBUGINFO: &str = "[TCG-OPT-DEBUGINFO]";
/// Note: a debuginfo level honoured with the line-table image.
pub(crate) const DEBUGINFO_LINES: &str = "[TCG-OPT-DEBUGINFO-LINES]";
/// Refusal: a DWARF version other than the one emitted.
pub(crate) const DWARF_VERSION: &str = "[TCG-OPT-DWARF-VERSION]";
/// Refusal: profile-guided instrumentation or optimization (instrumented or
/// sample-based).
pub(crate) const PGO: &str = "[TCG-OPT-PGO]";
/// Refusal: a sanitizer's instrumentation.
pub(crate) const SANITIZER: &str = "[TCG-OPT-SANITIZER]";
/// Refusal: stack-protector canaries.
pub(crate) const STACK_PROTECTOR: &str = "[TCG-OPT-STACK-PROTECTOR]";
/// Refusal: AArch64 branch protection (BTI, PAC-RET, GCS).
pub(crate) const BRANCH_PROTECTION: &str = "[TCG-OPT-BRANCH-PROTECTION]";
/// Refusal: function-entry profiling and patching hooks (mcount, XRay, a
/// patchable-function-entry NOP sled).
pub(crate) const PROFILING_HOOK: &str = "[TCG-OPT-PROFILING-HOOK]";
/// Refusal: a minimum function alignment above the one every function this
/// backend emits is guaranteed.
pub(crate) const FUNCTION_ALIGNMENT: &str = "[TCG-OPT-FUNCTION-ALIGNMENT]";
/// Refusal: a code model other than `small`.
pub(crate) const CODE_MODEL: &str = "[TCG-OPT-CODE-MODEL]";
/// Refusal: `-C jump-tables=no`.
pub(crate) const JUMP_TABLES: &str = "[TCG-OPT-JUMP-TABLES]";
/// Warning: frame pointers in every function, leaves included.
pub(crate) const FRAME_POINTERS: &str = "[TCG-OPT-FRAME-POINTERS]";
/// Warning: `-C link-dead-code` on an executable.
pub(crate) const LINK_DEAD_CODE: &str = "[TCG-OPT-LINK-DEAD-CODE]";
/// Note: a non-PIC relocation model served by PIC code on Mach-O.
pub(crate) const RELOC_MODEL: &str = "[TCG-OPT-RELOC-MODEL]";
/// Refusal: `-C instrument-coverage`.
pub(crate) const COVERAGE: &str = "[TCG-OPT-COVERAGE]";
/// Warning: an option that configures LLVM's own passes.
pub(crate) const LLVM_ONLY: &str = "[TCG-OPT-LLVM-ONLY]";

/// Every code [`plan`] can produce, in one place for documentation checks.
/// Each code is spelled with its brackets, as it is printed (and as
/// `scripts/generate_diagnostics_inventory.py` finds emission sites).
pub(crate) const ALL_CODES: &[&str] = &[
    LTO,
    LINKER_PLUGIN_LTO,
    THINLTO_LOCAL,
    EMBED_BITCODE,
    DEBUGINFO,
    DEBUGINFO_LINES,
    DWARF_VERSION,
    PGO,
    COVERAGE,
    LLVM_ONLY,
    SANITIZER,
    STACK_PROTECTOR,
    BRANCH_PROTECTION,
    PROFILING_HOOK,
    FUNCTION_ALIGNMENT,
    CODE_MODEL,
    JUMP_TABLES,
    FRAME_POINTERS,
    LINK_DEAD_CODE,
    RELOC_MODEL,
];

/// The only DWARF version the emitter writes (`trust_cg_codegen::dwarf_info`).
pub(crate) const EMITTED_DWARF_VERSION: u32 = 4;

/// The one target whose debuginfo lane is implemented and tested natively,
/// and whose objects are always position-independent.
pub(crate) const DARWIN_TARGET: &str = "aarch64-apple-darwin";

/// The function alignment, in bytes, every function this backend emits for
/// `target_triple` is guaranteed: an AArch64 instruction is four bytes and
/// four-byte aligned, so every AArch64 function starts on a four-byte
/// boundary. No other target's emission is audited for one, so nothing above
/// a byte is promised there.
pub(crate) fn guaranteed_function_alignment(target_triple: &str) -> u64 {
    if target_triple.starts_with("aarch64") {
        4
    } else {
        1
    }
}

/// rustc's `-C debuginfo` level (`rustc_session::config::DebugInfo`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DebugInfoLevel {
    None,
    LineDirectivesOnly,
    LineTablesOnly,
    Limited,
    Full,
}

impl DebugInfoLevel {
    /// The `-C debuginfo` spelling rustc documents for the level.
    pub(crate) fn spelling(self) -> &'static str {
        match self {
            DebugInfoLevel::None => "none",
            DebugInfoLevel::LineDirectivesOnly => "line-directives-only",
            DebugInfoLevel::LineTablesOnly => "line-tables-only",
            DebugInfoLevel::Limited => "limited",
            DebugInfoLevel::Full => "full",
        }
    }
}

/// The LTO mode rustc settled on (`Session::lto`), plus whether the local
/// ThinLTO choice was an explicit `-Z thinlto=yes`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LtoMode {
    No,
    ThinLocal { explicit: bool },
    Thin,
    Fat,
}

/// The codegen options the policy reads, extracted from the rustc session.
#[derive(Clone, Debug)]
pub(crate) struct OptionRequest {
    /// `--target` as rustc spells it.
    pub(crate) target_triple: String,
    /// The effective `-C debuginfo` level.
    pub(crate) debuginfo: DebugInfoLevel,
    /// The effective DWARF version (`Session::dwarf_version`).
    pub(crate) dwarf_version: u32,
    /// The effective LTO mode.
    pub(crate) lto: LtoMode,
    /// `-C linker-plugin-lto` is enabled.
    pub(crate) linker_plugin_lto: bool,
    /// `-C embed-bitcode=yes` was spelled on the command line (rustc's default
    /// is also `yes`, which no verdict names: see [`explicit_embed_bitcode`]).
    pub(crate) embed_bitcode_explicit_yes: bool,
    /// `-C profile-generate` is enabled.
    pub(crate) profile_generate: bool,
    /// `-C profile-use` names a profile.
    pub(crate) profile_use: bool,
    /// The actual sample-profile option spelling, when a profile was requested.
    pub(crate) profile_sample_use: Option<&'static str>,
    /// `-C instrument-coverage` is enabled.
    pub(crate) instrument_coverage: bool,
    /// The LLVM pass-manager options given, as `-C` spellings.
    pub(crate) llvm_only: Vec<&'static str>,
    /// `-Z sanitizer`, as rustc prints the set (empty: none).
    pub(crate) sanitizers: String,
    /// The effective `-Z stack-protector` when it is not `none`.
    pub(crate) stack_protector: Option<&'static str>,
    /// `-Z branch-protection` is set.
    pub(crate) branch_protection: bool,
    /// The function-entry profiling and patching hooks requested, as option
    /// spellings (`-Z instrument-mcount`, `-Z instrument-xray`,
    /// `-Z patchable-function-entry`).
    pub(crate) profiling_hooks: Vec<&'static str>,
    /// `-Z min-function-alignment`, in bytes, when given.
    pub(crate) min_function_alignment: Option<u64>,
    /// The effective code model when it is not `small`.
    pub(crate) code_model: Option<&'static str>,
    /// `-C jump-tables=no`.
    pub(crate) jump_tables_off: bool,
    /// The effective frame-pointer policy is `always`.
    pub(crate) frame_pointers_always: bool,
    /// `-C link-dead-code` on a crate whose every type is an executable (the
    /// bridge lowers such a crate on demand from its roots).
    pub(crate) link_dead_code_in_executable: bool,
    /// The effective relocation model when it is neither PIC nor PIE.
    pub(crate) relocation_model_not_pic: Option<&'static str>,
    /// Per-compile proof certificates are on (the default; the backend's
    /// `no-proof-certs` knob turns them off).
    pub(crate) proof_certificates: bool,
}

/// How a verdict is reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Severity {
    /// Printed; the compile continues with the stated behavior.
    Note,
    /// Printed; the option is not honoured and the compile continues.
    Warning,
    /// The compile stops before any object is written.
    Refusal,
}

/// One named diagnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Verdict {
    pub(crate) code: &'static str,
    pub(crate) severity: Severity,
    pub(crate) message: String,
}

impl Verdict {
    /// The rendered diagnostic text: `[CODE] rustc_codegen_trust_cg: message`.
    pub(crate) fn render(&self) -> String {
        format!("{} rustc_codegen_trust_cg: {}", self.code, self.message)
    }
}

/// The policy's answer for one compile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Plan {
    pub(crate) verdicts: Vec<Verdict>,
    /// Emit the DWARF line-table image (`CompilerConfig::emit_debug`) and stamp
    /// MIR source spans on the lowered trust-ir. False whenever a refusal is
    /// present.
    pub(crate) emit_debug_lines: bool,
}

impl Plan {
    pub(crate) fn refused(&self) -> bool {
        self.verdicts
            .iter()
            .any(|verdict| verdict.severity == Severity::Refusal)
    }
}

/// Decide every option in `request`. Verdicts are in a fixed order (the order
/// of the checks below), so the diagnostics a compile prints are stable.
pub(crate) fn plan(request: &OptionRequest) -> Plan {
    let mut verdicts = Vec::new();
    let mut push = |code, severity, message: String| {
        verdicts.push(Verdict {
            code,
            severity,
            message,
        })
    };

    match request.lto {
        LtoMode::No | LtoMode::ThinLocal { explicit: false } => {}
        LtoMode::ThinLocal { explicit: true } => push(
            THINLTO_LOCAL,
            Severity::Note,
            "`-Z thinlto=yes` requests local ThinLTO across this crate's codegen units; this \
             backend runs no cross-unit optimization, so the request is a no-op (each unit is \
             compiled on its own, which is what `-C lto=off` asks for)"
                .to_owned(),
        ),
        LtoMode::Thin | LtoMode::Fat => {
            let mode = if request.lto == LtoMode::Thin {
                "thin"
            } else {
                "fat"
            };
            push(
                LTO,
                Severity::Refusal,
                format!(
                    "`-C lto` ({mode}) requests cross-crate link-time optimization, which this \
                     backend does not implement (it emits no bitcode and has no whole-program \
                     pass); rustc would then link without the upstream crates it expects LTO to \
                     have merged. Refusing instead of failing the link or ignoring the request; \
                     use `-C lto=off`"
                ),
            );
        }
    }
    if request.linker_plugin_lto {
        push(
            LINKER_PLUGIN_LTO,
            Severity::Refusal,
            "`-C linker-plugin-lto` asks for LLVM bitcode objects for the linker's LTO plugin; \
             this backend emits native objects only. Refusing instead of handing the linker \
             objects its plugin cannot optimize"
                .to_owned(),
        );
    }
    if request.embed_bitcode_explicit_yes {
        push(
            EMBED_BITCODE,
            Severity::Warning,
            "`-C embed-bitcode=yes` is not honoured: this backend produces no LLVM bitcode, so \
             the objects (and any rlib) carry native code only. A downstream LTO link of them \
             fails closed (`-C lto` is refused here; LLVM reports the missing bitcode)"
                .to_owned(),
        );
    }
    let profile_options: Vec<&str> = [
        request.profile_generate.then_some("`-C profile-generate`"),
        request.profile_use.then_some("`-C profile-use`"),
        request.profile_sample_use,
    ]
    .into_iter()
    .flatten()
    .collect();
    if !profile_options.is_empty() {
        let which = profile_options.join(" and ");
        push(
            PGO,
            Severity::Refusal,
            format!(
                "{which}: profile-guided instrumentation and optimization are not implemented \
                 by this backend; refusing instead of emitting uninstrumented code or ignoring \
                 the profile"
            ),
        );
    }
    if request.instrument_coverage {
        push(
            COVERAGE,
            Severity::Refusal,
            "`-C instrument-coverage` is not implemented by this backend (no counters, no \
             `__llvm_covmap`/`__llvm_covfun` sections); refusing instead of producing a binary \
             that reports no coverage"
                .to_owned(),
        );
    }
    if !request.llvm_only.is_empty() {
        push(
            LLVM_ONLY,
            Severity::Warning,
            format!(
                "{} {} LLVM's own pass pipeline, which this backend does not run; {} not \
                 honoured",
                request
                    .llvm_only
                    .iter()
                    .map(|option| format!("`{option}`"))
                    .collect::<Vec<_>>()
                    .join(", "),
                if request.llvm_only.len() == 1 {
                    "configures"
                } else {
                    "configure"
                },
                if request.llvm_only.len() == 1 {
                    "it is"
                } else {
                    "they are"
                },
            ),
        );
    }

    if !request.sanitizers.is_empty() {
        push(
            SANITIZER,
            Severity::Refusal,
            format!(
                "`-Z sanitizer={}` asks for sanitizer instrumentation, which this backend does \
                 not emit; refusing instead of producing a binary that checks nothing",
                request.sanitizers
            ),
        );
    }
    if let Some(level) = request.stack_protector {
        push(
            STACK_PROTECTOR,
            Severity::Refusal,
            format!(
                "`-Z stack-protector={level}` asks for stack canaries, which this backend does \
                 not insert for rustc functions; refusing instead of emitting unprotected frames"
            ),
        );
    }
    if request.branch_protection {
        push(
            BRANCH_PROTECTION,
            Severity::Refusal,
            "`-Z branch-protection` asks for AArch64 BTI landing pads / PAC-RET return-address \
             signing / GCS, which this backend does not emit; refusing instead of producing \
             unprotected code"
                .to_owned(),
        );
    }
    if !request.profiling_hooks.is_empty() {
        push(
            PROFILING_HOOK,
            Severity::Refusal,
            format!(
                "{} asks for function-entry profiling or patching hooks (a profiler call, \
                 an XRay sled or a NOP sled), which this backend does not insert; refusing \
                 instead of producing a binary whose profiler sees nothing or whose runtime \
                 patcher would overwrite real instructions",
                request
                    .profiling_hooks
                    .iter()
                    .map(|option| format!("`{option}`"))
                    .collect::<Vec<_>>()
                    .join(" and ")
            ),
        );
    }
    if let Some(align) = request.min_function_alignment {
        let guaranteed = guaranteed_function_alignment(&request.target_triple);
        if align > guaranteed {
            push(
                FUNCTION_ALIGNMENT,
                Severity::Refusal,
                format!(
                    "`-Z min-function-alignment={align}` asks every function to start on a \
                     {align}-byte boundary; this backend aligns functions to {guaranteed} \
                     byte(s) on `{}` and has no option to pad them further. Refusing instead \
                     of emitting functions code may rely on being more aligned",
                    request.target_triple
                ),
            );
        }
    }
    if let Some(model) = request.code_model {
        push(
            CODE_MODEL,
            Severity::Refusal,
            format!(
                "`-C code-model={model}`: this backend emits small-code-model addressing only \
                 (ADRP/ADD pairs, +/-4 GiB); refusing instead of emitting code that may not \
                 reach its targets under the requested model"
            ),
        );
    }
    if request.jump_tables_off {
        push(
            JUMP_TABLES,
            Severity::Refusal,
            "`-C jump-tables=no`: this backend lowers dense switches through jump tables and \
             has no option to avoid them; refusing instead of emitting the indirect branches \
             the option rules out"
                .to_owned(),
        );
    }
    if request.frame_pointers_always {
        push(
            FRAME_POINTERS,
            Severity::Warning,
            "frame pointers in every function (`-C force-frame-pointers=yes` or the target's \
             `always`) are not honoured: every function that calls keeps its frame record, \
             but a frameless leaf function gets none, so a frame-pointer unwinder sees a leaf \
             through its caller's record"
                .to_owned(),
        );
    }
    if request.link_dead_code_in_executable {
        push(
            LINK_DEAD_CODE,
            Severity::Warning,
            "`-C link-dead-code` is not honoured for an executable: this backend lowers an \
             executable's functions on demand from its roots, so a function nothing reaches \
             is not emitted (a library crate lowers every function)"
                .to_owned(),
        );
    }
    if let Some(model) = request.relocation_model_not_pic {
        if request.target_triple == DARWIN_TARGET {
            push(
                RELOC_MODEL,
                Severity::Note,
                format!(
                    "`-C relocation-model={model}` is served by position-independent code: the \
                     Mach-O AArch64 objects of this backend address everything PC-relatively \
                     (ADRP/ADD, GOT loads), which is valid under every relocation model"
                ),
            );
        }
    }

    let mut emit_debug_lines = false;
    if request.debuginfo != DebugInfoLevel::None {
        let level = request.debuginfo.spelling();
        if request.target_triple != DARWIN_TARGET {
            push(
                DEBUGINFO,
                Severity::Refusal,
                format!(
                    "`-C debuginfo={level}` is not implemented for target `{}`: this backend \
                     emits DWARF only for {DARWIN_TARGET}. Refusing instead of linking code \
                     without the requested debug information; use `-C debuginfo=0`",
                    request.target_triple
                ),
            );
        } else if request.debuginfo == DebugInfoLevel::Full {
            push(
                DEBUGINFO,
                Severity::Refusal,
                "`-C debuginfo=full` (2) requests variable and type information, which this \
                 backend does not emit; it emits line tables and subprogram DIEs only. Refusing \
                 instead of silently dropping the variables and types; use \
                 `-C debuginfo=line-tables-only` (or `limited`)"
                    .to_owned(),
            );
        } else if request.proof_certificates {
            push(
                DEBUGINFO,
                Severity::Refusal,
                format!(
                    "`-C debuginfo={level}` with proof certificates on: the certified-object \
                     relocation inventory does not yet enumerate the `ARM64_RELOC_UNSIGNED` \
                     code-address relocations of the `__DWARF` sections, so every object with \
                     debug info would be refused at emission. Refusing up front; a debug build \
                     is a proofs-off build (`-Ztrust-ir-cg-args=no-proof-certs`)"
                ),
            );
        } else if request.dwarf_version != EMITTED_DWARF_VERSION {
            push(
                DWARF_VERSION,
                Severity::Refusal,
                format!(
                    "DWARF version {} was requested, but this backend emits DWARF \
                     {EMITTED_DWARF_VERSION} only; refusing instead of emitting another \
                     version than asked (use `-C dwarf-version={EMITTED_DWARF_VERSION}`)",
                    request.dwarf_version
                ),
            );
        } else {
            match request.debuginfo {
                DebugInfoLevel::LineDirectivesOnly => push(
                    DEBUGINFO_LINES,
                    Severity::Note,
                    "`-C debuginfo=line-directives-only` is honoured with the \
                     line-tables-only image: a DWARF 4 line table plus one subprogram DIE per \
                     function, a superset of line directives"
                        .to_owned(),
                ),
                DebugInfoLevel::Limited => push(
                    DEBUGINFO_LINES,
                    Severity::Note,
                    "`-C debuginfo=limited` is honoured with the line-tables-only image: a \
                     DWARF 4 line table plus one subprogram DIE per function, with no variable \
                     or type information (as `limited` specifies) and without LLVM's namespace \
                     and inlined-subroutine scopes (inlined and macro-expanded code is \
                     attributed to its call site)"
                        .to_owned(),
                ),
                _ => {}
            }
            emit_debug_lines = true;
        }
    }

    let plan = Plan {
        emit_debug_lines,
        verdicts,
    };
    if plan.refused() {
        return Plan {
            emit_debug_lines: false,
            ..plan
        };
    }
    plan
}

/// Whether the command line spells `-C embed-bitcode=yes` (or a bare
/// `-C embed-bitcode`) as its last `embed-bitcode` setting.
///
/// rustc records only the option's value, whose default is also `yes`, so the
/// request is read from the arguments themselves: `-Cname[=v]`,
/// `-C name[=v]`, `--codegen name[=v]` and `--codegen=name[=v]`, with `-`/`_`
/// interchangeable in the name as rustc accepts them, and `@path` argument
/// files expanded one argument per line as rustc's driver does. An argument
/// file that cannot be read contributes nothing (rustc itself fails on it).
pub(crate) fn explicit_embed_bitcode<I, S>(args: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let mut expanded = Vec::new();
    for arg in args {
        let arg = arg.as_ref();
        if let Some(path) = arg.strip_prefix('@') {
            if let Ok(text) = std::fs::read_to_string(path) {
                expanded.extend(text.lines().map(str::to_owned));
            }
        } else {
            expanded.push(arg.to_owned());
        }
    }
    let mut last = None;
    let mut index = 0;
    while index < expanded.len() {
        let arg = expanded[index].as_str();
        let value = if arg == "-C" || arg == "--codegen" {
            index += 1;
            expanded.get(index).map(String::as_str)
        } else if let Some(rest) = arg.strip_prefix("--codegen=") {
            Some(rest)
        } else if let Some(rest) = arg.strip_prefix("-C") {
            Some(rest)
        } else {
            None
        };
        if let Some(value) = value {
            let (name, setting) = value.split_once('=').unwrap_or((value, ""));
            if name.replace('_', "-") == "embed-bitcode" {
                last = Some(matches!(setting, "" | "y" | "yes" | "on" | "true"));
            }
        }
        index += 1;
    }
    last == Some(true)
}
