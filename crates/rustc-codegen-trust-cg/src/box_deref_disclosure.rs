// rustc_codegen_trust_cg/box_deref_disclosure.rs - the Box deref opt-in and its report
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

//! The one place this lane opts into trust-cg's named-premise floor for
//! `Inst::BoxDeref`, and the report that opt-in owes.
//!
//! Default: no report exists, the license keeps the floor `Refuse`, and every
//! module holding an `Inst::BoxDeref` is refused by the shared acceptance
//! check (`trust_cg_lower::admit_box_derefs`). With
//! `-Ztrust-ir-cg-args=box-deref-named-premise` the lane's license is built
//! with `CodegenLicensePolicy::with_named_premise_box_floor`, whose report
//! this module owns and prints on stderr when the crate's codegen is joined:
//!
//! - one `[TCG-BOX-DEREF-FACT]` line per lowered function that carries a
//!   fact (what the compiler admitted and the bridge emitted), and
//! - one `[TCG-BOX-DEREF-ASSUMED]` line per module the license admitted,
//!   accurately labeled as an admission under named assumptions. The line
//!   does not claim a later lowering or object-emission step succeeded.
//!
//! Neither line is evidence. An object compiled this way rests on an
//! assumption nothing in this backend establishes.

use std::sync::{Mutex, OnceLock};

use trust_cg_lower::BoxDerefDisclosure;

static REPORT: OnceLock<Option<BoxDerefDisclosure>> = OnceLock::new();
static EMITTED: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// The report of this process's opt-in, or `None` when the knob is not set:
/// then nothing can select the named-premise floor.
pub(crate) fn report() -> Option<&'static BoxDerefDisclosure> {
    REPORT
        .get_or_init(|| {
            crate::knobs::is_enabled(crate::knobs::BOX_DEREF_NAMED_PREMISE)
                .then(BoxDerefDisclosure::new)
        })
        .as_ref()
}

/// Record what one lowered function carries. Kept only under the opt-in:
/// without it the module is refused and its own refusal is the report.
pub(crate) fn note_emitted(symbol: &str, plan: &crate::box_deref_facts::BoxDerefPlan) {
    if report().is_none() {
        return;
    }
    let lines = plan.admitted_lines();
    if lines.is_empty() {
        return;
    }
    let mut emitted = EMITTED
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    for line in lines {
        let line = format!("[TCG-BOX-DEREF-FACT] `{symbol}`: {line}");
        // A function can be lowered more than once (a retry); report it once.
        if !emitted.contains(&line) {
            emitted.push(line);
        }
    }
}

/// Print the report. Called once, when the crate's codegen is joined, whether
/// or not every module compiled.
pub(crate) fn print() {
    let Some(report) = report() else {
        return;
    };
    let emitted = std::mem::take(
        &mut *EMITTED
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
    );
    for line in emitted {
        eprintln!("{line}");
    }
    for line in report.lines() {
        eprintln!("[TCG-BOX-DEREF-ASSUMED] {line}");
    }
}
