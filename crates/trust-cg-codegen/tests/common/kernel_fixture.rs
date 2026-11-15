#![allow(dead_code)]
// Copyright 2026 Andrew Yates | Apache-2.0
//! Host-target loading for the frozen Clean-kernel fixtures (`clean_*.tir`,
//! `clean_*.trust.tir`, upstream's `fixtures/ae9-linux/*.tir`, and the inline
//! `*_TRUST_IR` snapshots).
//!
//! Every fixture declares the machine it was emitted for in its module header:
//! `target "aarch64-apple-darwin" 8 little` for the Darwin stage1
//! `trust_ir_mir` corpus, `target "aarch64-unknown-linux-gnu" 8 little` for
//! upstream's ae9 Linux corpus. This module rewrites that ONE line to the
//! host's triple when it differs, and does nothing else.
//!
//! WHAT THE REWRITE IS AND IS NOT FOR. Measured on this checkout
//! (2026-09-27, `x86_64-unknown-linux-gnu`, stock rustc 1.97.1): the rewrite
//! is NOT what lets a Darwin-AArch64 fixture compile here.
//!
//! * `CompileError::JitTargetMismatch` compares `CompilerConfig::target` with
//!   the host process (`Compiler::ensure_host_jit_target`); it never reads the
//!   module header. What makes these lanes run on x86-64 is
//!   [`host_jit_target`] in the consumer's `CompilerConfig`, plus the
//!   `target_arch` cfg gate on the consumer itself.
//! * `trust-cg-lower`'s `target_info_surface_floor` states the lowering
//!   contract outright (`crates/trust-cg-lower/src/adapter.rs`): `triple` and
//!   `abi` are "NOT A LOWERING INPUT: the lowered architecture is the entry's
//!   `GuardCarrierArch`, not the module's claim". It refuses only a
//!   `pointer_size` that contradicts the architecture, a big-endian module,
//!   and an `AlwaysMemory`/unsafely-`Unclassified` struct-passing policy.
//!   All 38 Darwin fixtures declare `8 little` and no `structpass=` trailer,
//!   so none of those refusals fires on x86-64 either way.
//! * The triple IS checked exactly by one entry: `core_admission`'s
//!   `check_module` (`CoreTargetContractError::TrustIrTripleMismatch`). The
//!   rewrite is what keeps a fixture admissible there, and it keeps the
//!   module's declared identity — which `trust_ir::TargetInfo` documents as
//!   flowing into `Module::stable_digest` — equal to the machine it is
//!   actually compiled for. A lane that compiled a module still claiming
//!   `aarch64-apple-darwin` into x86-64 machine code would be recording a
//!   machine identity it did not use.
//!
//! EVIDENCE THAT THE `target` LINE IS THE ONLY HOST-DEPENDENT TEXT. Measured
//! 2026-09-27, reproducible from `crates/trust-cg-codegen/tests`:
//!
//! * `ls clean_*.tir | wc -l` is 38, and each has exactly one `target "`
//!   token: `for f in clean_*.tir; do grep -c 'target "' $f; done` reports
//!   `1` for all 38, every occurrence at column zero (line 3, after the
//!   format comment and `module` line).
//! * `grep -h '^target ' clean_*.tir | sort -u` yields the single line
//!   `target "aarch64-apple-darwin" 8 little`.
//! * No other architecture, vendor, operating-system or target-intrinsic
//!   token occurs anywhere in the corpus: a case-insensitive
//!   `grep -icE 'aarch64|arm64|apple|darwin|macos|x86|amd64|sysv|aapcs|neon|sse|avx|asm|llvm\.|intrinsic'`
//!   over `clean_*.tir` sums to exactly 38 matches — one per fixture, each
//!   being that header line. `grep -E 'abi=|structpass=' clean_*.tir` matches
//!   nothing at all: no fixture pins an ABI or struct-passing trailer.
//! * The declared pointer size and byte order (`8 little`) are identical on
//!   both JIT hosts, so no layout constant in a body can be host-dependent:
//!   the kernel types are `repr(Rust)` and their layout is the *compiler's*,
//!   which `build.rs`'s `fixture_toolchain` gate already pins, not the
//!   target's.
//!
//! That establishes a property of the COMMITTED TEXT: apart from the header
//! line it contains no architecture, OS or ABI token, so rewriting that line
//! is a loading step and the committed gold stays untouched. It is NOT a
//! claim that re-emitting the same Clean sources through an x86-64 frontend
//! would reproduce these bodies byte for byte — no x86-64 re-emission exists
//! to compare against, and this module does not need one. The consumers
//! assert on the frozen bodies lowered for the host, exactly the bodies and
//! exactly the assertions they use on AArch64.
//!
//! The rewrite is exact and fails closed: only a header line of the form
//! `target "<triple>" 8 little` with no ABI trailer is accepted; a fixture
//! declaring another pointer size, endianness or an `abi=`/`structpass=`
//! trailer is refused rather than silently retargeted, and the host must be a
//! JIT target this backend supports. A fixture without a target line (the
//! pre-2026-07-03 inline snapshots) is returned unchanged. When the fixture
//! already names the host — Darwin AArch64 for the frozen corpus, AArch64
//! Linux for upstream's ae9 corpus on its qualified host — the function is
//! the identity, so those floors keep their byte-for-byte input.

use std::borrow::Cow;

use trust_cg_codegen::Target;
use trust_cg_codegen::target::TargetSpec;

/// The architecture the in-process JIT executes on this host, or a refusal.
pub fn host_jit_target() -> Target {
    Target::try_host().unwrap_or_else(|| {
        panic!("Clean kernel fixtures need a supported in-process JIT host architecture")
    })
}

/// The canonical triple of this host, as the JIT's target spec spells it.
pub fn host_target_triple() -> String {
    TargetSpec::host_for_architecture(host_jit_target()).triple()
}

/// Rewrite a Clean fixture's `target` header line to this host's triple.
///
/// Refuses (panics) on any header shape other than
/// `target "<triple>" 8 little`, so a fixture that pins an ABI trailer, a
/// different pointer size or a different byte order is never retargeted.
pub fn host_kernel_fixture(text: &str) -> Cow<'_, str> {
    let Some((line_start, line)) = target_line(text) else {
        return Cow::Borrowed(text);
    };
    let (triple, rest) = parse_target_header(line);
    assert_eq!(
        rest, "8 little",
        "Clean fixture target header `{line}` is not `target \"<triple>\" 8 little`; \
         refusing to retarget a fixture with another pointer size, endianness or ABI trailer"
    );
    let host = host_target_triple();
    if triple == host {
        return Cow::Borrowed(text);
    }
    let mut out = String::with_capacity(text.len() + host.len());
    out.push_str(&text[..line_start]);
    out.push_str("target \"");
    out.push_str(&host);
    out.push_str("\" 8 little");
    out.push_str(&text[line_start + line.len()..]);
    Cow::Owned(out)
}

/// Parse a Clean fixture for the host: [`host_kernel_fixture`] then
/// `trust_ir::parser::parse_module`.
pub fn parse_host_module(text: &str) -> Result<trust_ir::Module, trust_ir::parser::ParseError> {
    trust_ir::parser::parse_module(&host_kernel_fixture(text))
}

/// The module header's `target` line (byte offset and text without the line
/// terminator), if the fixture declares one. Only column-zero lines are
/// considered; every instruction line is indented.
fn target_line(text: &str) -> Option<(usize, &str)> {
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        let body = line.trim_end_matches(['\n', '\r']);
        if body.starts_with("target \"") {
            return Some((offset, body));
        }
        // The header ends at the first function type; a `target` line after
        // that would be something else entirely.
        if body.starts_with("functy.") || body.starts_with("fn ") {
            return None;
        }
        offset += line.len();
    }
    None
}

/// Split `target "<triple>" <rest>` into the triple and the trimmed rest.
fn parse_target_header(line: &str) -> (&str, &str) {
    let after = line
        .strip_prefix("target \"")
        .expect("caller matched the `target \"` prefix");
    let close = after
        .find('"')
        .unwrap_or_else(|| panic!("unterminated triple in Clean fixture header `{line}`"));
    (&after[..close], after[close + 1..].trim())
}
