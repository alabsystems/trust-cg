//! `TCG_DUMP_LIR` — print the adapter's lowered LIR for a function, with each
//! instruction's trust_ir origin.
//!
//! The backend had no way to read its own LIR. `--emit-trust_ir` and
//! `--format=text` both print the trust_ir *input*; nothing printed the
//! instruction stream the adapter produced, so when an instruction selector
//! refused a malformed node the emitting adapter site could only be guessed at.
//! Guessing is unreliable in exactly the way that matters:
//! DR-X86-STRUCT-ARITH-PRODUCER-NOT-FOUND-20261020 records three candidate
//! sites eliminated by probe, one of which matched the failure's value
//! numbering *exactly* and still was not on the executed path.
//!
//! INERT BY DEFAULT and READ-ONLY. Every entry point is a no-op unless
//! `TCG_DUMP_LIR` is set to a value other than `0`/`false`/`off`, and when
//! enabled it only formats the `Function` it is handed and writes to stderr (or
//! to `TCG_DUMP_LIR_PATH`, appended). It never inspects, reorders or mutates
//! the instruction stream, so an ON-vs-OFF differential is byte-identical by
//! construction. Nothing on the compile or proof path reads its output: this
//! grants and withholds no authority, and a dumped stream is a diagnostic
//! rendering, not a canonical form.
//!
//! `TCG_DUMP_LIR=1` (or `all`, or `*`) dumps every translated function.
//! Any other value is a comma-separated list of SUBSTRINGS matched against the
//! function name, so `TCG_DUMP_LIR=packed_two_chains` dumps one body out of a
//! module.
//!
//! The origin column is the trust_ir instruction id the adapter recorded for
//! that LIR instruction ([`Function::trust_ir_origins`]). It is `-` where the
//! adapter recorded none: a synthetic instruction with no single source
//! instruction, or a block whose origins the adapter did not populate. A `-`
//! therefore means "this instruction is not attributed", NOT "this instruction
//! has no source".

use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::OnceLock;

use crate::function::Function;

/// What `TCG_DUMP_LIR` selects.
enum Selection {
    /// The variable is unset, empty, or one of `0`/`false`/`off`.
    Off,
    /// `1`, `all` or `*`: every translated function.
    All,
    /// Name substrings; a function is dumped when it contains any of them.
    Names(Vec<String>),
}

impl Selection {
    /// Whether a function with this name is selected.
    fn selects(&self, name: &str) -> bool {
        match self {
            Selection::Off => false,
            Selection::All => true,
            Selection::Names(names) => names.iter().any(|needle| name.contains(needle.as_str())),
        }
    }
}

/// Parse what `TCG_DUMP_LIR` is set to. Pure, so the whole knob is testable
/// without mutating the process environment.
///
/// An absent, empty, `0`, `false` or `off` value is OFF. `0` meaning OFF is
/// the point: a knob whose `0` reads as "on" is the fail-open spelling this
/// repo has already paid for once (OD-LINT/knob review, 2026-10).
fn parse(raw: Option<&str>) -> Selection {
    let Some(raw) = raw else {
        return Selection::Off;
    };
    let raw = raw.trim();
    if raw.is_empty()
        || raw == "0"
        || raw.eq_ignore_ascii_case("false")
        || raw.eq_ignore_ascii_case("off")
    {
        return Selection::Off;
    }
    if raw == "1" || raw.eq_ignore_ascii_case("all") || raw == "*" {
        return Selection::All;
    }
    let names: Vec<String> = raw
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(str::to_owned)
        .collect();
    if names.is_empty() {
        Selection::Off
    } else {
        Selection::Names(names)
    }
}

/// The selection `TCG_DUMP_LIR` requests. Evaluated once and cached — the flag
/// is a static property of the process environment.
fn selection() -> &'static Selection {
    static SELECTION: OnceLock<Selection> = OnceLock::new();
    SELECTION.get_or_init(|| parse(std::env::var("TCG_DUMP_LIR").ok().as_deref()))
}

/// Dump `func` when `TCG_DUMP_LIR` selects it. A no-op otherwise.
///
/// Called from the adapter's single per-function return, so every translation
/// path (module, census, inline-only, body template) dumps the same way.
pub fn dump_if_requested(func: &Function) {
    if !selection().selects(&func.name) {
        return;
    }
    emit(&render(func));
}

/// Format one function. Separated from [`emit`] so the renderer is testable
/// without touching the environment or the filesystem.
fn render(func: &Function) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "=== LIR {} ({:?} -> {:?}) entry={:?} ===",
        func.name, func.signature.params, func.signature.returns, func.entry_block
    );
    if !func.stack_slots.is_empty() {
        let _ = writeln!(out, "  stack_slots: {:?}", func.stack_slots);
    }
    // Sorted so a dump is reproducible: `value_types` is a HashMap, whose
    // iteration order is not stable across runs.
    if !func.value_types.is_empty() {
        let mut typed: Vec<_> = func.value_types.iter().collect();
        typed.sort_by_key(|(value, _)| value.0);
        let _ = writeln!(out, "  value_types:");
        for (value, ty) in typed {
            let _ = writeln!(out, "    {value:?} : {ty:?}");
        }
    }
    // `block_order` is the adapter's selection order; a block present in
    // `blocks` but absent from it is still dumped, after the ordered ones, so
    // the dump never silently omits a block.
    let mut blocks: Vec<_> = func.block_order.clone();
    let mut unordered: Vec<_> = func
        .blocks
        .keys()
        .copied()
        .filter(|block| !blocks.contains(block))
        .collect();
    unordered.sort_by_key(|block| block.0);
    blocks.extend(unordered);
    for block in blocks {
        let Some(basic_block) = func.blocks.get(&block) else {
            let _ = writeln!(out, "  {block:?}: <in block_order, absent from blocks>");
            continue;
        };
        let _ = writeln!(out, "  {:?}{:?}:", block, basic_block.params);
        let origins = func.trust_ir_origins.get(&block);
        for (index, inst) in basic_block.instructions.iter().enumerate() {
            let origin = origins
                .and_then(|origins| origins.get(index))
                .and_then(|origin| origin.as_ref())
                .map_or_else(|| "-".to_owned(), |origin| format!("%{}", origin.0));
            let _ = writeln!(
                out,
                "    [{index:3}] src={origin:>6}  {:?} args={:?} -> {:?}",
                inst.opcode, inst.args, inst.results
            );
        }
    }
    out
}

/// Write a rendered dump to `TCG_DUMP_LIR_PATH` (appended) or stderr.
///
/// A path that cannot be opened or written falls back to stderr rather than
/// dropping the dump: losing a diagnostic silently is the failure mode this
/// module exists to remove.
fn emit(text: &str) {
    if let Ok(path) = std::env::var("TCG_DUMP_LIR_PATH")
        && !path.trim().is_empty()
        && let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path.trim())
        && file.write_all(text.as_bytes()).is_ok()
    {
        return;
    }
    let _ = std::io::stderr().write_all(text.as_bytes());
}

#[cfg(test)]
mod tests {
    use super::{Selection, parse, render};
    use crate::function::{BasicBlock, Function, Signature};
    use crate::instructions::{Block, Instruction, Opcode, Value};
    use crate::types::Type;
    use trust_cg_ir::TrustIrInstId;

    /// `0`, `false` and `off` are OFF, and so is an unset, empty or
    /// whitespace-only value. A knob whose `0` reads as "on" is the fail-open
    /// spelling this repo has already paid for once, so each of those spellings
    /// is pinned here and not left to the reader of the parser.
    #[test]
    fn zero_and_friends_select_nothing() {
        for raw in [
            None,
            Some(""),
            Some("   "),
            Some("0"),
            Some("false"),
            Some("OFF"),
            Some(",,"),
        ] {
            assert!(
                !parse(raw).selects("anything"),
                "TCG_DUMP_LIR={raw:?} must be OFF"
            );
        }
    }

    /// The ON spellings, and that any other value is read as a name filter
    /// rather than as a second "on" — a filter that matched nothing would make
    /// the knob look broken, and a filter read as ON would dump every body.
    #[test]
    fn on_spellings_and_name_filters_are_distinguished() {
        for raw in ["1", "all", "ALL", "*"] {
            assert!(
                parse(Some(raw)).selects("whatever"),
                "TCG_DUMP_LIR={raw} must dump every function"
            );
        }
        let filter = parse(Some(" packed_two_chains , select_base "));
        assert!(filter.selects("packed_two_chains"));
        assert!(filter.selects("select_base"));
        assert!(!filter.selects("adjacent_fields"));
    }

    /// `All` takes every name; `Names` takes a SUBSTRING match, which is what
    /// makes `TCG_DUMP_LIR=packed_two_chains` pick one body out of a module
    /// whose symbol may be mangled around that name.
    #[test]
    fn selection_matches_substrings() {
        assert!(Selection::All.selects("_ZN4main"));
        let names = Selection::Names(vec!["packed_two_chains".to_owned()]);
        assert!(names.selects("packed_two_chains"));
        assert!(names.selects("_ZN17packed_two_chains17h0E"));
        assert!(!names.selects("select_base"));
    }

    /// The dump names the opcode, both operands and the result of every
    /// instruction, and the trust_ir instruction each came from — the three
    /// facts the eliminated-candidate hunt lacked. An unattributed instruction
    /// prints `-`, not a fabricated origin.
    #[test]
    fn render_names_opcodes_operands_and_origins() {
        let mut func = Function::new(
            "packed_two_chains",
            Signature {
                params: vec![Type::I64],
                returns: vec![Type::I64],
            },
        );
        let mut block = BasicBlock::default();
        block.params.push((Value(0), Type::I64));
        block.instructions.push(Instruction {
            opcode: Opcode::Iconst {
                ty: Type::I64,
                imm: 8,
            },
            args: vec![],
            results: vec![Value(4)],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::Iadd,
            args: vec![Value(2), Value(4)],
            results: vec![Value(3)],
        });
        func.blocks.insert(Block(0), block);
        func.block_order.push(Block(0));
        func.trust_ir_origins
            .insert(Block(0), vec![None, Some(TrustIrInstId(3))]);
        func.value_types
            .insert(Value(2), Type::Struct(vec![Type::I8, Type::I64, Type::I16]));

        let text = render(&func);
        assert!(text.contains("=== LIR packed_two_chains"), "{text}");
        assert!(
            text.contains("Value(2) : Struct([I8, I64, I16])"),
            "the dump must name the aggregate type the selector refuses: {text}"
        );
        assert!(
            text.contains("src=     -  Iconst { ty: I64, imm: 8 } args=[] -> [Value(4)]"),
            "an unattributed instruction prints `-`: {text}"
        );
        assert!(
            text.contains("src=    %3  Iadd args=[Value(2), Value(4)] -> [Value(3)]"),
            "the dump must name the producing trust_ir instruction: {text}"
        );
    }

    /// A block in `blocks` that `block_order` omits is still dumped: the dump
    /// must not hide an instruction stream the selector will still be handed.
    #[test]
    fn render_dumps_blocks_missing_from_block_order() {
        let mut func = Function::new(
            "unordered",
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        func.blocks.insert(Block(0), BasicBlock::default());
        let mut late = BasicBlock::default();
        late.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        func.blocks.insert(Block(7), late);
        func.block_order.push(Block(0));

        let text = render(&func);
        assert!(text.contains("Block(7)"), "{text}");
        assert!(text.contains("Return"), "{text}");
    }
}
