// trust-cg-llvm-import / metadata.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The module's named metadata and module flags, read as llc reads them: every
// name llc's parser, code generator or object writers act on is read or
// refused by name.

use std::collections::{HashMap, HashSet};

use crate::lexical::{Kind, Token, string_value};
use crate::{Error, Result};

fn refuse<T>(line: usize, what: impl std::fmt::Display) -> Result<T> {
    Err(Error::Unsupported(format!("line {line}: {what}")))
}

/// An `iN` constant as LLVM's parser builds it (`convertValIDToValue`: the
/// literal extended or truncated to `N` bits, so `i8 255` and `i8 -1` are one
/// value and `i1 2` is 0), for `N` up to 128.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IntConst {
    /// The value's `N` bits, zero-extended.
    bits: u128,
    width: u32,
}

impl IntConst {
    /// The constant `literal` of type `iN`, or `None` for a width this
    /// importer does not read (0, which LLVM rejects, or above 128).
    fn new(literal: i128, width: u32) -> Option<IntConst> {
        if !(1..=128).contains(&width) {
            return None;
        }
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        Some(IntConst {
            bits: (literal as u128) & mask,
            width,
        })
    }

    /// The value read as unsigned (`getZExtValue`, `getLimitedValue`).
    fn unsigned(self) -> u128 {
        self.bits
    }

    /// The value read as signed (`getSExtValue`, `isNonNegative`).
    fn signed(self) -> i128 {
        let shift = 128 - self.width;
        ((self.bits << shift) as i128) >> shift
    }
}

/// One operand of a metadata tuple, as far as this importer reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Element {
    /// `iN <integer>` (or `i1 true`/`false`): a `ConstantInt`.
    Int(IntConst),
    /// `iN u0x...` or `iN s0x...`: a `ConstantInt` LLVM's lexer reads from
    /// hexadecimal (an `APSInt` token), which this importer does not read;
    /// the spelling.
    HexInt(String),
    /// `!"..."`, decoded as LLVM decodes it.
    Str(Vec<u8>),
    /// `!N`.
    Node(u64),
    /// `!{...}` written inline.
    Tuple,
    /// `!DIExpression(...)`.
    Expression,
    /// Anything else (`null`, `ptr @g`, `[2 x i32] [...]`, `!DILocation(...)`).
    Other,
}

impl Element {
    fn describe(&self) -> String {
        match self {
            Element::Int(value) => format!("the integer i{} {}", value.width, value.signed()),
            Element::HexInt(spelled) => format!("the hexadecimal integer `{spelled}`"),
            Element::Str(bytes) => {
                format!(
                    "the string \"{}\"",
                    String::from_utf8_lossy(bytes).escape_debug()
                )
            }
            Element::Node(id) => format!("the node `!{id}`"),
            Element::Tuple => "an inline tuple".to_string(),
            Element::Expression => "a `!DIExpression`".to_string(),
            Element::Other => "a value this importer does not read".to_string(),
        }
    }
}

/// A numbered metadata node definition, `!N = [distinct] ...`.
#[derive(Debug)]
struct Node {
    line: usize,
    /// The operands of a tuple `!{...}`; `None` for a specialized node.
    tuple: Option<Vec<Element>>,
    /// The name of a specialized node (`DICompileUnit` of `!DICompileUnit(...)`).
    specialized: Option<String>,
}

/// A named metadata node: its name, the line of its first definition, and
/// every operand of its definitions with the line it is on.
type NamedNode = (String, usize, Vec<(NamedOperand, usize)>);

/// One operand of a named metadata node (`!name = !{ ... }`).
#[derive(Clone, Copy, Debug)]
enum NamedOperand {
    Node(u64),
    /// `!DIExpression(...)`, the one other form LLVM's parser reads there.
    Other,
}

/// The tokens of each top-level entity: `check_module` has refused an entity
/// continued on a later line and a second entity on a line, so every
/// metadata definition is one line, and nothing outside a function body
/// shares its line.
fn entity_lines(tokens: &[Token]) -> Vec<&[Token]> {
    let mut lines = Vec::new();
    let mut start = 0;
    for index in 1..=tokens.len() {
        if index == tokens.len() || tokens[index].line_first {
            if start < index {
                lines.push(&tokens[start..index]);
            }
            start = index;
        }
    }
    lines
}

/// The index after the bracket group opened at `tokens[open]`.
fn group_end(tokens: &[Token], open: usize) -> usize {
    crate::attributes::skip_bracket_group(tokens, open)
}

/// Read the operands of a tuple whose `{` is `tokens[open]`, and the index
/// after its `}`; `None` when the `{` is never closed.
fn tuple_elements(text: &str, tokens: &[Token], open: usize) -> Option<(Vec<Element>, usize)> {
    let end = group_end(tokens, open);
    if end <= open + 1 || tokens[end - 1].kind != Kind::Punct(b'}') {
        return None;
    }
    let inner = &tokens[open + 1..end - 1];
    let mut elements = Vec::new();
    let mut depth = 0i32;
    let mut piece_start = 0;
    let mut pieces: Vec<&[Token]> = Vec::new();
    for (index, token) in inner.iter().enumerate() {
        match token.kind {
            Kind::Punct(b',') if depth == 0 => {
                pieces.push(&inner[piece_start..index]);
                piece_start = index + 1;
            }
            Kind::Punct(b'(' | b'[' | b'{' | b'<') => depth += 1,
            Kind::Punct(b')' | b']' | b'}' | b'>') => depth -= 1,
            _ => {}
        }
    }
    if piece_start < inner.len() || !pieces.is_empty() {
        pieces.push(&inner[piece_start..]);
    }
    for piece in pieces {
        elements.push(element(text, piece));
    }
    Some((elements, end))
}

/// Classify one tuple operand.
fn element(text: &str, piece: &[Token]) -> Element {
    match piece {
        [bang, number] if bang.kind == Kind::Punct(b'!') && number.kind == Kind::Number => number
            .text(text)
            .parse::<u64>()
            .map_or(Element::Other, Element::Node),
        [bang, string] if bang.kind == Kind::Punct(b'!') && string.kind == Kind::Str => {
            Element::Str(string_value(string.text(text)))
        }
        [bang, open, ..] if bang.kind == Kind::Punct(b'!') && open.kind == Kind::Punct(b'{') => {
            Element::Tuple
        }
        [name, open, ..]
            if name.kind == Kind::MetadataName
                && name.text(text) == "!DIExpression"
                && open.kind == Kind::Punct(b'(') =>
        {
            Element::Expression
        }
        [ty, value] if ty.kind == Kind::Word => {
            let Some(width) = integer_width(ty.text(text)) else {
                return Element::Other;
            };
            if value.kind == Kind::Word && hex_integer_digits(value.text(text)).is_some() {
                return Element::HexInt(value.text(text).to_string());
            }
            let literal = match (value.kind, value.text(text)) {
                (Kind::Number, digits) => integer_literal(digits),
                (Kind::Word, "true") if width == 1 => Some(1),
                (Kind::Word, "false") if width == 1 => Some(0),
                _ => None,
            };
            literal
                .and_then(|literal| IntConst::new(literal, width))
                .map_or(Element::Other, Element::Int)
        }
        _ => Element::Other,
    }
}

/// The width `N` of `iN`, an LLVM integer type.
fn integer_width(word: &str) -> Option<u32> {
    word.strip_prefix('i')
        .filter(|bits| !bits.is_empty() && bits.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|bits| bits.parse::<u32>().ok())
}

/// The hexadecimal integer `u0x<hex>` or `s0x<hex>` (LLVM's `LexIdentifier`:
/// a keyword-shaped token, its digits all hexadecimal), as whether LLVM's
/// lexer reads it unsigned (`u`) and its digits; `None` for any other word.
fn hex_integer_digits(word: &str) -> Option<(bool, &str)> {
    let (unsigned, digits) = match word.as_bytes() {
        [b'u', b'0', b'x', ..] => (true, &word[3..]),
        [b's', b'0', b'x', ..] => (false, &word[3..]),
        _ => return None,
    };
    (!digits.is_empty() && digits.bytes().all(|b| b.is_ascii_hexdigit()))
        .then_some((unsigned, digits))
}

/// An LLVM integer literal: `-?[0-9]+` (`0x...` is a floating-point literal
/// to LLVM's lexer).
fn integer_literal(spelled: &str) -> Option<i128> {
    let digits = spelled.strip_prefix('-').unwrap_or(spelled);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    spelled.parse::<i128>().ok()
}

/// Read a numbered node's definition (the tokens after `!N =`).
fn node_definition(text: &str, rest: &[Token], line: usize) -> Node {
    let rest = match rest.first() {
        Some(word) if word.kind == Kind::Word && word.text(text) == "distinct" => &rest[1..],
        _ => rest,
    };
    match rest {
        [bang, open, ..] if bang.kind == Kind::Punct(b'!') && open.kind == Kind::Punct(b'{') => {
            Node {
                line,
                tuple: tuple_elements(text, rest, 1)
                    .filter(|(_, end)| *end == rest.len())
                    .map(|(elements, _)| elements),
                specialized: None,
            }
        }
        [name, open, ..] if name.kind == Kind::MetadataName && open.kind == Kind::Punct(b'(') => {
            Node {
                line,
                tuple: None,
                specialized: Some(name.text(text)[1..].to_string()),
            }
        }
        _ => Node {
            line,
            tuple: None,
            specialized: None,
        },
    }
}

/// The value tokens of the field `field` (`field:` in the source) of the
/// specialized node whose `(` is `tokens[open]`, or `None` when the node has
/// no such field. LLVM's parser rejects a field written twice
/// ([`specialized_field_count`]).
fn specialized_field<'t>(
    text: &str,
    tokens: &'t [Token],
    open: usize,
    field: &str,
) -> Option<&'t [Token]> {
    specialized_field_values(text, tokens, open, field)
        .into_iter()
        .next()
}

/// How many times the field `field` is written in the specialized node
/// whose `(` is `tokens[open]` (LLVM's parser rejects a second one: "field
/// 'X' cannot be specified more than once").
fn specialized_field_count(text: &str, tokens: &[Token], open: usize, field: &str) -> usize {
    specialized_field_values(text, tokens, open, field).len()
}

/// The value tokens of every `field:` of the specialized node whose `(` is
/// `tokens[open]`, in source order.
fn specialized_field_values<'t>(
    text: &str,
    tokens: &'t [Token],
    open: usize,
    field: &str,
) -> Vec<&'t [Token]> {
    let mut values = Vec::new();
    let end = group_end(tokens, open);
    let Some(inner) = tokens.get(open + 1..end.saturating_sub(1)) else {
        return values;
    };
    let mut depth = 0i32;
    let mut start = 0;
    for index in 0..=inner.len() {
        let separator = match inner.get(index).map(|token| token.kind) {
            None => true,
            Some(Kind::Punct(b',')) => depth == 0,
            Some(Kind::Punct(b'(' | b'[' | b'{' | b'<')) => {
                depth += 1;
                false
            }
            Some(Kind::Punct(b')' | b']' | b'}' | b'>')) => {
                depth -= 1;
                false
            }
            Some(_) => false,
        };
        if !separator {
            continue;
        }
        let piece = &inner[start..index];
        start = index + 1;
        if let [label, value @ ..] = piece
            && label.kind == Kind::Label
            && label.text(text).strip_suffix(':') == Some(field)
        {
            values.push(value);
        }
    }
    values
}

/// LLVM 22's `DISPFlag` names (`DebugInfoFlags.def`, which
/// `DISubprogram::getFlag` reads) and their bits. `DISPFlagZero` is not
/// among them: LLVM's parser rejects a name that reads as 0.
const SP_FLAG_NAMES: [(&str, u32); 11] = [
    ("DISPFlagVirtual", 1),
    ("DISPFlagPureVirtual", 1 << 1),
    ("DISPFlagLocalToUnit", 1 << 2),
    ("DISPFlagDefinition", 1 << 3),
    ("DISPFlagOptimized", 1 << 4),
    ("DISPFlagPure", 1 << 5),
    ("DISPFlagElemental", 1 << 6),
    ("DISPFlagRecursive", 1 << 7),
    ("DISPFlagMainSubprogram", 1 << 8),
    ("DISPFlagDeleted", 1 << 9),
    ("DISPFlagObjCDirect", 1 << 11),
];

/// `DISPFlagDefinition`: a `!DISubprogram` with it is a definition.
const SP_FLAG_DEFINITION: u32 = 1 << 3;

/// The `spFlags` field of a `!DISubprogram` (its value tokens) as LLVM's
/// parser reads it (`DISPFlagField`): `|`-separated flags combined by
/// bitwise or, each a `DISPFlag...` name or an integer LLVM's lexer reads
/// unsigned that fits in 32 bits (`parseUInt32`): a decimal or a `u0x`
/// hexadecimal. `None` for a field LLVM's parser rejects: a negative or
/// `s0x` integer (signed to LLVM's lexer: "expected debug info flag"), one
/// above 32 bits ("expected 32-bit integer (too large)"), a flag name LLVM
/// does not define or that reads as 0, an empty piece, or any other token.
fn sp_flags(text: &str, value: &[Token]) -> Option<u32> {
    let mut combined = 0;
    for piece in value.split(|token| token.kind == Kind::Punct(b'|')) {
        let [flag] = piece else {
            return None;
        };
        let spelled = flag.text(text);
        combined |= match flag.kind {
            Kind::Word if spelled.starts_with("DISPFlag") => SP_FLAG_NAMES
                .iter()
                .find(|(name, _)| *name == spelled)
                .map(|&(_, bits)| bits)?,
            Kind::Word => match hex_integer_digits(spelled)? {
                (true, digits) => u32::from_str_radix(digits, 16).ok()?,
                (false, _) => return None,
            },
            Kind::Number if spelled.bytes().all(|b| b.is_ascii_digit()) => {
                spelled.parse::<u32>().ok()?
            }
            _ => return None,
        };
    }
    Some(combined)
}

/// Whether LLVM's parser requires `distinct` before the specialized node
/// `!name(...)` whose `(` is `tokens[open]` (its three "missing 'distinct'"
/// errors): a `!DICompileUnit`, a `!DIAssignID`, and a `!DISubprogram` that
/// is a definition — `DISPFlagDefinition` among its `spFlags`, read as
/// LLVM reads them ([`sp_flags`]), or, without `spFlags`, an `isDefinition`
/// other than `false` (LLVM's default is `true`). An `spFlags` LLVM's
/// parser rejects is refused before this is asked ([`check_distinct_nodes`]).
fn requires_distinct(text: &str, tokens: &[Token], name: &str, open: usize) -> bool {
    match name {
        "DICompileUnit" | "DIAssignID" => true,
        "DISubprogram" => match specialized_field(text, tokens, open, "spFlags") {
            Some(value) => {
                sp_flags(text, value).is_some_and(|flags| flags & SP_FLAG_DEFINITION != 0)
            }
            None => !matches!(
                specialized_field(text, tokens, open, "isDefinition"),
                Some([value]) if value.kind == Kind::Word && value.text(text) == "false"
            ),
        },
        _ => false,
    }
}

/// Refuse a `!DICompileUnit`, `!DIAssignID` or defining `!DISubprogram`
/// written without `distinct` ([`requires_distinct`]), which LLVM's parser
/// rejects, wherever it is written; a `distinct` anywhere but right after
/// the `=` of a numbered node's definition (`!N = distinct ...`), the one
/// place LLVM's parser reads it (inside another node, `unit: distinct
/// !DICompileUnit(...)`, it rejects it: "expected metadata operand"); and
/// a `!DISubprogram` whose `spFlags` LLVM's parser rejects ([`sp_flags`]),
/// whose `isDefinition` is not `true` or `false` (LLVM's parser reads the
/// field as a boolean: "expected 'true' or 'false'"), or that writes either
/// field twice (LLVM's parser rejects a second one; the reader here would
/// take the first): the two fields decide whether it is a definition.
fn check_distinct_nodes(text: &str, tokens: &[Token]) -> Result<()> {
    for (index, token) in tokens.iter().enumerate() {
        if token.kind == Kind::Word && token.text(text) == "distinct" {
            let definition = index >= 3
                && tokens[index - 1].kind == Kind::Punct(b'=')
                && tokens[index - 2].kind == Kind::Number
                && tokens[index - 3].kind == Kind::Punct(b'!');
            if !definition {
                return refuse(
                    token.line,
                    "`distinct` where LLVM's parser does not read it (only right after the `=` \
                     of a numbered metadata node's definition, `!N = distinct ...`)",
                );
            }
            continue;
        }
        if token.kind != Kind::MetadataName
            || tokens
                .get(index + 1)
                .is_none_or(|open| open.kind != Kind::Punct(b'('))
        {
            continue;
        }
        let name = &token.text(text)[1..];
        if name == "DISubprogram"
            && let Some(field) = ["isDefinition", "spFlags"]
                .into_iter()
                .find(|field| specialized_field_count(text, tokens, index + 1, field) > 1)
        {
            return refuse(
                token.line,
                format!(
                    "a `!DISubprogram` with `{field}` written twice (LLVM's parser rejects it: \
                     \"field '{field}' cannot be specified more than once\")"
                ),
            );
        }
        if name == "DISubprogram"
            && let Some(value) = specialized_field(text, tokens, index + 1, "isDefinition")
            && !matches!(value, [flag] if flag.kind == Kind::Word
                && matches!(flag.text(text), "true" | "false"))
        {
            return refuse(
                token.line,
                "a `!DISubprogram` `isDefinition` other than `true` or `false` (LLVM's parser \
                 rejects it: \"expected 'true' or 'false'\")",
            );
        }
        if name == "DISubprogram"
            && let Some(value) = specialized_field(text, tokens, index + 1, "spFlags")
            && sp_flags(text, value).is_none()
        {
            return refuse(
                token.line,
                "a `!DISubprogram` `spFlags` LLVM's parser rejects (it reads `|`-separated \
                 `DISPFlag` names and unsigned 32-bit integers, decimal or `u0x` hexadecimal)",
            );
        }
        let distinct = index > 0
            && tokens[index - 1].kind == Kind::Word
            && tokens[index - 1].text(text) == "distinct";
        if !distinct && requires_distinct(text, tokens, name, index + 1) {
            return refuse(
                token.line,
                format!(
                    "`!{name}` without `distinct` (LLVM's parser rejects it: \"missing \
                     'distinct', required for !{name}\")"
                ),
            );
        }
    }
    Ok(())
}

/// Read the operands of `!name = !{ ... }` (the tokens after the `=`), or
/// `None` when the right-hand side is not that shape.
fn named_operands(text: &str, rest: &[Token]) -> Option<Vec<NamedOperand>> {
    let [bang, open, ..] = rest else {
        return None;
    };
    if bang.kind != Kind::Punct(b'!') || open.kind != Kind::Punct(b'{') {
        return None;
    }
    let (elements, end) = tuple_elements(text, rest, 1)?;
    if end != rest.len() {
        return None;
    }
    elements
        .into_iter()
        .map(|element| match element {
            Element::Node(id) => Some(NamedOperand::Node(id)),
            // The one other operand LLVM's parser reads in named metadata.
            Element::Expression => Some(NamedOperand::Other),
            _ => None,
        })
        .collect()
}

/// What this importer does with the named metadata `name`.
enum NamedRule {
    /// `!llvm.module.flags`: every flag read ([`module_flag_refusal`]).
    ModuleFlags,
    /// Read and dropped: llc writes only records no program reads (the
    /// `.comment` identification strings, the command line, debug
    /// information). `operand` names the node every operand must be, as
    /// LLVM's verifier checks (for `!llvm.dbg.cu` a debug-information check,
    /// which llc answers by dropping the debug information).
    Records { operand: RecordOperand },
    /// llc acts on it in a way this importer does not; the reason.
    Refused(&'static str),
    /// llc acts on each operand in a way this importer does not (the
    /// reason); with no operand, it writes an empty ELF section (`.deplibs`,
    /// `.linker-options`) that no linker reads, and nothing on Mach-O.
    RefusedUnlessEmpty(&'static str),
    /// A name llc does not read for these targets.
    Inert,
}

#[derive(Clone, Copy)]
enum RecordOperand {
    /// `!{!"..."}`: one string.
    OneString,
    /// `distinct !DICompileUnit(...)`.
    CompileUnit,
}

/// The named metadata llc 22 (`llc`'s parser, auto-upgrade, code generator
/// and object writers for AArch64 and x86-64 ELF and Mach-O) reads, from a
/// survey of `getNamedMetadata` in LLVM 22's `lib/` (`AsmParser`, `IR`,
/// `CodeGen`, `Target`, `MC`, `Object`): each read or refused by name. Any
/// other name in LLVM's reserved `llvm.` namespace is refused too; any other
/// name is one llc does not read.
fn named_metadata_rule(name: &str) -> NamedRule {
    match name {
        "llvm.module.flags" => NamedRule::ModuleFlags,
        // `AsmPrinter::emitModuleIdents` writes the strings to `.comment`
        // (ELF) or nothing (Mach-O).
        "llvm.ident" => NamedRule::Records {
            operand: RecordOperand::OneString,
        },
        // `AsmPrinter::emitModuleCommandLines` writes `.GCC.command.line`.
        "llvm.commandline" => NamedRule::Records {
            operand: RecordOperand::OneString,
        },
        // Debug information (`.debug_*` sections); LLVM builds the same code
        // with and without it.
        "llvm.dbg.cu" => NamedRule::Records {
            operand: RecordOperand::CompileUnit,
        },
        // LLVM's verifier calls any other `llvm.dbg.` name invalid debug
        // information, and llc then drops the module's debug information with
        // a warning ("ignoring invalid debug info", or, without a `Debug Info
        // Version` of 3, "ignoring debug info with an invalid version") and
        // builds the code.
        _ if name.starts_with("llvm.dbg.") => NamedRule::Refused(
            "a name in LLVM's `llvm.dbg.` namespace other than `llvm.dbg.cu`, which llc drops \
             with the module's debug information, warning that it is invalid; this importer \
             refuses it",
        ),
        "llvm.dependent-libraries" => NamedRule::RefusedUnlessEmpty(
            "llc writes the named libraries to an ELF `.deplibs` section, from which LLD links \
             them; this importer writes none, so the imported object does not pull them in",
        ),
        "llvm.linker.options" => NamedRule::RefusedUnlessEmpty(
            "llc writes the linker options (ELF `.linker-options`, Mach-O `LC_LINKER_OPTION`, \
             which ld64 obeys); this importer writes none",
        ),
        "llvm.stats" => {
            NamedRule::Refused("llc writes an `.llvm_stats` section; this importer writes none")
        }
        "llvm.pseudo_probe_desc" => NamedRule::Refused(
            "llc writes the pseudo-probe descriptors and probes for sample profiling; this \
             importer writes none",
        ),
        "llvm.embedded.objects" | "llvm.offloading.symbols" => NamedRule::Refused(
            "llc embeds the offloading objects it names; this importer embeds none",
        ),
        "llvm.errno.tbaa" => NamedRule::Refused(
            "type-based alias facts for `errno`, which LLVM's verifier checks as TBAA nodes; \
             this importer reads no TBAA",
        ),
        "llvm.debugify" | "llvm.mir.debugify" => NamedRule::Refused(
            "LLVM's debugify test metadata, which llc's debugify passes read and check",
        ),
        "nvvm.annotations" => NamedRule::Refused(
            "LLVM's parser upgrades these NVPTX annotations into function attributes and \
             calling conventions",
        ),
        "hipe.literals" => NamedRule::Refused(
            "x86 HiPE frame-lowering literals, which llc reads for its HiPE calling convention",
        ),
        "wasm.custom_sections" => NamedRule::Refused(
            "llc writes these WebAssembly custom sections; this importer writes none",
        ),
        "clang.arc.retainAutoreleasedReturnValueMarker" => NamedRule::Refused(
            "LLVM's parser upgrades this Objective-C ARC marker into a module flag that \
             llc's ARC lowering reads",
        ),
        _ if name.starts_with("llvm.") => NamedRule::Refused(
            "named metadata in LLVM's reserved `llvm.` namespace that this importer does not \
             read",
        ),
        _ => NamedRule::Inert,
    }
}

/// The module flags llc 22 reads for these targets, from a survey of
/// `getModuleFlag` and the `Module` accessors over it (`getPICLevel`,
/// `getCodeModel`, `getStackProtectorGuard`, ...) in LLVM 22's `lib/`, with
/// what this importer does with each. A flag read here changes nothing the
/// importer builds; every other key is refused by name.
fn module_flag_refusal(key: &str, value: &Element) -> Option<String> {
    let integer = |value: &Element| matches!(value, Element::Int(_));
    let not_integer = || {
        Some(format!(
            "{}, where llc reads a constant integer",
            value.describe()
        ))
    };
    match key {
        // Read by nothing the importer's backend builds, and by nothing llc
        // builds that runs differently from it: `wchar_size` by the
        // library-call simplifier (an `opt` pass), `uwtable` and
        // `frame-pointer` only when a pass creates a function
        // (`Function::createWithDefaultAttr`), `PIC Level` by PowerPC and,
        // on AArch64 ELF, by the stack protector's `__stack_chk_guard`
        // declaration (`insertSSPDeclarations`, through
        // `getDirectAccessExternalData`, whose own flag is refused): at level
        // 0, as with no flag, llc addresses the guard PC-relative, which a
        // shared object cannot link, and at any other level through the
        // GOT, as the importer's backend always does (x86-64 reads it only
        // for a refused `stack-protector-guard-symbol`), `PIE Level` by the
        // TLS model (the importer refuses `thread_local`)
        // and by the local aliases llc writes for `dso_local` definitions in
        // a shared object (`dso_local` promises that no other definition
        // interposes), the debug-information versions by the DWARF writer,
        // and `RtLibUseGOT` (`-fno-plt`) by the call lowering, which then
        // calls the same runtime functions through the GOT.
        "wchar_size" | "PIC Level" | "PIE Level" | "uwtable" | "frame-pointer"
        | "Dwarf Version" | "Debug Info Version" | "DWARF64" | "RtLibUseGOT" => {
            if integer(value) {
                None
            } else {
                not_integer()
            }
        }
        // Mach-O build-version facts and profile summaries (hints for block
        // placement and function splitting).
        "SDK Version" | "ProfileSummary" | "CSProfileSummary" => None,
        // The code model llc builds with (`llc` sets it from the flag); the
        // importer's backend builds every target's default, small.
        "Code Model" => match value {
            Element::Int(model) if model.unsigned() == 1 => None,
            Element::Int(_) => Some(
                "a code model other than `small` (1), which llc builds with and this importer's \
                 backend does not"
                    .to_string(),
            ),
            _ => not_integer(),
        },
        // Branch protection: llc writes the GNU property note (and, under an
        // ARM or AArch64 `target triple`, LLVM's parser gives every
        // definition the matching attribute) for any value but 0.
        "branch-target-enforcement"
        | "guarded-control-stack"
        | "sign-return-address"
        | "sign-return-address-all"
        | "sign-return-address-with-bkey"
        | "branch-protection-pauth-lr" => match value {
            Element::Int(on) if on.unsigned() == 0 => None,
            Element::Int(_) => Some(
                "llc builds BTI landing pads, return-address signing or guarded-control-stack \
                 code and marks the object with the GNU property note; this importer's backend \
                 does neither"
                    .to_string(),
            ),
            _ => not_integer(),
        },
        // AArch64 frames are always probed at most 4096 bytes apart, as
        // LLVM's `inline-asm` method does.
        "probe-stack" => match value {
            Element::Str(method) if method == b"inline-asm" => None,
            _ => Some(
                "a stack probe method other than `inline-asm` (llc on AArch64 aborts on any \
                 other; elsewhere it calls the named function, which this importer does not)"
                    .to_string(),
            ),
        },
        // Read as `getZExtValue` reads it, unsigned at the constant's width
        // (`i16 61440` is 61440); the interval admitted is the attribute's
        // ([`crate::attributes::stack_probe_interval_read`]).
        "stack-probe-size" => match value {
            Element::Int(size) if crate::attributes::stack_probe_interval_read(size.unsigned()) => {
                None
            }
            Element::Int(_) => Some(
                "a stack-probe interval below the 4096 bytes AArch64 frames are probed at, or at \
                 or above 2^63 (LLVM reads it as a `uint64_t` and asserts it is positive as an \
                 `int64_t`)"
                    .to_string(),
            ),
            _ => not_integer(),
        },
        "stack-protector-guard"
        | "stack-protector-guard-reg"
        | "stack-protector-guard-symbol"
        | "stack-protector-guard-offset" => Some(
            "llc reads the stack-protector canary from where it says (a system register, \
             another symbol or offset); this importer's backend reads `__stack_chk_guard`"
                .to_string(),
        ),
        "override-stack-alignment" => Some(
            "llc aligns the stack as it says; this importer's backend keeps the ABI alignment"
                .to_string(),
        ),
        "direct-access-external-data" | "SemanticInterposition" => Some(
            "llc addresses external data or interposable symbols as it says; this importer's \
             backend does not read it"
                .to_string(),
        ),
        "kcfi" | "kcfi-arity" | "kcfi-hash" | "kcfi-offset" | "cfi-normalize-integers" => {
            Some("llc checks indirect calls (KCFI); this importer's backend does not".to_string())
        }
        "cf-protection-branch"
        | "cf-protection-return"
        | "indirect_branch_cs_prefix"
        | "function_return_thunk_extern" => Some(
            "llc builds x86 control-flow protection (`endbr64`, the CET property note, return \
             thunks or branch prefixes) whenever the flag is present; this importer's backend \
             does not"
                .to_string(),
        ),
        "SkipRaxSetup" => Some(
            "llc omits setting `%al` before an x86-64 variadic call; this importer's backend \
             sets it"
                .to_string(),
        ),
        // llc's three readers of these two (the AArch64 asm printer and
        // function info, `MachineModuleInfoELF`) act only on
        // `getZExtValue() == 1`, so 0 is off; clang 22 writes them only when
        // on. Later clang (upstream clang at 2f8eb5b4be, and at least since
        // 2026-07-24, the oldest commit of the shallow clone read) writes them
        // at 0 on every AArch64 ELF (`ptrauth-elf-got`) or Linux
        // (`ptrauth-sign-personality`) module, but with flags refused here:
        // `ptrauth-init-fini` and `ptrauth-init-fini-address-discrimination`
        // (which llc 22 does not read) and, on Linux, the
        // `aarch64-elf-pauthabi-platform`/`-version` pair below.
        "ptrauth-elf-got" | "ptrauth-sign-personality" => match value {
            Element::Int(on) if on.unsigned() == 0 => None,
            Element::Int(_) => Some(
                "llc signs GOT entries or the personality pointer; this importer's backend does \
                 not"
                .to_string(),
            ),
            _ => not_integer(),
        },
        // llc writes the pair into a `.note.gnu.property` pointer-
        // authentication property (at any value but `2^64 - 1`, a version of
        // 0 included; LLD compares it across its inputs) and, unless both
        // are 0, into the `.ARM.attributes` build attributes.
        "aarch64-elf-pauthabi-platform" | "aarch64-elf-pauthabi-version" => Some(
            "llc marks the object with this pointer-authentication ABI (a `.note.gnu.property` \
             property, a version of 0 included); this importer's backend writes none"
                .to_string(),
        ),
        "CG Profile" => Some(
            "llc writes a call-graph profile section that references the functions it names; \
             this importer writes none"
                .to_string(),
        ),
        "MaxTLSAlign"
        | "Large Data Threshold"
        | "target-abi"
        | "darwin.target_variant.triple"
        | "darwin.target_variant.SDK Version"
        | "NumRegisterParameters"
        | "ehcontguard"
        | "cfguard"
        | "eh-asynch"
        | "ms-kernel"
        | "import-call-optimization"
        | "winx64-eh-unwindv2"
        | "SmallDataLimit" => Some(
            "llc builds code or object records for it that this importer's backend does not"
                .to_string(),
        ),
        _ if key.starts_with("Objective-C ") || key.starts_with("Swift ") => Some(
            "llc writes the Objective-C image info it describes; this importer writes none"
                .to_string(),
        ),
        _ => Some(
            "not a module flag this importer reads (it reads only flags known to change \
             nothing it builds)"
                .to_string(),
        ),
    }
}

/// The module's `target triple = "..."` as LLVM decodes it, or `None`: the
/// last one, as LLVM's parser keeps the last, whatever its bytes. A last
/// triple whose bytes are not UTF-8 is refused by name (LLVM keeps the
/// bytes; this importer reads a triple as text), never passed over for an
/// earlier one.
pub(crate) fn module_triple(text: &str, tokens: &[Token]) -> Result<Option<String>> {
    let Some(value) = entity_lines(tokens)
        .into_iter()
        .rev()
        .find_map(|entity| match entity {
            [target, triple, equal, value]
                if target.kind == Kind::Word
                    && target.text(text) == "target"
                    && triple.kind == Kind::Word
                    && triple.text(text) == "triple"
                    && equal.kind == Kind::Punct(b'=')
                    && value.kind == Kind::Str =>
            {
                Some(value.text(text))
            }
            _ => None,
        })
    else {
        return Ok(None);
    };
    match String::from_utf8(string_value(value)) {
        Ok(triple) => Ok(Some(triple)),
        Err(_) => Err(Error::Unsupported(format!(
            "`target triple = {value}`: the triple's bytes are not UTF-8 (LLVM keeps the last \
             `target triple`'s bytes and reads them as its triple; this importer reads a triple \
             as text)"
        ))),
    }
}

/// LLVM's module-flag behaviors (`Module::ModFlagBehavior`).
const ERROR: u128 = 1;
const REQUIRE: u128 = 3;
const APPEND: u128 = 5;
const APPEND_UNIQUE: u128 = 6;
const MAX: u128 = 7;
const MIN: u128 = 8;

/// Read every flag `!llvm.module.flags` lists, as LLVM's verifier and llc
/// read it, refusing by name what llc acts on and the importer does not.
fn check_module_flags(
    operands: &[(NamedOperand, usize)],
    nodes: &HashMap<u64, Node>,
) -> Result<()> {
    let mut seen: HashSet<Vec<u8>> = HashSet::new();
    for &(operand, line) in operands {
        let NamedOperand::Node(id) = operand else {
            return refuse(
                line,
                "a `!llvm.module.flags` operand that is not a node `!N` (LLVM's verifier \
                 rejects it)",
            );
        };
        let Some(node) = nodes.get(&id) else {
            return refuse(line, format!("module flag `!{id}` is never defined"));
        };
        let line = node.line;
        let Some(elements) = &node.tuple else {
            return refuse(
                line,
                format!(
                    "module flag `!{id}` is not a tuple `!{{...}}` (LLVM's verifier rejects it)"
                ),
            );
        };
        let [behavior, key, value] = elements.as_slice() else {
            return refuse(
                line,
                format!(
                    "module flag `!{id}` has {} operands (LLVM's verifier requires three: \
                     behavior, key and value)",
                    elements.len()
                ),
            );
        };
        // LLVM reads `iN u0x...`/`iN s0x...` as an integer constant like any
        // other; this importer does not read that spelling.
        if let Some(Element::HexInt(spelled)) = [behavior, value]
            .into_iter()
            .find(|element| matches!(element, Element::HexInt(_)))
        {
            return refuse(
                line,
                format!(
                    "module flag `!{id}` spells an integer in hexadecimal (`{spelled}`), which \
                     LLVM reads as an integer constant and this importer does not read"
                ),
            );
        }
        let Element::Int(behavior) = *behavior else {
            return refuse(
                line,
                format!(
                    "module flag `!{id}` without an integer behavior (LLVM's verifier rejects it)"
                ),
            );
        };
        // `Module::isValidModFlagBehavior` reads the behavior unsigned.
        let behavior = behavior.unsigned();
        if !(1..=8).contains(&behavior) {
            return refuse(
                line,
                format!(
                    "module flag `!{id}` with behavior {behavior} (LLVM's verifier rejects it)"
                ),
            );
        }
        let Element::Str(key) = key else {
            return refuse(
                line,
                format!("module flag `!{id}` without a string key (LLVM's verifier rejects it)"),
            );
        };
        // LLVM's parser upgrades these behaviors (`UpgradeModuleFlags`)
        // before the verifier reads the flag: `PIC Level` from error or max
        // to min, `PIE Level` from error to max, and the branch-protection
        // flags from error to min.
        let written = behavior;
        let behavior = match (key.as_slice(), behavior) {
            (b"PIC Level", ERROR | MAX) => MIN,
            (b"PIE Level", ERROR) => MAX,
            (key, ERROR)
                if key == b"branch-target-enforcement"
                    || key.starts_with(b"sign-return-address") =>
            {
                MIN
            }
            (_, behavior) => behavior,
        };
        let shown = String::from_utf8_lossy(key).escape_debug().to_string();
        let flag = |what: String| refuse::<()>(line, format!("module flag \"{shown}\" ({what})"));
        if behavior == REQUIRE {
            return flag(
                "a `require` flag, which constrains another flag's value; this importer reads \
                 no requirements"
                    .to_string(),
            );
        }
        let valid = match behavior {
            MAX => matches!(value, Element::Int(_)),
            MIN => matches!(value, Element::Int(v) if v.signed() >= 0),
            APPEND | APPEND_UNIQUE => matches!(value, Element::Node(_) | Element::Tuple),
            _ => true,
        };
        if !valid {
            let upgraded = if written == behavior {
                String::new()
            } else {
                format!(" (LLVM's parser upgrades this flag's behavior {written} to {behavior})")
            };
            return flag(format!(
                "{} under behavior {behavior}{upgraded}, which LLVM's verifier rejects",
                value.describe()
            ));
        }
        if !seen.insert(key.clone()) {
            return flag(
                "listed twice (LLVM's verifier requires each flag's key to be unique)".to_string(),
            );
        }
        let Ok(key) = std::str::from_utf8(key) else {
            return flag("a key that is not UTF-8 after LLVM's escapes".to_string());
        };
        if let Some(why) = module_flag_refusal(key, value) {
            return flag(why);
        }
    }
    Ok(())
}

/// Check every operand of a record-only named metadata node.
fn check_records(
    name: &str,
    operand: RecordOperand,
    operands: &[(NamedOperand, usize)],
    nodes: &HashMap<u64, Node>,
) -> Result<()> {
    for &(named, line) in operands {
        let node = match named {
            NamedOperand::Node(id) => nodes.get(&id),
            NamedOperand::Other => None,
        };
        let valid = node.is_some_and(|node| match operand {
            RecordOperand::OneString => {
                matches!(node.tuple.as_deref(), Some([Element::Str(_)]))
            }
            RecordOperand::CompileUnit => node.specialized.as_deref() == Some("DICompileUnit"),
        });
        if !valid {
            let (wanted, llvm) = match operand {
                RecordOperand::OneString => {
                    ("a node holding one string", "LLVM's verifier rejects it")
                }
                // `CheckDI`: a debug-information failure, not a broken module.
                RecordOperand::CompileUnit => (
                    "a `!DICompileUnit` node",
                    "LLVM's verifier calls the debug information invalid, and llc drops it with \
                     a warning; this importer refuses it",
                ),
            };
            return refuse(
                line,
                format!("`!{name}` lists an operand that is not {wanted} ({llvm})"),
            );
        }
    }
    Ok(())
}

/// Read the module's named metadata and module flags (`text` is the module,
/// already canonical: a metadata name is spelled as LLVM decodes it), and
/// refuse by name what llc acts on and this importer does not carry:
///
/// * named metadata llc reads ([`named_metadata_rule`]): the module flags
///   are read flag by flag; the identification strings, command lines and
///   debug compile units are dropped once each operand is the node LLVM's
///   verifier checks for (one string, a `!DICompileUnit`; the debug records
///   are not otherwise validated); and every other name llc reads, any other
///   in the `llvm.dbg.` namespace (which llc drops with the debug
///   information) and any other in the `llvm.` namespace is refused
///   (`!llvm.dependent-libraries`: llc's object makes LLD link the library,
///   the imported one does not);
/// * a module flag llc reads ([`module_flag_refusal`]) unless it changes
///   nothing the importer builds, and a flag LLVM's verifier rejects after
///   the parser's behavior upgrades (a behavior outside 1..=8, a key listed
///   twice, a value its behavior does not admit, a `require` flag), its
///   integers read as LLVM's `iN` constants ([`IntConst`]; an integer
///   spelled `u0x`/`s0x`, which LLVM reads too, is refused by name);
/// * a numbered node defined twice, a reference to a node never defined, a
///   node LLVM requires `distinct` written without it, a `distinct` inside
///   another node, and a `!DISubprogram` `spFlags` or `isDefinition` LLVM
///   cannot read ([`check_distinct_nodes`]), which LLVM's parser rejects.
pub(crate) fn check_module_metadata(text: &str, tokens: &[Token]) -> Result<()> {
    check_distinct_nodes(text, tokens)?;
    let mut nodes: HashMap<u64, Node> = HashMap::new();
    // Each name, the line of its first definition and its operands.
    let mut named: Vec<NamedNode> = Vec::new();
    for entity in entity_lines(tokens) {
        let first = entity[0];
        let is_equal = |at: usize| {
            entity
                .get(at)
                .is_some_and(|token| token.kind == Kind::Punct(b'='))
        };
        if first.kind == Kind::MetadataName && is_equal(1) {
            let name = first.text(text)[1..].to_string();
            let Some(operands) = named_operands(text, &entity[2..]) else {
                return refuse(
                    first.line,
                    format!(
                        "named metadata `!{name}` that is not `!{{ !N, ... }}` (LLVM's parser \
                         rejects it)"
                    ),
                );
            };
            let operands = operands.into_iter().map(|op| (op, first.line)).collect();
            // LLVM appends the operands of a second definition to the first.
            match named.iter_mut().find(|(existing, _, _)| *existing == name) {
                Some((_, _, existing)) => existing.extend(operands),
                None => named.push((name, first.line, operands)),
            }
            continue;
        }
        if first.kind == Kind::Punct(b'!')
            && entity
                .get(1)
                .is_some_and(|number| number.kind == Kind::Number)
            && is_equal(2)
        {
            let Ok(id) = entity[1].text(text).parse::<u64>() else {
                return refuse(
                    first.line,
                    format!(
                        "metadata node `!{}` with an unreadable number",
                        entity[1].text(text)
                    ),
                );
            };
            let node = node_definition(text, &entity[3..], first.line);
            if nodes.insert(id, node).is_some() {
                return refuse(
                    first.line,
                    format!("metadata node `!{id}` defined twice (LLVM's parser rejects it)"),
                );
            }
        }
    }
    // Every `!N` the module uses must be defined.
    for (index, token) in tokens.iter().enumerate() {
        if token.kind != Kind::Punct(b'!') {
            continue;
        }
        let Some(number) = tokens.get(index + 1).filter(|t| t.kind == Kind::Number) else {
            continue;
        };
        let defines = token.line_first
            && tokens
                .get(index + 2)
                .is_some_and(|equal| equal.kind == Kind::Punct(b'='));
        if defines {
            continue;
        }
        let defined = number
            .text(text)
            .parse::<u64>()
            .is_ok_and(|id| nodes.contains_key(&id));
        if !defined {
            return refuse(
                token.line,
                format!(
                    "use of undefined metadata `!{}` (LLVM's parser rejects it)",
                    number.text(text)
                ),
            );
        }
    }
    for (name, line, operands) in &named {
        match named_metadata_rule(name) {
            NamedRule::ModuleFlags => check_module_flags(operands, &nodes)?,
            NamedRule::Records { operand } => check_records(name, operand, operands, &nodes)?,
            NamedRule::Refused(why) => {
                return refuse(*line, format!("named metadata `!{name}` ({why})"));
            }
            NamedRule::RefusedUnlessEmpty(why) if !operands.is_empty() => {
                return refuse(*line, format!("named metadata `!{name}` ({why})"));
            }
            NamedRule::RefusedUnlessEmpty(_) | NamedRule::Inert => {}
        }
    }
    Ok(())
}
