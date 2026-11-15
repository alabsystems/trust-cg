// trust-cg-lower/source_scan.rs - A small Rust source scanner for drift tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Test-only: the lexer and module-tree walker the runtime-symbol drift rows
//! of `trust-cg-lower`, `trust-cg-opt` and `trust-cg-codegen` share (the
//! latter two include this one file by `#[path]`).
//!
//! The walker follows a crate's module tree from `lib.rs` (`mod x;`
//! declarations, Trust's `clean mod` declarations, `#[path]` attributes,
//! declarations inside inline modules),
//! so a scan reads exactly the files the crate compiles. A file is test-only
//! when every declaration chain to it requires `test`. Positive `all`/`any`
//! conditions are checked conservatively; unsupported conditions remain
//! production. In the other
//! files the lexer drops comments, keeps string and char literals as single
//! tokens (so a brace or quote inside one never counts) and lexes raw
//! identifiers, and each item, statement, field or arm carrying
//! `#[cfg(test)]` is removed, bounded by its own braces, `;` or `,`, so code
//! after an inline or out-of-line test module is still scanned.
//!
//! A non-test `include!` fails the scan, because the included text is not
//! read.
//!
//! It is a source scan, not a proof: a name assembled by `concat!`,
//! formatting or a macro fragment, a further invocation of a macro whose body
//! already holds a counted use, a name read through a helper defined in
//! another crate, or one routed through an existing site by a variable, is
//! not seen.

#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Tok {
    Ident(String),
    /// `::`
    PathSep,
    Punct(char),
    /// A string literal's contents (escapes left as written).
    Str(String),
    /// A char or byte literal.
    Char,
    /// A lifetime or label (`'a`).
    Lifetime,
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Tokens of `source` without comments. Raw strings (`r"..."`, `r#"..."#`,
/// with an optional `b`/`c` prefix), raw identifiers (`r#name`, lexed as
/// `name`), escaped strings, char and byte literals and lifetimes are
/// recognized, so no literal's contents reach the token stream as code.
pub(crate) fn lex(source: &str) -> Vec<Tok> {
    let chars: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    let at = |i: usize| chars.get(i).copied().unwrap_or('\0');
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '/' && at(i + 1) == '/' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && at(i + 1) == '*' {
            let mut depth = 1;
            i += 2;
            while i < chars.len() && depth > 0 {
                if chars[i] == '/' && at(i + 1) == '*' {
                    depth += 1;
                    i += 2;
                } else if chars[i] == '*' && at(i + 1) == '/' {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
        } else if c == '"' {
            let mut content = String::new();
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                if chars[i] == '\\' {
                    content.push(chars[i]);
                    i += 1;
                }
                if i < chars.len() {
                    content.push(chars[i]);
                    i += 1;
                }
            }
            i += 1;
            tokens.push(Tok::Str(content));
        } else if c == '\'' {
            if at(i + 1) == '\\' {
                // An escaped char literal: to the closing quote.
                i += 2;
                while i < chars.len() && chars[i] != '\'' {
                    i += 1;
                }
                i += 1;
                tokens.push(Tok::Char);
            } else if at(i + 2) == '\'' {
                i += 3;
                tokens.push(Tok::Char);
            } else {
                i += 1;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                tokens.push(Tok::Lifetime);
            }
        } else if is_ident_start(c) {
            let start = i;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            // A raw identifier: `r#` then an identifier (`r#Symbol`).
            if word == "r" && at(i) == '#' && is_ident_start(at(i + 1)) {
                let start = i + 1;
                i += 1;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                tokens.push(Tok::Ident(chars[start..i].iter().collect()));
                continue;
            }
            // A raw string: `r`, `br` or `cr`, hashes, then a quote.
            if matches!(word.as_str(), "r" | "br" | "cr") && (at(i) == '#' || at(i) == '"') {
                let mut hashes = 0;
                while at(i) == '#' {
                    hashes += 1;
                    i += 1;
                }
                if at(i) == '"' {
                    i += 1;
                    let start = i;
                    loop {
                        if i >= chars.len() {
                            break;
                        }
                        if chars[i] == '"' && (0..hashes).all(|h| at(i + 1 + h) == '#') {
                            break;
                        }
                        i += 1;
                    }
                    tokens.push(Tok::Str(chars[start..i.min(chars.len())].iter().collect()));
                    i += 1 + hashes;
                    continue;
                }
            }
            tokens.push(Tok::Ident(word));
        } else if c == ':' && at(i + 1) == ':' {
            tokens.push(Tok::PathSep);
            i += 2;
        } else {
            tokens.push(Tok::Punct(c));
            i += 1;
        }
    }
    tokens
}

/// An out-of-line module declaration (`mod name;`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModDecl {
    pub(crate) name: String,
    /// Its `#[path = "..."]`, if any.
    pub(crate) path: Option<String>,
    /// Declared under `#[cfg(test)]`.
    pub(crate) test: bool,
    /// The inline modules (`mod a { mod b; }`) it is declared inside.
    pub(crate) inline_parents: Vec<String>,
}

/// What one file's non-test code contains.
#[derive(Debug, Default)]
pub(crate) struct Scan {
    /// String literal contents.
    pub(crate) literals: Vec<String>,
    /// Uses of a symbol operand: a `Symbol` or `ExactModuleSymbol` path
    /// segment after `::`, whatever names the enum (`MachOperand`,
    /// `X86ISelOperand`, `Self`, a type alias, `<MachOperand>`, a raw
    /// identifier), and the `.as_symbol` and `.as_exact_module_symbol`
    /// accessors: every construction of, and every read of the name in, a
    /// symbol operand spelled by path.
    pub(crate) mentions: usize,
    /// `::Symbol(` or `::ExactModuleSymbol(` directly followed by a string
    /// literal.
    pub(crate) literal_operands: usize,
    /// `use` items that import a `Symbol`/`ExactModuleSymbol` variant, or an
    /// operand enum's variants by glob or list, after which a bare `Symbol(..)`
    /// would hide a use from the count.
    pub(crate) aliases: usize,
    /// The file's out-of-line module declarations.
    pub(crate) modules: Vec<ModDecl>,
    /// The tokens of the file's non-test code, in order.
    pub(crate) tokens: Vec<Tok>,
}

/// The symbol-operand variants every operand enum spells.
const SYMBOL_VARIANTS: [&str; 2] = ["Symbol", "ExactModuleSymbol"];
/// The name accessors of the operand types.
const SYMBOL_ACCESSORS: [&str; 2] = ["as_symbol", "as_exact_module_symbol"];

/// The index just past the bracket that closes the one opening at `open`.
pub(crate) fn matching_close(tokens: &[Tok], open: usize) -> usize {
    let mut depth = 0usize;
    let mut j = open;
    while j < tokens.len() {
        match tokens[j] {
            Tok::Punct('(' | '[' | '{') => depth += 1,
            Tok::Punct(')' | ']' | '}') => {
                depth -= 1;
                if depth == 0 {
                    return j + 1;
                }
            }
            _ => {}
        }
        j += 1;
    }
    tokens.len()
}

/// The end of the item, statement, field or arm starting at `start`: after
/// its first brace block at depth zero, after its `;` or `,` at depth zero,
/// or before a closing bracket that ends its enclosing scope.
fn item_end(tokens: &[Tok], start: usize) -> usize {
    let mut depth = 0usize;
    let mut j = start;
    while j < tokens.len() {
        match tokens[j] {
            Tok::Punct('{') if depth == 0 => return matching_close(tokens, j),
            Tok::Punct('(' | '[' | '{') => depth += 1,
            Tok::Punct(')' | ']' | '}') => {
                if depth == 0 {
                    return j;
                }
                depth -= 1;
            }
            Tok::Punct(';' | ',') if depth == 0 => return j + 1,
            _ => {}
        }
        j += 1;
    }
    tokens.len()
}

/// `(name, index after the name)` of a `[vis] [clean] mod name` at `i`.
pub(crate) fn mod_name(tokens: &[Tok], mut i: usize) -> Option<(String, usize)> {
    if tokens.get(i) == Some(&Tok::Ident("pub".into())) {
        i += 1;
        if tokens.get(i) == Some(&Tok::Punct('(')) {
            i = matching_close(tokens, i);
        }
    }
    // Trust's checked Clean source modules are real module declarations too.
    // Consume the prefix WITH the declaration so its attributes are retained;
    // otherwise the next `mod` would be read again with its #[path] lost.
    if tokens.get(i) == Some(&Tok::Ident("clean".into())) {
        i += 1;
    }
    if tokens.get(i) != Some(&Tok::Ident("mod".into())) {
        return None;
    }
    match tokens.get(i + 1) {
        Some(Tok::Ident(name)) => Some((name.clone(), i + 2)),
        _ => None,
    }
}

/// A sufficient, conservative implication from a cfg expression to `test`.
/// Unknown predicates/negation/deep syntax never grant test-only status.
fn cfg_expr_requires_test(tokens: &[Tok], depth: usize) -> bool {
    if depth >= 64 {
        return false;
    }
    if let [Tok::Ident(name)] = tokens {
        return name == "test";
    }
    let Some(Tok::Ident(operator)) = tokens.first() else {
        return false;
    };
    if !matches!(operator.as_str(), "all" | "any")
        || tokens.get(1) != Some(&Tok::Punct('('))
        || tokens.last() != Some(&Tok::Punct(')'))
        || matching_close(tokens, 1) != tokens.len()
    {
        return false;
    }
    let end = tokens.len() - 1;
    let (mut start, mut nesting, mut arguments) = (2, 0usize, 0usize);
    let (mut any, mut all) = (false, true);
    for at in 2..=end {
        if at == end || (tokens[at] == Tok::Punct(',') && nesting == 0) {
            if start < at {
                let required = cfg_expr_requires_test(&tokens[start..at], depth + 1);
                any |= required;
                all &= required;
                arguments += 1;
            } else if at != end {
                return false;
            }
            start = at + 1;
        } else {
            match tokens[at] {
                Tok::Punct('(' | '[' | '{') => nesting += 1,
                Tok::Punct(')' | ']' | '}') => {
                    let Some(next) = nesting.checked_sub(1) else {
                        return false;
                    };
                    nesting = next;
                }
                _ => {}
            }
        }
    }
    nesting == 0 && arguments > 0 && if operator == "all" { any } else { all }
}

fn cfg_requires_test(body: &[Tok]) -> bool {
    body.len() >= 4
        && body.first() == Some(&Tok::Ident("cfg".into()))
        && body.get(1) == Some(&Tok::Punct('('))
        && body.last() == Some(&Tok::Punct(')'))
        && matching_close(body, 1) == body.len()
        && cfg_expr_requires_test(&body[2..body.len() - 1], 0)
}

fn require_explicit_clean_source(tokens: &[Tok], after: usize, path: Option<&str>) {
    if after >= 3 && tokens[after - 3] == Tok::Ident("clean".into()) {
        assert!(
            path.is_some() && tokens.get(after) == Some(&Tok::Punct(';')),
            "source census requires an explicit #[path] on a file-backed Clean module; no guessed Rust fallback"
        );
    }
}

/// Every out-of-line module declaration inside `tokens` (the body of a
/// removed inline test module), all test-only, with `parents` the inline
/// modules around them.
fn nested_test_modules(tokens: &[Tok], parents: &[String], out: &mut Vec<ModDecl>) {
    let mut i = 0;
    let mut path = None;
    while i < tokens.len() {
        if tokens[i] == Tok::Punct('#') && tokens.get(i + 1) == Some(&Tok::Punct('[')) {
            let end = matching_close(tokens, i + 1);
            if let [Tok::Ident(key), Tok::Punct('='), Tok::Str(value)] =
                &tokens[i + 2..end.saturating_sub(1)]
                && key == "path"
            {
                path = Some(value.clone());
            }
            i = end;
            continue;
        }
        if let Some((name, after)) = mod_name(tokens, i) {
            require_explicit_clean_source(tokens, after, path.as_deref());
            match tokens.get(after) {
                Some(Tok::Punct(';')) => {
                    out.push(ModDecl {
                        name,
                        path: path.take(),
                        test: true,
                        inline_parents: parents.to_vec(),
                    });
                    i = after + 1;
                    continue;
                }
                Some(Tok::Punct('{')) => {
                    let end = matching_close(tokens, after);
                    let mut inner = parents.to_vec();
                    inner.push(name);
                    nested_test_modules(&tokens[after + 1..end.saturating_sub(1)], &inner, out);
                    i = end;
                    path = None;
                    continue;
                }
                _ => {}
            }
        }
        path = None;
        i += 1;
    }
}

/// Scan one file's source.
pub(crate) fn scan(source: &str) -> Scan {
    let tokens = lex(source);
    let mut removed = vec![false; tokens.len()];
    let mut scan = Scan::default();
    // Inline modules entered: (name, brace depth inside them).
    let mut inline: Vec<(String, usize)> = Vec::new();
    let mut depth = 0usize;
    let mut i = 0;
    while i < tokens.len() {
        // Attributes, then the item they apply to.
        let attributes_start = i;
        let (mut cfg_test, mut path) = (false, None);
        while tokens.get(i) == Some(&Tok::Punct('#')) {
            let bang = usize::from(tokens.get(i + 1) == Some(&Tok::Punct('!')));
            if tokens.get(i + 1 + bang) != Some(&Tok::Punct('[')) {
                break;
            }
            let end = matching_close(&tokens, i + 1 + bang);
            let body = &tokens[i + 2 + bang..end.saturating_sub(1)];
            if cfg_requires_test(body) {
                cfg_test = true;
            }
            if let [Tok::Ident(key), Tok::Punct('='), Tok::Str(value)] = body
                && key == "path"
            {
                path = Some(value.clone());
            }
            i = end;
        }
        if i >= tokens.len() {
            break;
        }
        let declaration = mod_name(&tokens, i);
        if let Some((_, after)) = &declaration {
            require_explicit_clean_source(&tokens, *after, path.as_deref());
        }
        let inline_parents: Vec<String> = inline.iter().map(|(name, _)| name.clone()).collect();
        if cfg_test {
            let end = item_end(&tokens, i);
            if let Some((name, after)) = &declaration {
                match tokens.get(*after) {
                    Some(Tok::Punct(';')) => scan.modules.push(ModDecl {
                        name: name.clone(),
                        path,
                        test: true,
                        inline_parents,
                    }),
                    Some(Tok::Punct('{')) => {
                        let mut parents = inline_parents;
                        parents.push(name.clone());
                        nested_test_modules(
                            &tokens[after + 1..end.saturating_sub(1)],
                            &parents,
                            &mut scan.modules,
                        );
                    }
                    _ => {}
                }
            }
            removed[attributes_start..end]
                .iter_mut()
                .for_each(|r| *r = true);
            i = end;
            continue;
        }
        if let Some((name, after)) = declaration {
            match tokens.get(after) {
                Some(Tok::Punct(';')) => {
                    scan.modules.push(ModDecl {
                        name,
                        path,
                        test: false,
                        inline_parents,
                    });
                    // Past the whole declaration: `pub mod x;` must not be
                    // read a second time from its `mod`.
                    i = after + 1;
                    continue;
                }
                Some(Tok::Punct('{')) => {
                    inline.push((name, depth + 1));
                    depth += 1;
                    i = after + 1;
                    continue;
                }
                _ => {}
            }
        }
        match tokens[i] {
            Tok::Punct('{') => depth += 1,
            Tok::Punct('}') => {
                if inline.last().is_some_and(|(_, inside)| *inside == depth) {
                    inline.pop();
                }
                depth = depth.saturating_sub(1);
            }
            _ => {}
        }
        i += 1;
    }
    let kept: Vec<&Tok> = tokens
        .iter()
        .zip(&removed)
        .filter(|(_, removed)| !**removed)
        .map(|(token, _)| token)
        .collect();
    let mut in_use = false;
    for (k, token) in kept.iter().enumerate() {
        let next = |n: usize| kept.get(k + n).copied();
        let previous = k.checked_sub(1).and_then(|p| kept.get(p).copied());
        match token {
            Tok::Str(content) => scan.literals.push(content.clone()),
            Tok::Ident(word) if word == "use" && !in_use => in_use = true,
            Tok::Punct(';') => in_use = false,
            Tok::Ident(variant)
                if SYMBOL_VARIANTS.contains(&variant.as_str())
                    && previous == Some(&Tok::PathSep) =>
            {
                scan.mentions += 1;
                if in_use {
                    scan.aliases += 1;
                }
                if next(1) == Some(&Tok::Punct('(')) && matches!(next(2), Some(Tok::Str(_))) {
                    scan.literal_operands += 1;
                }
            }
            Tok::Ident(variant) if in_use && SYMBOL_VARIANTS.contains(&variant.as_str()) => {
                // `use ...::{Symbol, ..}`: imported by a list.
                scan.aliases += 1;
            }
            Tok::Ident(name)
                if in_use
                    && name.ends_with("Operand")
                    && next(1) == Some(&Tok::PathSep)
                    && matches!(next(2), Some(Tok::Punct('*' | '{'))) =>
            {
                scan.aliases += 1;
            }
            Tok::Punct('.')
                if matches!(next(1), Some(Tok::Ident(accessor))
                    if SYMBOL_ACCESSORS.contains(&accessor.as_str())) =>
            {
                scan.mentions += 1;
            }
            _ => {}
        }
    }
    scan.tokens = kept.into_iter().cloned().collect();
    scan
}

/// The file a module declaration in `parent` names.
pub(crate) fn module_file(parent: &Path, declaration: &ModDecl) -> PathBuf {
    let directory = parent.parent().expect("a source file has a directory");
    if let Some(path) = &declaration.path {
        return directory.join(path);
    }
    let file_name = parent
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_default();
    let mut base = if matches!(file_name, "lib.rs" | "main.rs" | "mod.rs") {
        directory.to_path_buf()
    } else {
        directory.join(parent.file_stem().expect("a file stem"))
    };
    for inline in &declaration.inline_parents {
        base = base.join(inline);
    }
    let flat = base.join(format!("{}.rs", declaration.name));
    if flat.exists() {
        flat
    } else {
        base.join(&declaration.name).join("mod.rs")
    }
}

/// Every `.rs` file under `directory`.
pub(crate) fn all_files(directory: &Path, files: &mut BTreeSet<PathBuf>) {
    for entry in std::fs::read_dir(directory).expect("read src") {
        let path = entry.expect("directory entry").path();
        if path.is_dir() {
            all_files(&path, files);
        } else if path.extension().is_some_and(|e| e == "rs") {
            files.insert(path);
        }
    }
}

/// The crate's compiled files under `root` (its `src/`), each with whether
/// it is test-only, walked from `lib.rs`. A file is production code when a
/// chain of declarations none of which is `#[cfg(test)]` reaches it, even if
/// it is also declared under `#[cfg(test)]` somewhere; it is test-only when
/// every chain to it passes a `#[cfg(test)]` declaration.
pub(crate) fn crate_files(root: &Path) -> BTreeMap<PathBuf, bool> {
    crate_files_from(&[root.join("lib.rs")])
}

/// [`crate_files`] walked from several crate-root files at once (a library's
/// `lib.rs`, a binary's `main.rs`, each `src/bin/*.rs`): a file is production
/// code when a non-test declaration chain from ANY root reaches it.
pub(crate) fn crate_files_from(roots: &[PathBuf]) -> BTreeMap<PathBuf, bool> {
    let mut declarations: BTreeMap<PathBuf, Vec<(PathBuf, bool)>> = BTreeMap::new();
    let mut pending = roots.to_vec();
    while let Some(path) = pending.pop() {
        if declarations.contains_key(&path) {
            continue;
        }
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        let children: Vec<(PathBuf, bool)> = scan(&text)
            .modules
            .iter()
            .map(|declaration| (module_file(&path, declaration), declaration.test))
            .collect();
        pending.extend(children.iter().map(|(child, _)| child.clone()));
        declarations.insert(path, children);
    }
    let mut production = BTreeSet::new();
    let mut pending = roots.to_vec();
    while let Some(path) = pending.pop() {
        if production.insert(path.clone()) {
            pending.extend(
                declarations[&path]
                    .iter()
                    .filter(|(_, test)| !test)
                    .map(|(child, _)| child.clone()),
            );
        }
    }
    declarations
        .into_keys()
        .map(|path| {
            let test = !production.contains(&path);
            (path, test)
        })
        .collect()
}

/// Every non-test file of the crate whose `src/` is `root`, relative to it,
/// with its scan. Fails if a source file under `root` is not reached by the
/// module walk (it could not be classified).
pub(crate) fn crate_scans(root: &Path) -> BTreeMap<String, Scan> {
    let files = crate_files(root);
    let mut on_disk = BTreeSet::new();
    all_files(root, &mut on_disk);
    let reached: BTreeSet<PathBuf> = files.keys().cloned().collect();
    assert_eq!(
        on_disk.difference(&reached).collect::<Vec<_>>(),
        Vec::<&PathBuf>::new(),
        "source files the module walk does not reach (declare them, or the scan cannot classify \
         them)"
    );
    files
        .into_iter()
        .filter(|(_, test)| !test)
        .map(|(path, _)| {
            let relative = path
                .strip_prefix(root)
                .expect("under src")
                .to_string_lossy()
                .replace('\\', "/");
            let text = std::fs::read_to_string(&path).expect("read source");
            let scan = scan(&text);
            assert!(
                !includes_source(&scan.tokens),
                "{relative} splices source text in with `include!`, which the scan does not \
                 follow; declare the code as a module instead"
            );
            (relative, scan)
        })
        .collect()
}

/// Whether `tokens` invoke `include!` (by any path), which splices another
/// file's text in as code. `include_str!` and `include_bytes!` yield data.
pub(crate) fn includes_source(tokens: &[Tok]) -> bool {
    tokens
        .windows(2)
        .any(|pair| pair[0] == Tok::Ident("include".into()) && pair[1] == Tok::Punct('!'))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct SourceTree(PathBuf);
    impl SourceTree {
        fn new(files: &[(&str, &str)]) -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "trust-source-scan-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            // Never reuse an unexpected pre-existing directory.
            std::fs::create_dir(&path).unwrap();
            let tree = Self(path);
            for (name, text) in files {
                let file = tree.0.join(name);
                std::fs::create_dir_all(file.parent().unwrap()).unwrap();
                std::fs::write(file, text).unwrap();
            }
            tree
        }
    }
    impl Drop for SourceTree {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn clean_module_retains_its_path_and_reads_the_actual_source() {
        let tree = SourceTree::new(&[
            ("src/lib.rs", "#[path = \"../proof.lean\"] clean mod proof;"),
            ("proof.lean", "def visible_clean_definition : Nat := 0"),
        ]);
        let files = crate_files(&tree.0.join("src"));
        let source = tree.0.join("src/../proof.lean");
        assert_eq!(files.len(), 2);
        assert_eq!(files.get(&source), Some(&false));
        assert!(
            scan(&std::fs::read_to_string(source).unwrap())
                .tokens
                .contains(&Tok::Ident("visible_clean_definition".into()))
        );
    }

    #[test]
    fn visible_and_nested_test_clean_modules_keep_attributes_and_scope() {
        let parsed = scan(
            r#"
            #[path = "public.lean"] pub(crate) clean mod public;
            #[cfg(test)] mod tests {
                #[path = "checked.lean"] pub clean mod checked;
            }
            fn live_after() {}
        "#,
        );
        assert_eq!(parsed.modules.len(), 2);
        assert_eq!(parsed.modules[0].path.as_deref(), Some("public.lean"));
        assert!(!parsed.modules[0].test);
        assert_eq!(parsed.modules[1].path.as_deref(), Some("checked.lean"));
        assert!(parsed.modules[1].test);
        assert_eq!(parsed.modules[1].inline_parents, ["tests"]);
        assert!(parsed.tokens.contains(&Tok::Ident("live_after".into())));
    }

    #[test]
    fn missing_clean_source_still_refuses_instead_of_being_excluded() {
        let tree = SourceTree::new(&[(
            "src/lib.rs",
            "#[path = \"missing.lean\"] clean mod missing;",
        )]);
        assert!(std::panic::catch_unwind(|| crate_files(&tree.0.join("src"))).is_err());
    }

    #[test]
    fn mixed_rust_clean_and_following_modules_are_all_traversed_once() {
        let tree = SourceTree::new(&[
            (
                "src/lib.rs",
                r#"
                #[path = "first.rs"] mod first;
                #[path = "proof.lean"] pub clean mod proof;
                mod last;
            "#,
            ),
            ("src/first.rs", "fn first() {}"),
            ("src/proof.lean", "def proof_value : Nat := 1"),
            ("src/last.rs", "fn last() {}"),
        ]);
        let files = crate_files(&tree.0.join("src"));
        assert_eq!(files.len(), 4);
        assert!(files.values().all(|test| !test));
        for name in ["lib.rs", "first.rs", "proof.lean", "last.rs"] {
            assert!(files.contains_key(&tree.0.join("src").join(name)));
        }
    }
    #[test]
    fn cfg_test_implication_keeps_every_mixed_or_unknown_production_arm() {
        for source in [
            "cfg(test)",
            "cfg(all(test, feature = \"verify\"))",
            "cfg(any(all(test, unix), all(test, windows)))",
            "cfg(all(feature = \"verify\", any(test, all(test, unix))))",
        ] {
            assert!(cfg_requires_test(&lex(source)), "{source}");
        }
        for source in [
            "cfg(unix)",
            "cfg(any(test, feature = \"verify\"))",
            "cfg(all(unix, feature = \"verify\"))",
            "cfg(not(test))",
            "cfg(any(test, not(unix)))",
            "cfg(all(test,, unix))",
            "cfg(all(test, unix)",
            "cfg(all())",
            "cfg(any())",
        ] {
            assert!(!cfg_requires_test(&lex(source)), "{source}");
        }
        let deep = format!("cfg({}test{})", "all(".repeat(65), ")".repeat(65));
        assert!(
            !cfg_requires_test(&lex(&deep)),
            "deep inference stays production"
        );
    }

    #[test]
    fn compound_test_tree_classification_requires_test_on_every_production_path() {
        let tree = SourceTree::new(&[
            (
                "src/lib.rs",
                r#"
                #[cfg(all(test, feature = "verify", target_arch = "aarch64"))]
                #[path = "only.rs"] mod only;
                #[cfg(any(test, feature = "verify"))]
                #[path = "mixed.rs"] mod mixed;
                #[cfg(all(test, unix))] #[path = "shared.rs"] mod test_path;
                #[path = "shared.rs"] mod production_path;
            "#,
            ),
            ("src/only.rs", "fn only() {}"),
            ("src/mixed.rs", "fn mixed() {}"),
            ("src/shared.rs", "fn shared() {}"),
        ]);
        let files = crate_files(&tree.0.join("src"));
        assert_eq!(files.get(&tree.0.join("src/only.rs")), Some(&true));
        assert_eq!(files.get(&tree.0.join("src/mixed.rs")), Some(&false));
        assert_eq!(files.get(&tree.0.join("src/shared.rs")), Some(&false));
    }

    #[test]
    fn unsupported_clean_lookup_refuses_even_with_a_decoy_rust_file() {
        let tree = SourceTree::new(&[
            ("src/lib.rs", "clean mod decoy;"),
            ("src/decoy.rs", "fn wrong_source() {}"),
            ("src/decoy.lean", "def actual_source : Nat := 0"),
        ]);
        assert!(std::panic::catch_unwind(|| crate_files(&tree.0.join("src"))).is_err());
        assert!(
            std::panic::catch_unwind(|| scan("#[path = \"x.lean\"] clean mod inline { }")).is_err()
        );
    }
}
