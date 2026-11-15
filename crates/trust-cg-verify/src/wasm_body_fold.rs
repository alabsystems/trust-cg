// trust-cg-verify/wasm_body_fold.rs - the checker of the wasm32 object lane's
// identical-body folding.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — "Binary Format";
//            WebAssembly tool-conventions `Linking.md` (the `linking` symbol
//            table and the `reloc.*` sections).
//
// WHAT THIS MODULE IS
//
// At O1 and above the wasm32 object lane folds identical function bodies
// (crates/trust-cg-codegen/src/wasm/lower.rs, `finish_with_body_folds`): the
// body of a FOLDED function that equals the body of a KEPT function becomes a
// forwarder, `local.get 0 .. local.get n-1; call <kept>; end`. The folded
// function keeps its index, its symbol, its exports and its table entries, so
// no function address changes and no two become equal; what changes is which
// bytes run when it is called.
//
// [`check_body_folds`] decides, over the object encoded BEFORE the fold and
// the object encoded AFTER it plus the witness (each `(folded, kept)` pair),
// with its own reader (nothing here reads `encode.rs` or `lower.rs`):
//
//   * every section of the two objects other than the code section and its
//     `reloc.CODE` section is byte-identical, in the same order, so types,
//     imports, function types, exports, elements, data, the symbol table and
//     every other relocation are unchanged (`reloc.CODE` itself may appear or
//     disappear, and always names the code section);
//   * the witness is well formed: every folded and kept index is a DEFINED
//     function, no function is folded twice, no kept function is folded, a
//     function is never folded onto itself, and both have one type;
//   * BEFORE the fold, the folded body equalled the kept body: the same
//     local declarations and instruction bytes, and the same relocations at
//     the same body-relative offsets with the same type, symbol and addend;
//   * AFTER the fold, the folded body is exactly the forwarder: no locals,
//     `local.get p` (minimal LEB128) for every parameter `p` of its type in
//     order, `call` with a five-byte padded LEB128 immediate that encodes
//     the kept index, and `end`, with exactly one relocation, a
//     `R_WASM_FUNCTION_INDEX_LEB` at that immediate whose symbol is a
//     DEFINED, non-weak function symbol of the kept function (so the linker
//     binds the call to the kept body itself, never to another object's
//     replacement of it);
//   * every other body, kept ones included, is byte-identical with
//     relocations identical at body-relative offsets;
//   * in the BEFORE object's call graph, the folded function is not
//     reachable from its kept function. A body has an edge to every defined
//     function one of its relocations names (a call, or an address it
//     takes); a body with a `R_WASM_TYPE_INDEX_LEB` or
//     `R_WASM_TABLE_NUMBER_LEB` relocation (an indirect call: a relocatable
//     object cannot encode `call_indirect` without them) has an edge to
//     every defined function whose address it could be handed: every one
//     whose address the object takes, by a relocation other than
//     `R_WASM_FUNCTION_INDEX_LEB` in any `reloc.*` section, and every one
//     that no symbol names or that some symbol names without
//     `WASM_SYM_BINDING_LOCAL` (another object or the host can name such a
//     function and take its address, so an indirect call here can land on
//     it even though this object never takes its address). So no cycle of
//     calls among this object's functions passes through a forwarder, an
//     indirect call included wherever the address it calls was taken (a
//     fold only shrinks this graph, every path after it maps onto one before
//     it), and such a recursion pays no forwarder frame per level.
//
// Together these say: calling a folded function with arguments `a` runs the
// kept body on `a`, which before the fold was the folded function's own body
// byte for byte with every relocation resolving to the same symbol, and
// returns its results; everything else in the object is unchanged.
//
// WHAT THIS MODULE IS NOT
//
// It says nothing about whether either body computes what its trust-ir
// function computes (the lane's other gates and the execution differentials
// cover that). Beyond the call-graph rule it does not reason about engine
// resources: the forwarder adds one call frame to each call of a folded
// function, and a cycle that runs through another object's function or the
// host and re-enters a folded function pays it per level.

/// `R_WASM_FUNCTION_INDEX_LEB`.
const R_FUNCTION_INDEX_LEB: u8 = 0;
/// `R_WASM_TYPE_INDEX_LEB`: its index is a type, not a symbol.
const R_TYPE_INDEX_LEB: u8 = 6;
/// `R_WASM_TABLE_NUMBER_LEB`.
const R_TABLE_NUMBER_LEB: u8 = 20;
/// `WASM_SYMBOL_TYPE_FUNCTION`.
const SYMTAB_FUNCTION: u8 = 0;
/// `WASM_SYM_BINDING_WEAK`.
const SYM_WEAK: u32 = 0x1;
/// `WASM_SYM_BINDING_LOCAL`.
const SYM_LOCAL: u32 = 0x2;
/// `WASM_SYM_UNDEFINED`.
const SYM_UNDEFINED: u32 = 0x10;
/// `WASM_SYM_EXPLICIT_NAME`.
const SYM_EXPLICIT_NAME: u32 = 0x40;
const OP_CALL: u8 = 0x10;
const OP_END: u8 = 0x0b;
const OP_LOCAL_GET: u8 = 0x20;

/// A byte cursor over one slice.
struct Rd<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Rd<'a> {
    fn new(b: &'a [u8]) -> Self {
        Self { b, p: 0 }
    }
    fn done(&self) -> bool {
        self.p >= self.b.len()
    }
    fn byte(&mut self, what: &str) -> Result<u8, String> {
        let v = *self
            .b
            .get(self.p)
            .ok_or_else(|| format!("truncated {what}"))?;
        self.p += 1;
        Ok(v)
    }
    fn take(&mut self, n: usize, what: &str) -> Result<&'a [u8], String> {
        let end = self
            .p
            .checked_add(n)
            .filter(|&e| e <= self.b.len())
            .ok_or_else(|| format!("truncated {what}"))?;
        let v = &self.b[self.p..end];
        self.p = end;
        Ok(v)
    }
    fn uleb(&mut self, what: &str) -> Result<u64, String> {
        let mut v: u64 = 0;
        for shift in (0..64).step_by(7) {
            let b = self.byte(what)?;
            v |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(v);
            }
        }
        Err(format!("overlong LEB128 in {what}"))
    }
    fn u32(&mut self, what: &str) -> Result<u32, String> {
        u32::try_from(self.uleb(what)?).map_err(|_| format!("{what} exceeds u32"))
    }
    fn sleb(&mut self, what: &str) -> Result<i64, String> {
        let mut v: i64 = 0;
        let mut shift = 0;
        loop {
            let b = self.byte(what)?;
            if shift < 64 {
                v |= i64::from(b & 0x7f) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                if shift < 64 && b & 0x40 != 0 {
                    v |= -1i64 << shift;
                }
                return Ok(v);
            }
            if shift >= 70 {
                return Err(format!("overlong LEB128 in {what}"));
            }
        }
    }
    fn name(&mut self, what: &str) -> Result<String, String> {
        let n = self.u32(what)? as usize;
        let raw = self.take(n, what)?;
        String::from_utf8(raw.to_vec()).map_err(|_| format!("{what} is not UTF-8"))
    }
}

/// One code-section entry: offsets into the code section's payload.
struct Body {
    /// First byte after the body's size.
    start: usize,
    /// One past its `end`.
    end: usize,
    /// First instruction byte.
    code_start: usize,
}

/// One relocation of `reloc.CODE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Rel {
    ty: u8,
    offset: u32,
    index: u32,
    addend: i64,
}

/// One symbol of the `linking` symbol table.
struct Sym {
    kind: u8,
    flags: u32,
    index: Option<u32>,
}

/// The parts of a relocatable object this checker reads.
struct Obj<'a> {
    /// Every section in file order: id, custom-section name, payload.
    sections: Vec<(u8, Option<String>, &'a [u8])>,
    /// Number of function imports (the low function index space).
    func_imports: u32,
    /// Parameter count of each type.
    type_params: Vec<u32>,
    /// Type index of each defined function.
    func_types: Vec<u32>,
    /// The code section's payload, and its index in file order.
    code: &'a [u8],
    code_section: Option<u32>,
    bodies: Vec<Body>,
    symbols: Vec<Sym>,
    code_relocs: Vec<Rel>,
    /// The relocations of every other `reloc.*` section (data, custom).
    other_relocs: Vec<Rel>,
    /// The section index `reloc.CODE` names.
    code_reloc_target: Option<u32>,
}

fn reloc_has_addend(ty: u8) -> Result<bool, String> {
    match ty {
        0 | 1 | 2 | 6 | 7 | 10 | 12 | 13 | 18 | 19 | 20 | 24 | 26 => Ok(false),
        3 | 4 | 5 | 8 | 9 | 11 | 14 | 15 | 16 | 17 | 21 | 22 | 23 | 25 => Ok(true),
        other => Err(format!("unknown relocation type {other}")),
    }
}

fn skip_limits(r: &mut Rd<'_>) -> Result<(), String> {
    let flags = r.byte("limits")?;
    r.uleb("limits min")?;
    if flags & 1 != 0 {
        r.uleb("limits max")?;
    }
    Ok(())
}

fn parse(bytes: &[u8]) -> Result<Obj<'_>, String> {
    let mut r = Rd::new(bytes);
    if r.take(8, "header")? != b"\0asm\x01\0\0\0" {
        return Err("not a wasm 1 binary".to_string());
    }
    let mut o = Obj {
        sections: Vec::new(),
        func_imports: 0,
        type_params: Vec::new(),
        func_types: Vec::new(),
        code: &[],
        code_section: None,
        bodies: Vec::new(),
        symbols: Vec::new(),
        code_relocs: Vec::new(),
        other_relocs: Vec::new(),
        code_reloc_target: None,
    };
    while !r.done() {
        let id = r.byte("section id")?;
        let size = r.u32("section size")? as usize;
        let payload = r.take(size, "section payload")?;
        let index = o.sections.len() as u32;
        let mut s = Rd::new(payload);
        let mut name = None;
        match id {
            0 => {
                let n = s.name("custom section name")?;
                if n == "linking" {
                    read_symbols(&mut s, &mut o.symbols)?;
                } else if n == "reloc.CODE" {
                    if o.code_reloc_target.is_some() {
                        return Err("two reloc.CODE sections".to_string());
                    }
                    o.code_reloc_target = Some(s.u32("reloc target")?);
                    read_relocs(&mut s, &mut o.code_relocs)?;
                } else if n.starts_with("reloc.") {
                    s.u32("reloc target")?;
                    read_relocs(&mut s, &mut o.other_relocs)?;
                }
                name = Some(n);
            }
            1 => {
                for _ in 0..s.u32("type count")? {
                    if s.byte("type form")? != 0x60 {
                        return Err("non-function type".to_string());
                    }
                    let params = s.u32("param count")?;
                    s.take(params as usize, "params")?;
                    let results = s.u32("result count")?;
                    s.take(results as usize, "results")?;
                    o.type_params.push(params);
                }
            }
            2 => {
                for _ in 0..s.u32("import count")? {
                    s.name("import module")?;
                    s.name("import name")?;
                    match s.byte("import kind")? {
                        0 => {
                            s.u32("import type")?;
                            o.func_imports += 1;
                        }
                        1 => {
                            s.byte("table type")?;
                            skip_limits(&mut s)?;
                        }
                        2 => skip_limits(&mut s)?,
                        3 => {
                            s.byte("global type")?;
                            s.byte("global mutability")?;
                        }
                        other => return Err(format!("unknown import kind {other}")),
                    }
                }
            }
            3 => {
                for _ in 0..s.u32("function count")? {
                    o.func_types.push(s.u32("function type")?);
                }
            }
            10 => {
                o.code = payload;
                o.code_section = Some(index);
                for _ in 0..s.u32("body count")? {
                    let len = s.u32("body size")? as usize;
                    let start = s.p;
                    let end = start
                        .checked_add(len)
                        .filter(|&e| e <= payload.len())
                        .ok_or("truncated body")?;
                    for _ in 0..s.u32("local groups")? {
                        s.u32("local count")?;
                        s.byte("local type")?;
                    }
                    let code_start = s.p;
                    if code_start >= end || payload[end - 1] != OP_END {
                        return Err("a body does not end with `end`".to_string());
                    }
                    s.p = end;
                    o.bodies.push(Body {
                        start,
                        end,
                        code_start,
                    });
                }
            }
            _ => {}
        }
        o.sections.push((id, name, payload));
    }
    if o.bodies.len() != o.func_types.len() {
        return Err("function and code sections disagree".to_string());
    }
    if !o.code_relocs.is_empty() && o.code_reloc_target != o.code_section {
        return Err("reloc.CODE does not name the code section".to_string());
    }
    Ok(o)
}

fn read_relocs(s: &mut Rd<'_>, out: &mut Vec<Rel>) -> Result<(), String> {
    for _ in 0..s.u32("reloc count")? {
        let ty = s.byte("reloc type")?;
        let offset = s.u32("reloc offset")?;
        let index = s.u32("reloc index")?;
        let addend = if reloc_has_addend(ty)? {
            s.sleb("reloc addend")?
        } else {
            0
        };
        out.push(Rel {
            ty,
            offset,
            index,
            addend,
        });
    }
    Ok(())
}

fn read_symbols(s: &mut Rd<'_>, out: &mut Vec<Sym>) -> Result<(), String> {
    if s.u32("linking version")? != 2 {
        return Err("linking section version is not 2".to_string());
    }
    while !s.done() {
        let sub = s.byte("linking subsection")?;
        let len = s.u32("linking subsection size")? as usize;
        let payload = s.take(len, "linking subsection")?;
        if sub != 8 {
            continue;
        }
        let mut t = Rd::new(payload);
        for _ in 0..t.u32("symbol count")? {
            let kind = t.byte("symbol kind")?;
            let flags = t.u32("symbol flags")?;
            let undefined = flags & SYM_UNDEFINED != 0;
            let index = match kind {
                1 => {
                    t.name("data symbol name")?;
                    if !undefined {
                        t.uleb("data segment")?;
                        t.uleb("data offset")?;
                        t.uleb("data size")?;
                    }
                    None
                }
                3 => Some(t.u32("section index")?),
                0 | 2 | 4 | 5 => {
                    let index = t.u32("symbol index")?;
                    if !undefined || flags & SYM_EXPLICIT_NAME != 0 {
                        t.name("symbol name")?;
                    }
                    Some(index)
                }
                other => return Err(format!("unknown symbol kind {other}")),
            };
            out.push(Sym { kind, flags, index });
        }
    }
    Ok(())
}

impl Obj<'_> {
    /// Body `b`'s bytes (local declarations, instructions, `end`).
    fn body_bytes(&self, b: usize) -> &[u8] {
        &self.code[self.bodies[b].start..self.bodies[b].end]
    }

    /// Body `b`'s relocations, with offsets relative to its first byte.
    fn body_relocs(&self, b: usize) -> Vec<Rel> {
        let body = &self.bodies[b];
        self.code_relocs
            .iter()
            .filter(|r| (body.start..body.end).contains(&(r.offset as usize)))
            .map(|r| Rel {
                offset: r.offset - body.start as u32,
                ..*r
            })
            .collect()
    }

    /// The defined function (its ordinal) relocation `r` names, if any.
    fn reloc_function(&self, r: &Rel) -> Result<Option<usize>, String> {
        if r.ty == R_TYPE_INDEX_LEB {
            return Ok(None);
        }
        let sym = self
            .symbols
            .get(r.index as usize)
            .ok_or_else(|| format!("relocation symbol {} is out of range", r.index))?;
        if sym.kind != SYMTAB_FUNCTION {
            return Ok(None);
        }
        Ok(sym
            .index
            .and_then(|f| f.checked_sub(self.func_imports))
            .map(|o| o as usize)
            .filter(|&o| o < self.bodies.len()))
    }

    /// The object's call graph over defined-function ordinals (module docs).
    fn call_graph(&self) -> Result<Vec<Vec<usize>>, String> {
        let mut address_taken = Vec::new();
        for r in &self.code_relocs {
            if r.ty != R_FUNCTION_INDEX_LEB
                && let Some(f) = self.reloc_function(r)?
            {
                address_taken.push(f);
            }
        }
        for r in &self.other_relocs {
            if let Some(f) = self.reloc_function(r)? {
                address_taken.push(f);
            }
        }
        // A function another object or the host can name: no symbol names
        // it, or some symbol names it without local binding.
        let mut named_local = vec![false; self.bodies.len()];
        let mut named_global = vec![false; self.bodies.len()];
        for sym in &self.symbols {
            if sym.kind != SYMTAB_FUNCTION || sym.flags & SYM_UNDEFINED != 0 {
                continue;
            }
            if let Some(o) = sym
                .index
                .and_then(|f| f.checked_sub(self.func_imports))
                .map(|o| o as usize)
                .filter(|&o| o < self.bodies.len())
            {
                if sym.flags & SYM_LOCAL != 0 {
                    named_local[o] = true;
                } else {
                    named_global[o] = true;
                }
            }
        }
        address_taken
            .extend((0..self.bodies.len()).filter(|&o| named_global[o] || !named_local[o]));
        let mut graph = Vec::with_capacity(self.bodies.len());
        for b in 0..self.bodies.len() {
            let relocs = self.body_relocs(b);
            let mut edges = Vec::new();
            for r in &relocs {
                if let Some(f) = self.reloc_function(r)? {
                    edges.push(f);
                }
            }
            if relocs
                .iter()
                .any(|r| r.ty == R_TYPE_INDEX_LEB || r.ty == R_TABLE_NUMBER_LEB)
            {
                edges.extend(&address_taken);
            }
            graph.push(edges);
        }
        Ok(graph)
    }
}

/// Whether `to` is reachable from `from` by a path of at least one edge.
fn reaches(graph: &[Vec<usize>], from: usize, to: usize) -> bool {
    let mut seen = vec![false; graph.len()];
    let mut stack = graph[from].clone();
    while let Some(n) = stack.pop() {
        if n == to {
            return true;
        }
        if !std::mem::replace(&mut seen[n], true) {
            stack.extend(&graph[n]);
        }
    }
    false
}

/// Check the identical-body folds `folds` (`(folded, kept)` function
/// indices) that turned the relocatable object `before` into `after` (module
/// docs). Returns the number of folds checked.
pub fn check_body_folds(
    before: &[u8],
    after: &[u8],
    folds: &[(u32, u32)],
) -> Result<usize, String> {
    let b = parse(before).map_err(|e| format!("the object before the fold: {e}"))?;
    let a = parse(after).map_err(|e| format!("the object after the fold: {e}"))?;
    if folds.is_empty() {
        return Err("no fold to check".to_string());
    }
    // Every section but the code section and its relocations is unchanged.
    let kept_sections = |o: &Obj<'_>| -> Vec<(u8, Option<String>, Vec<u8>)> {
        o.sections
            .iter()
            .filter(|(id, name, _)| *id != 10 && name.as_deref() != Some("reloc.CODE"))
            .map(|(id, name, p)| (*id, name.clone(), p.to_vec()))
            .collect()
    };
    if kept_sections(&b) != kept_sections(&a) {
        return Err("a section other than the code section or reloc.CODE changed".to_string());
    }
    // The same sections in the same order; `reloc.CODE` may appear or
    // disappear (a forwarder's call is relocated, a folded body's
    // relocations go), and wherever it is, it names the code section
    // (`parse`).
    let order = |o: &Obj<'_>| -> Vec<(u8, Option<String>)> {
        o.sections
            .iter()
            .filter(|(_, name, _)| name.as_deref() != Some("reloc.CODE"))
            .map(|(id, n, _)| (*id, n.clone()))
            .collect()
    };
    if order(&b) != order(&a) {
        return Err("the section order changed".to_string());
    }
    if b.bodies.len() != a.bodies.len() || b.func_imports != a.func_imports {
        return Err("the defined functions changed".to_string());
    }
    let defined = |f: u32| -> Result<usize, String> {
        f.checked_sub(b.func_imports)
            .map(|o| o as usize)
            .filter(|&o| o < b.bodies.len())
            .ok_or_else(|| format!("function {f} is not a defined function"))
    };
    let mut folded_of: Vec<Option<usize>> = vec![None; b.bodies.len()];
    for &(folded, kept) in folds {
        let fo = defined(folded)?;
        let ko = defined(kept)?;
        if fo == ko {
            return Err(format!("function {folded} is folded onto itself"));
        }
        if folded_of[fo].is_some() {
            return Err(format!("function {folded} is folded twice"));
        }
        if b.func_types[fo] != b.func_types[ko] {
            return Err(format!(
                "function {folded} (type {}) is folded onto function {kept} (type {})",
                b.func_types[fo], b.func_types[ko]
            ));
        }
        folded_of[fo] = Some(ko);
    }
    for &(_, kept) in folds {
        if folded_of[defined(kept)?].is_some() {
            return Err(format!("kept function {kept} is itself folded"));
        }
    }
    for (o, target) in folded_of.iter().enumerate() {
        let f = b.func_imports + o as u32;
        match *target {
            Some(ko) => {
                let kept = b.func_imports + ko as u32;
                if b.body_bytes(o) != b.body_bytes(ko) || b.body_relocs(o) != b.body_relocs(ko) {
                    return Err(format!(
                        "before the fold, function {f}'s body differs from function {kept}'s"
                    ));
                }
                check_forwarder(&a, o, ko)
                    .map_err(|e| format!("function {f} is not a forwarder to {kept}: {e}"))?;
            }
            None => {
                if b.body_bytes(o) != a.body_bytes(o) || b.body_relocs(o) != a.body_relocs(o) {
                    return Err(format!("function {f} is not folded, but its body changed"));
                }
            }
        }
    }
    // No forwarder lies on a cycle of calls among this object's functions.
    let graph = b.call_graph()?;
    for &(folded, kept) in folds {
        if reaches(&graph, defined(kept)?, defined(folded)?) {
            return Err(format!(
                "function {folded} is reachable from its kept function {kept}: its forwarder \
                 would lie on a cycle of calls among this object's functions"
            ));
        }
    }
    // Every relocation lies inside some body.
    let covered: usize = (0..a.bodies.len()).map(|o| a.body_relocs(o).len()).sum();
    if covered != a.code_relocs.len() {
        return Err("a code relocation lies outside every body".to_string());
    }
    Ok(folds.len())
}

/// Body `o` of `a` is exactly the forwarder to defined function `ko`.
fn check_forwarder(a: &Obj<'_>, o: usize, ko: usize) -> Result<(), String> {
    let kept = a.func_imports + ko as u32;
    let body = &a.bodies[o];
    let bytes = a.body_bytes(o);
    let ty = a.func_types[o] as usize;
    let params = *a
        .type_params
        .get(ty)
        .ok_or_else(|| format!("type {ty} is out of range"))?;
    let mut want = vec![0u8]; // no local declarations
    for p in 0..params {
        want.push(OP_LOCAL_GET);
        let mut v = p;
        loop {
            let byte = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                want.push(byte);
                break;
            }
            want.push(byte | 0x80);
        }
    }
    want.push(OP_CALL);
    let immediate = want.len();
    let mut v = kept;
    for i in 0..5 {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        want.push(if i < 4 { byte | 0x80 } else { byte });
    }
    want.push(OP_END);
    if body.code_start != body.start + 1 || bytes != want.as_slice() {
        return Err(format!(
            "its body is {bytes:02x?}, the forwarder is {want:02x?}"
        ));
    }
    match a.body_relocs(o).as_slice() {
        [r] if r.ty == R_FUNCTION_INDEX_LEB && r.offset as usize == immediate && r.addend == 0 => {
            let sym = a
                .symbols
                .get(r.index as usize)
                .ok_or_else(|| format!("relocation symbol {} is out of range", r.index))?;
            if sym.kind != SYMTAB_FUNCTION
                || sym.index != Some(kept)
                || sym.flags & (SYM_UNDEFINED | SYM_WEAK) != 0
            {
                return Err(format!(
                    "the call's symbol {} is not a defined, non-weak symbol of function {kept} \
                     (kind {}, index {:?}, flags 0x{:x})",
                    r.index, sym.kind, sym.index, sym.flags
                ));
            }
            Ok(())
        }
        other => Err(format!(
            "its relocations are {other:?}, not one function-index relocation at the call"
        )),
    }
}

#[cfg(test)]
#[path = "wasm_body_fold_tests.rs"]
mod tests;
