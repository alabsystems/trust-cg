// trust-cg-llvm-import / vector.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// LANE-SCALARIZING VECTOR IMPORT.
//
// clang at `-O2`/`-O3` runs the loop and SLP vectorizers, so its IR carries
// fixed-width vector types (`<4 x i32>`, `<2 x double>`, …) and the vector
// element operations `insertelement` / `extractelement` / `shufflevector`.
// Before this module the importer rejected every one of them, which is why
// only 31 of the 69 clang-importable SingleSource programs and 1049 of the
// 1455 gcc-c-torture programs survived `-O2` (against 64 / 1118 at `-O1`).
//
// # Why scalarize instead of lowering to NEON
//
// trust-cg's machine IR does model 128-bit vectors, but only the CONTRACTED
// shapes `<16 x i8>`, `<8 x i16>`, `<4 x i32>`, `<2 x i64>`, `<4 x f32>`,
// `<2 x f64>` (plus the 64-bit `<8 x i8>` / `<1 x i64>` D-register pair). The
// measured `-O3` census over the failing corpus contains NINETEEN distinct
// shapes, a majority of which are wider than a machine register
// (`<4 x double>`, `<8 x float>`, `<8 x i32>`, `<16 x i32>`, `<12 x i32>`,
// `<4 x i64>`, `<16 x float>`). Mapping the contracted subset natively while
// failing closed on the rest would leave most of the corpus unimported AND
// would require auditing every (op x shape) pair against the encoder.
//
// Lane scalarization instead has a single, uniform correctness argument that
// holds for EVERY width: LLVM defines all of the arithmetic, logic, compare,
// cast and select operations on vectors ELEMENTWISE, so replacing one vector
// operation by `N` independent scalar operations of the element type is a
// semantics-preserving rewrite by definition, not by construction. The
// element-manipulation instructions collapse to pure SSA renaming, which is
// why the expansion emits ZERO instructions for `extractelement`,
// `insertelement` and `shufflevector`.
//
// # How it works
//
// `expand` is a source-to-source rewrite: it takes ONE textual vector
// instruction and returns the list of SCALAR textual instructions that
// replace it, which the caller feeds straight back into the ordinary scalar
// parser. Nothing about constant parsing, flag stripping, FP-literal decoding
// or instruction construction is duplicated — the scalar paths that are
// already exercised by the `-O1` corpus do all of the work, so a lane of a
// vector `fadd` is built by exactly the code that builds a scalar `fadd`.
//
// A vector SSA value `%v` of type `<N x T>` is represented by the `N` scalar
// SSA names `%v#v0 … %v#v{N-1}`, where lane `i` is the element at BYTE OFFSET
// `i * sizeof(T)` — LLVM's little-endian lane order, which is the target's
// order on both AArch64 and x86-64. `#` cannot occur in an unquoted LLVM
// identifier and a quoted one always carries its quotes into the name, so a
// synthesized lane name can never collide with a real one.
//
// # Fail-closed discipline
//
// Every construct without a proven lane-wise expansion returns `Err(reason)`,
// which the caller turns into a clean `Error::Unsupported`. That includes:
//
//   * scalable vectors (`<vscale x N x T>`) — no fixed lane count;
//   * a dynamic (non-constant) `insertelement` / `extractelement` index;
//   * `bitcast` that re-lanes (`<4 x i32>` -> `<2 x i64>`, `<2 x i32>` -> `i64`);
//   * `<N x i1>` in memory — an i1 vector is BIT-packed, so its lanes are not
//     at byte offsets and a per-lane byte load would read the wrong bits;
//   * `volatile` / `atomic` vector memory — splitting one volatile access into
//     `N` is observable, so it is refused rather than approximated;
//   * vector `getelementptr` (gather/scatter), vector returns and arguments;
//   * every `@llvm.*` intrinsic outside the explicitly enumerated elementwise
//     and reduction tables (`llvm.masked.*`, `llvm.vp.*`,
//     `llvm.experimental.*`, `llvm.vector.reduce.fmax`, …).
//
// The backstop is `mentions_vector_type`: if `expand` declines an instruction
// that nonetheless carries a vector type anywhere, it is refused instead of
// being handed to a scalar path that might misread it.

/// Upper bound on the lane count of a single vector value. Scalarization is
/// linear in the lane count, so an unbounded width would turn one instruction
/// into an unbounded basic block; the corpus maximum is 64 (`<64 x i8>` in
/// gcc-c-torture `20000801-1`). Anything wider fails closed.
const MAX_LANES: u32 = 64;

/// The scalar instructions one vector instruction expands into, plus the
/// operand-token aliases the caller must register first.
pub(crate) struct Expansion {
    /// `(result_name_without_percent, instruction_text)` in emission order.
    pub insts: Vec<(Option<String>, String)>,
    /// `(ssa_name_without_percent, replacement_operand_token)`. Registered
    /// BEFORE `insts` are parsed. This is how `extractelement` /
    /// `insertelement` / `shufflevector` cost nothing: the result lane simply
    /// resolves to the source lane's token (which may itself be a literal).
    pub aliases: Vec<(String, String)>,
}

impl Expansion {
    fn new() -> Self {
        Self {
            insts: Vec::new(),
            aliases: Vec::new(),
        }
    }
}

/// Lane `i` of vector SSA name `base`, spelled without the leading `%`.
fn lane_name(base: &str, i: u32) -> String {
    format!("{base}#v{i}")
}

/// Parse a vector type token `<N x T>`.
///
/// * `Ok(None)` — not a vector type.
/// * `Ok(Some((elem, lanes)))` — a fixed-width vector.
/// * `Err(_)` — a vector type that cannot be scalarized (scalable, zero-lane,
///   or wider than [`MAX_LANES`]).
pub(crate) fn vector_shape(t: &str) -> Result<Option<(String, u32)>, String> {
    let t = t.trim();
    let Some(inner) = t.strip_prefix('<').and_then(|s| s.strip_suffix('>')) else {
        return Ok(None);
    };
    let inner = inner.trim();
    // `<{ i32, i8 }>` is a PACKED STRUCT, not a vector.
    if inner.starts_with('{') {
        return Ok(None);
    }
    if inner.starts_with("vscale") {
        return Err(format!("scalable vector type `{t}` (no fixed lane count)"));
    }
    let (count, elem) = inner
        .split_once(" x ")
        .ok_or_else(|| format!("vector type `{t}` is not spelled `<N x T>`"))?;
    let lanes: u32 = count
        .trim()
        .parse()
        .map_err(|_| format!("vector type `{t}` has a non-numeric lane count"))?;
    if lanes == 0 {
        return Err(format!("zero-lane vector type `{t}`"));
    }
    if lanes > MAX_LANES {
        return Err(format!(
            "vector type `{t}` exceeds the {MAX_LANES}-lane scalarization bound"
        ));
    }
    Ok(Some((elem.trim().to_string(), lanes)))
}

/// True when `s` carries a `<N x ...>` vector type token anywhere outside a
/// string literal. Used as the fail-closed backstop for instructions this
/// module declines to expand.
pub(crate) fn mentions_vector_type(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut in_quote = false;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => in_quote = !in_quote,
            b'<' if !in_quote => {
                let rest = &s[i + 1..];
                let trimmed = rest.trim_start();
                if trimmed.starts_with("vscale") {
                    return true;
                }
                let digits: String = trimmed.chars().take_while(char::is_ascii_digit).collect();
                if !digits.is_empty() && trimmed[digits.len()..].trim_start().starts_with("x ") {
                    return true;
                }
            }
            _ => {}
        }
        i += 1;
    }
    false
}

/// The textual scalar constant that fills a lane of a `zeroinitializer`.
fn zero_literal(elem: &str) -> &'static str {
    match elem {
        "half" | "bfloat" | "float" | "double" | "fp128" | "x86_fp80" | "ppc_fp128" => {
            "0.000000e+00"
        }
        "i1" => "false",
        "ptr" => "null",
        _ => "0",
    }
}

/// True for the element types whose lanes sit at `i * sizeof(T)` byte offsets,
/// i.e. those for which a vector load/store may be split into scalar accesses.
/// `i1` is excluded because an `<N x i1>` value is BIT-packed in memory.
fn elem_is_byte_addressable(elem: &str) -> bool {
    matches!(
        elem,
        "i8" | "i16" | "i32" | "i64" | "i128" | "half" | "float" | "double" | "ptr"
    )
}

/// Split `s` at the first top-level ` to ` (the cast separator), respecting
/// bracket nesting so `<4 x i32>` is never cut apart.
fn split_cast_to(s: &str) -> Option<(&str, &str)> {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'[' | b'(' | b'{' | b'<' => depth += 1,
            b']' | b')' | b'}' | b'>' => depth -= 1,
            b' ' if depth == 0 && s[i..].starts_with(" to ") => {
                return Some((s[..i].trim(), s[i + 4..].trim()));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Flag tokens LLVM may print between an opcode (or predicate) and its type.
/// Every one is a poison-refinement or fast-math hint that the scalar paths
/// already accept and drop; they are carried through verbatim so each lane is
/// parsed by exactly the same code as the original.
fn is_flag_token(t: &str) -> bool {
    matches!(
        t,
        "nsw"
            | "nuw"
            | "exact"
            | "disjoint"
            | "samesign"
            | "nneg"
            | "fast"
            | "nnan"
            | "ninf"
            | "nsz"
            | "arcp"
            | "contract"
            | "afn"
            | "reassoc"
    )
}

/// Peel the leading flag tokens off `s`, returning `(flags_with_trailing_space,
/// remainder)`.
fn peel_flags(s: &str) -> (String, &str) {
    let mut flags = String::new();
    let mut rest = s.trim_start();
    loop {
        let next = rest.split_whitespace().next().unwrap_or("");
        if next.is_empty() || !is_flag_token(next) {
            break;
        }
        flags.push_str(next);
        flags.push(' ');
        rest = rest[next.len()..].trim_start();
    }
    (flags, rest)
}

/// Split a top-level comma list (`a, b, c`), respecting brackets and strings.
fn split_top_level(s: &str) -> Vec<String> {
    crate::parser::split_aggregate_elems(s)
}

/// `<ty> <value>` -> `(ty, value)`, with `<N x T>` kept whole.
fn split_ty_val(s: &str) -> Result<(String, String), String> {
    crate::parser::split_leading_type(s)
        .map(|(t, v)| (t.to_string(), v.to_string()))
        .ok_or_else(|| format!("expected `<ty> <value>` in `{s}`"))
}

/// The per-lane operand tokens for a vector-typed operand.
///
/// Handles every constant spelling clang emits for a vector: an SSA name, a
/// `<...>` element list, `zeroinitializer`, `undef` / `poison`, and the
/// LLVM-19 `splat (T v)` shorthand. Non-constant, non-name operands (an inline
/// constant expression, say) fail closed.
fn lane_ops(tok: &str, elem: &str, lanes: u32) -> Result<Vec<String>, String> {
    let tok = tok.trim();
    let n = lanes as usize;
    if let Some(name) = tok.strip_prefix('%') {
        return Ok((0..lanes)
            .map(|i| format!("%{}", lane_name(name, i)))
            .collect());
    }
    if tok == "zeroinitializer" {
        return Ok(vec![zero_literal(elem).to_string(); n]);
    }
    if tok == "undef" || tok == "poison" {
        return Ok(vec!["undef".to_string(); n]);
    }
    if let Some(inner) = tok
        .strip_prefix("splat (")
        .and_then(|s| s.strip_suffix(')'))
    {
        let (ty, val) = split_ty_val(inner)?;
        if ty != elem {
            return Err(format!(
                "vector splat element type `{ty}` does not match `{elem}`"
            ));
        }
        return Ok(vec![val; n]);
    }
    if tok.starts_with('<') && tok.ends_with('>') {
        let inner = &tok[1..tok.len() - 1];
        let elems = split_top_level(inner);
        if elems.len() != n {
            return Err(format!(
                "vector constant `{tok}` has {} elements, expected {n}",
                elems.len()
            ));
        }
        let mut out = Vec::with_capacity(n);
        for e in elems {
            let (ty, val) = split_ty_val(&e)?;
            if ty != elem {
                return Err(format!(
                    "vector constant element type `{ty}` does not match `{elem}`"
                ));
            }
            out.push(val);
        }
        return Ok(out);
    }
    Err(format!("vector operand `{tok}`"))
}

/// Read a non-negative constant lane index from an operand clause `<ty> <val>`.
fn const_lane_index(clause: &str) -> Result<u32, String> {
    let (_, val) = split_ty_val(clause)?;
    let v = crate::parser::parse_int_literal(&val)
        .ok_or_else(|| format!("dynamic vector lane index `{val}`"))?;
    u32::try_from(v).map_err(|_| format!("out-of-range vector lane index `{val}`"))
}

/// Expand one textual vector instruction into its scalar replacement.
///
/// * `Ok(None)` — `rest` carries no vector type; the caller's ordinary scalar
///   dispatch handles it unchanged.
/// * `Ok(Some(expansion))` — the scalar instructions to parse instead.
/// * `Err(reason)` — the instruction IS vector-typed and has no proven
///   lane-wise expansion. The caller must fail closed.
///
/// `uid` must be unique within the function; it names the temporaries that
/// address lanes 1.. of a vector load/store.
pub(crate) fn expand(
    result: Option<&str>,
    rest: &str,
    uid: u32,
) -> Result<Option<Expansion>, String> {
    let opcode = rest.split_whitespace().next().unwrap_or("");
    let tail = rest[opcode.len()..].trim_start();

    let expansion = match opcode {
        "add" | "sub" | "mul" | "and" | "or" | "xor" | "shl" | "lshr" | "ashr" | "sdiv"
        | "udiv" | "srem" | "urem" | "fadd" | "fsub" | "fmul" | "fdiv" | "frem" => {
            expand_binop(opcode, tail, result)?
        }
        "fneg" | "freeze" => expand_unary(opcode, tail, result)?,
        "icmp" | "fcmp" => expand_cmp(opcode, tail, result)?,
        "select" => expand_select(tail, result)?,
        "trunc" | "zext" | "sext" | "fptrunc" | "fpext" | "fptoui" | "fptosi" | "uitofp"
        | "sitofp" | "ptrtoint" | "inttoptr" | "bitcast" => expand_cast(opcode, tail, result)?,
        "load" => expand_load(tail, result, uid)?,
        "store" => expand_store(tail, uid)?,
        "phi" => expand_phi(tail, result)?,
        "insertelement" => Some(expand_insertelement(tail, result)?),
        "extractelement" => Some(expand_extractelement(tail, result)?),
        "shufflevector" => Some(expand_shufflevector(tail, result)?),
        "call" => expand_call(tail, result)?,
        _ => None,
    };

    if expansion.is_none() && mentions_vector_type(rest) {
        // Fail-closed backstop: a vector type reached an opcode with no
        // lane-wise expansion. Never hand it to a scalar path.
        return Err(format!("vector-typed `{opcode}`"));
    }
    Ok(expansion)
}

fn expand_binop(
    opcode: &str,
    tail: &str,
    result: Option<&str>,
) -> Result<Option<Expansion>, String> {
    let (flags, rest) = peel_flags(tail);
    let (ty, operands) = split_ty_val(rest)?;
    let Some((elem, lanes)) = vector_shape(&ty)? else {
        return Ok(None);
    };
    let name = result.ok_or_else(|| format!("vector `{opcode}` without result"))?;
    let (lhs, rhs) = crate::parser::split_comma(&operands)
        .ok_or_else(|| format!("vector `{opcode}`: expected `a, b`"))?;
    let l = lane_ops(&lhs, &elem, lanes)?;
    let r = lane_ops(&rhs, &elem, lanes)?;
    let mut e = Expansion::new();
    for i in 0..lanes as usize {
        e.insts.push((
            Some(lane_name(name, i as u32)),
            format!("{opcode} {flags}{elem} {}, {}", l[i], r[i]),
        ));
    }
    Ok(Some(e))
}

fn expand_unary(
    opcode: &str,
    tail: &str,
    result: Option<&str>,
) -> Result<Option<Expansion>, String> {
    let (flags, rest) = peel_flags(tail);
    let (ty, operand) = split_ty_val(rest)?;
    let Some((elem, lanes)) = vector_shape(&ty)? else {
        return Ok(None);
    };
    let name = result.ok_or_else(|| format!("vector `{opcode}` without result"))?;
    let a = lane_ops(&operand, &elem, lanes)?;
    let mut e = Expansion::new();
    for i in 0..lanes as usize {
        e.insts.push((
            Some(lane_name(name, i as u32)),
            format!("{opcode} {flags}{elem} {}", a[i]),
        ));
    }
    Ok(Some(e))
}

fn expand_cmp(opcode: &str, tail: &str, result: Option<&str>) -> Result<Option<Expansion>, String> {
    // `icmp [samesign] <pred> <ty> a, b` / `fcmp [fmf] <pred> <ty> a, b`.
    let (flags, rest) = peel_flags(tail);
    let (pred, rest) = rest
        .split_once(char::is_whitespace)
        .ok_or_else(|| format!("`{opcode}`: missing predicate"))?;
    let (ty, operands) = split_ty_val(rest.trim())?;
    let Some((elem, lanes)) = vector_shape(&ty)? else {
        return Ok(None);
    };
    let name = result.ok_or_else(|| format!("vector `{opcode}` without result"))?;
    let (lhs, rhs) = crate::parser::split_comma(&operands)
        .ok_or_else(|| format!("vector `{opcode}`: expected `a, b`"))?;
    let l = lane_ops(&lhs, &elem, lanes)?;
    let r = lane_ops(&rhs, &elem, lanes)?;
    let mut e = Expansion::new();
    for i in 0..lanes as usize {
        e.insts.push((
            Some(lane_name(name, i as u32)),
            format!("{opcode} {flags}{pred} {elem} {}, {}", l[i], r[i]),
        ));
    }
    Ok(Some(e))
}

fn expand_select(tail: &str, result: Option<&str>) -> Result<Option<Expansion>, String> {
    let (flags, rest) = peel_flags(tail);
    let parts = split_top_level(rest);
    if parts.len() != 3 {
        return Ok(None);
    }
    let (cond_ty, cond_val) = split_ty_val(&parts[0])?;
    let (a_ty, a_val) = split_ty_val(&parts[1])?;
    let (b_ty, b_val) = split_ty_val(&parts[2])?;
    let Some((elem, lanes)) = vector_shape(&a_ty)? else {
        // A scalar-result select whose CONDITION is somehow a vector is
        // ill-formed; `mentions_vector_type` catches it at the caller.
        return Ok(None);
    };
    if a_ty != b_ty {
        return Err(format!(
            "vector `select` arm types `{a_ty}` and `{b_ty}` differ"
        ));
    }
    let name = result.ok_or_else(|| "vector `select` without result".to_string())?;
    let cond = match vector_shape(&cond_ty)? {
        Some((cond_elem, cond_lanes)) => {
            if cond_elem != "i1" || cond_lanes != lanes {
                return Err(format!(
                    "vector `select` condition type `{cond_ty}` is not `<{lanes} x i1>`"
                ));
            }
            lane_ops(&cond_val, "i1", lanes)?
        }
        None => {
            if cond_ty != "i1" {
                return Err(format!("vector `select` condition type `{cond_ty}`"));
            }
            vec![cond_val; lanes as usize]
        }
    };
    let a = lane_ops(&a_val, &elem, lanes)?;
    let b = lane_ops(&b_val, &elem, lanes)?;
    let mut e = Expansion::new();
    for i in 0..lanes as usize {
        e.insts.push((
            Some(lane_name(name, i as u32)),
            format!(
                "select {flags}i1 {}, {elem} {}, {elem} {}",
                cond[i], a[i], b[i]
            ),
        ));
    }
    Ok(Some(e))
}

fn expand_cast(
    opcode: &str,
    tail: &str,
    result: Option<&str>,
) -> Result<Option<Expansion>, String> {
    let (flags, rest) = peel_flags(tail);
    let (src_part, dst_ty) =
        split_cast_to(rest).ok_or_else(|| format!("`{opcode}`: missing ` to <ty>`"))?;
    let (src_ty, src_val) = split_ty_val(src_part)?;
    let src_vec = vector_shape(&src_ty)?;
    let dst_vec = vector_shape(dst_ty)?;
    match (src_vec, dst_vec) {
        (None, None) => Ok(None),
        (Some((src_elem, src_lanes)), Some((dst_elem, dst_lanes))) => {
            if src_lanes != dst_lanes {
                // A re-laning bitcast (`<4 x i32>` -> `<2 x i64>`) is a
                // bit-level reinterpretation ACROSS lanes; there is no
                // lane-wise scalar equivalent.
                return Err(format!(
                    "`{opcode}` changes the lane count (`{src_ty}` -> `{dst_ty}`)"
                ));
            }
            let name = result.ok_or_else(|| format!("vector `{opcode}` without result"))?;
            let a = lane_ops(&src_val, &src_elem, src_lanes)?;
            let mut e = Expansion::new();
            for i in 0..src_lanes as usize {
                e.insts.push((
                    Some(lane_name(name, i as u32)),
                    format!("{opcode} {flags}{src_elem} {} to {dst_elem}", a[i]),
                ));
            }
            Ok(Some(e))
        }
        _ => Err(format!(
            "`{opcode}` between vector and scalar (`{src_ty}` -> `{dst_ty}`)"
        )),
    }
}

fn expand_load(tail: &str, result: Option<&str>, uid: u32) -> Result<Option<Expansion>, String> {
    let (qualified, tail) = match tail.strip_prefix("volatile ") {
        Some(r) => (true, r.trim_start()),
        None => match tail.strip_prefix("atomic ") {
            Some(r) => (true, r.trim_start()),
            None => (false, tail),
        },
    };
    let (ty, rest) = crate::parser::split_comma(tail)
        .ok_or_else(|| "`load`: expected `<ty>, ptr %p`".to_string())?;
    let Some((elem, lanes)) = vector_shape(&ty)? else {
        return Ok(None);
    };
    if qualified {
        // Splitting one volatile/atomic access into N is OBSERVABLE.
        return Err("volatile / atomic vector load".to_string());
    }
    if !elem_is_byte_addressable(&elem) {
        return Err(format!(
            "vector load of `{ty}`: element type `{elem}` is not byte-addressable \
             (an i1 vector is bit-packed in memory)"
        ));
    }
    let name = result.ok_or_else(|| "vector `load` without result".to_string())?;
    let ptr_part = crate::parser::split_comma(&rest)
        .map(|(head, _)| head)
        .unwrap_or_else(|| rest.trim().to_string());
    let (_, ptr_tok) = split_ty_val(&ptr_part)?;
    let mut e = Expansion::new();
    for i in 0..lanes {
        let addr = if i == 0 {
            ptr_tok.clone()
        } else {
            let tmp = format!("#vt{uid}p{i}");
            e.insts.push((
                Some(tmp.clone()),
                format!("getelementptr inbounds {elem}, ptr {ptr_tok}, i64 {i}"),
            ));
            format!("%{tmp}")
        };
        e.insts
            .push((Some(lane_name(name, i)), format!("load {elem}, ptr {addr}")));
    }
    Ok(Some(e))
}

fn expand_store(tail: &str, uid: u32) -> Result<Option<Expansion>, String> {
    let (qualified, tail) = match tail.strip_prefix("volatile ") {
        Some(r) => (true, r.trim_start()),
        None => match tail.strip_prefix("atomic ") {
            Some(r) => (true, r.trim_start()),
            None => (false, tail),
        },
    };
    let (val_part, rest) = crate::parser::split_comma(tail)
        .ok_or_else(|| "`store`: expected `<ty> <val>, ptr %p`".to_string())?;
    let (ty, val_tok) = split_ty_val(&val_part)?;
    let Some((elem, lanes)) = vector_shape(&ty)? else {
        return Ok(None);
    };
    if qualified {
        return Err("volatile / atomic vector store".to_string());
    }
    if !elem_is_byte_addressable(&elem) {
        return Err(format!(
            "vector store of `{ty}`: element type `{elem}` is not byte-addressable \
             (an i1 vector is bit-packed in memory)"
        ));
    }
    let ptr_part = crate::parser::split_comma(&rest)
        .map(|(head, _)| head)
        .unwrap_or_else(|| rest.trim().to_string());
    let (_, ptr_tok) = split_ty_val(&ptr_part)?;
    let vals = lane_ops(&val_tok, &elem, lanes)?;
    let mut e = Expansion::new();
    for i in 0..lanes {
        let addr = if i == 0 {
            ptr_tok.clone()
        } else {
            let tmp = format!("#vt{uid}p{i}");
            e.insts.push((
                Some(tmp.clone()),
                format!("getelementptr inbounds {elem}, ptr {ptr_tok}, i64 {i}"),
            ));
            format!("%{tmp}")
        };
        e.insts.push((
            None,
            format!("store {elem} {}, ptr {addr}", vals[i as usize]),
        ));
    }
    Ok(Some(e))
}

fn expand_phi(tail: &str, result: Option<&str>) -> Result<Option<Expansion>, String> {
    let (flags, rest) = peel_flags(tail);
    let _ = flags;
    let (ty, incoming_str) = split_ty_val(rest)?;
    let Some((elem, lanes)) = vector_shape(&ty)? else {
        return Ok(None);
    };
    let name = result.ok_or_else(|| "vector `phi` without result".to_string())?;
    // `[ v, %pred ], [ v, %pred ]` — one clause per incoming edge.
    let clauses = split_top_level(&incoming_str);
    let mut per_edge: Vec<(Vec<String>, String)> = Vec::with_capacity(clauses.len());
    for clause in &clauses {
        let body = clause
            .trim()
            .strip_prefix('[')
            .and_then(|s| s.trim().strip_suffix(']'))
            .ok_or_else(|| format!("vector `phi`: malformed incoming `{clause}`"))?;
        let (val, pred) = crate::parser::split_comma(body)
            .ok_or_else(|| "vector `phi`: expected `[ value, %pred ]`".to_string())?;
        per_edge.push((lane_ops(&val, &elem, lanes)?, pred));
    }
    let mut e = Expansion::new();
    for i in 0..lanes as usize {
        let body = per_edge
            .iter()
            .map(|(vals, pred)| format!("[ {}, {} ]", vals[i], pred))
            .collect::<Vec<_>>()
            .join(", ");
        e.insts.push((
            Some(lane_name(name, i as u32)),
            format!("phi {elem} {body}"),
        ));
    }
    Ok(Some(e))
}

fn expand_insertelement(tail: &str, result: Option<&str>) -> Result<Expansion, String> {
    let parts = split_top_level(tail);
    if parts.len() != 3 {
        return Err("`insertelement` expects `<vec>, <elem>, <idx>`".to_string());
    }
    let (vec_ty, vec_val) = split_ty_val(&parts[0])?;
    let (elem, lanes) = vector_shape(&vec_ty)?
        .ok_or_else(|| format!("`insertelement` source type `{vec_ty}` is not a vector"))?;
    let (ins_ty, ins_val) = split_ty_val(&parts[1])?;
    if ins_ty != elem {
        return Err(format!(
            "`insertelement` element type `{ins_ty}` does not match `{elem}`"
        ));
    }
    let idx = const_lane_index(&parts[2])?;
    if idx >= lanes {
        // LLVM defines an out-of-range index as poison for the whole result.
        return Err(format!(
            "`insertelement` index {idx} is out of range for `{vec_ty}`"
        ));
    }
    let name = result.ok_or_else(|| "`insertelement` without result".to_string())?;
    let src = lane_ops(&vec_val, &elem, lanes)?;
    let mut e = Expansion::new();
    for i in 0..lanes {
        let tok = if i == idx {
            ins_val.clone()
        } else {
            src[i as usize].clone()
        };
        e.aliases.push((lane_name(name, i), tok));
    }
    Ok(e)
}

fn expand_extractelement(tail: &str, result: Option<&str>) -> Result<Expansion, String> {
    let parts = split_top_level(tail);
    if parts.len() != 2 {
        return Err("`extractelement` expects `<vec>, <idx>`".to_string());
    }
    let (vec_ty, vec_val) = split_ty_val(&parts[0])?;
    let (elem, lanes) = vector_shape(&vec_ty)?
        .ok_or_else(|| format!("`extractelement` source type `{vec_ty}` is not a vector"))?;
    let idx = const_lane_index(&parts[1])?;
    if idx >= lanes {
        return Err(format!(
            "`extractelement` index {idx} is out of range for `{vec_ty}`"
        ));
    }
    let name = result.ok_or_else(|| "`extractelement` without result".to_string())?;
    let src = lane_ops(&vec_val, &elem, lanes)?;
    let mut e = Expansion::new();
    e.aliases
        .push((name.to_string(), src[idx as usize].clone()));
    Ok(e)
}

fn expand_shufflevector(tail: &str, result: Option<&str>) -> Result<Expansion, String> {
    let parts = split_top_level(tail);
    if parts.len() != 3 {
        return Err("`shufflevector` expects `<vec>, <vec>, <mask>`".to_string());
    }
    let (a_ty, a_val) = split_ty_val(&parts[0])?;
    let (b_ty, b_val) = split_ty_val(&parts[1])?;
    let (mask_ty, mask_val) = split_ty_val(&parts[2])?;
    let (elem, lanes) = vector_shape(&a_ty)?
        .ok_or_else(|| format!("`shufflevector` operand type `{a_ty}` is not a vector"))?;
    if a_ty != b_ty {
        return Err(format!(
            "`shufflevector` operand types `{a_ty}` and `{b_ty}` differ"
        ));
    }
    let (_, out_lanes) = vector_shape(&mask_ty)?
        .ok_or_else(|| format!("`shufflevector` mask type `{mask_ty}` is not a vector"))?;
    let name = result.ok_or_else(|| "`shufflevector` without result".to_string())?;
    let a = lane_ops(&a_val, &elem, lanes)?;
    let b = lane_ops(&b_val, &elem, lanes)?;
    // The mask is always a vector of i32 constants (or undef/poison lanes).
    let mask = lane_ops(&mask_val, "i32", out_lanes)?;
    let mut e = Expansion::new();
    for (i, m) in mask.iter().enumerate() {
        let tok = if m == "undef" || m == "poison" {
            // An undef mask lane makes the result lane undef; binding it to a
            // concrete existing lane REFINES undef, which is always sound.
            a[0].clone()
        } else {
            let sel = crate::parser::parse_int_literal(m)
                .ok_or_else(|| format!("`shufflevector` mask element `{m}` is not constant"))?;
            let sel = u32::try_from(sel)
                .map_err(|_| format!("`shufflevector` mask element `{m}` is negative"))?;
            if sel < lanes {
                a[sel as usize].clone()
            } else if sel < lanes * 2 {
                b[(sel - lanes) as usize].clone()
            } else {
                return Err(format!(
                    "`shufflevector` mask element {sel} is out of range for `{a_ty}`"
                ));
            }
        };
        e.aliases.push((lane_name(name, i as u32), tok));
    }
    Ok(e)
}

/// Elementwise `@llvm.*` families: the vector form applies the scalar form to
/// each lane independently. Every operand and the result must carry the SAME
/// vector shape — the entry is refused otherwise, so shape-mixing forms such
/// as `llvm.powi` (`<4 x float>, i32`) and `llvm.ctlz` (`<4 x i32>, i1`) never
/// take this path.
const ELEMENTWISE_INTRINSICS: &[&str] = &[
    "fmuladd",
    "fma",
    "sqrt",
    "fabs",
    "floor",
    "ceil",
    "trunc",
    "rint",
    "nearbyint",
    "round",
    "roundeven",
    "copysign",
    "minnum",
    "maxnum",
    "sin",
    "cos",
    "tan",
    "asin",
    "acos",
    "atan",
    "sinh",
    "cosh",
    "tanh",
    "exp",
    "exp2",
    "log",
    "log2",
    "log10",
    "pow",
    "smin",
    "smax",
    "umin",
    "umax",
    "bswap",
    "ctpop",
    "fshl",
    "fshr",
];

/// `llvm.vector.reduce.<op>` families that are exactly a left-to-right scalar
/// fold. The integer ones are associative so any order is exact; the FP ones
/// are the SEQUENTIAL (ordered) reductions by definition, and the fold below
/// is that definition. `fmax`/`fmin` are deliberately absent: their NaN and
/// signed-zero behaviour does not follow from a naive fold.
fn reduce_scalar_op(family: &str) -> Option<&'static str> {
    match family {
        "add" => Some("add"),
        "mul" => Some("mul"),
        "and" => Some("and"),
        "or" => Some("or"),
        "xor" => Some("xor"),
        "fadd" => Some("fadd"),
        "fmul" => Some("fmul"),
        _ => None,
    }
}

/// Strip a trailing `.v<N><suffix>` overload segment, returning
/// `(prefix, suffix, lanes)`: `llvm.fmuladd.v2f64` -> `("llvm.fmuladd", "f64", 2)`.
fn split_vector_overload(name: &str) -> Option<(&str, &str, u32)> {
    let (prefix, last) = name.rsplit_once('.')?;
    let rest = last.strip_prefix('v')?;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    if digits.is_empty() {
        return None;
    }
    let lanes: u32 = digits.parse().ok()?;
    let suffix = &rest[digits.len()..];
    if suffix.is_empty() {
        return None;
    }
    Some((prefix, suffix, lanes))
}

fn expand_call(tail: &str, result: Option<&str>) -> Result<Option<Expansion>, String> {
    // A call with no vector anywhere is not ours. Checking FIRST keeps the
    // explicit-function-type spelling `call i32 (ptr, ...) @printf(…)` — whose
    // first `(` belongs to the TYPE, not the argument list — off this path
    // entirely.
    if !mentions_vector_type(tail) {
        return Ok(None);
    }
    let (ret_ty, rest) = split_ty_val(tail)?;
    let rest = rest.trim();
    let open = rest
        .find('(')
        .ok_or_else(|| format!("vector-typed call `{tail}`: no argument list"))?;
    let callee = rest[..open].trim();
    let close = rest
        .rfind(')')
        .ok_or_else(|| format!("vector-typed call `{tail}`: unterminated argument list"))?;
    let args = split_top_level(&rest[open + 1..close]);
    let ret_vec = vector_shape(&ret_ty)?;
    if !callee.starts_with("@llvm.") {
        return Err(format!(
            "vector-typed call to `{callee}` (no vector ABI is modelled)"
        ));
    }
    let iname = callee.trim_start_matches('@');

    // --- `llvm.vector.reduce.<op>` --------------------------------------
    if let Some(after) = iname.strip_prefix("llvm.vector.reduce.") {
        let family = after.split('.').next().unwrap_or("");
        let op = reduce_scalar_op(family)
            .ok_or_else(|| format!("vector reduction intrinsic `{iname}`"))?;
        let is_fp = op.starts_with('f');
        let name = result.ok_or_else(|| format!("`{iname}` without result"))?;
        // Ordered FP reductions take a leading scalar start value; the
        // integer ones take only the vector.
        let (start, vec_clause) = if is_fp {
            if args.len() != 2 {
                return Err(format!("`{iname}` expects (start, vector)"));
            }
            let (sty, sval) = split_ty_val(&args[0])?;
            if sty != ret_ty {
                return Err(format!("`{iname}` start type `{sty}` != result `{ret_ty}`"));
            }
            (Some(sval), &args[1])
        } else {
            if args.len() != 1 {
                return Err(format!("`{iname}` expects (vector)"));
            }
            (None, &args[0])
        };
        let (vty, vval) = split_ty_val(vec_clause)?;
        let (elem, lanes) = vector_shape(&vty)?
            .ok_or_else(|| format!("`{iname}` operand type `{vty}` is not a vector"))?;
        if elem != ret_ty {
            return Err(format!(
                "`{iname}` element type `{elem}` != result type `{ret_ty}`"
            ));
        }
        let src = lane_ops(&vval, &elem, lanes)?;
        let mut e = Expansion::new();
        let seeded_from_start = start.is_some();
        let mut acc = match start {
            Some(s) => s,
            None => {
                // No start value: seed the fold with lane 0.
                let first = src[0].clone();
                if lanes == 1 {
                    e.aliases.push((name.to_string(), first));
                    return Ok(Some(e));
                }
                first
            }
        };
        let first_lane = if seeded_from_start { 0 } else { 1 };
        for i in first_lane..lanes {
            let last = i + 1 == lanes;
            let dest = if last {
                name.to_string()
            } else {
                format!("{name}#vr{i}")
            };
            e.insts.push((
                Some(dest.clone()),
                format!("{op} {elem} {acc}, {}", src[i as usize]),
            ));
            acc = format!("%{dest}");
        }
        if e.insts.is_empty() {
            // A single-lane ordered FP reduction still needs the start fold.
            e.insts.push((
                Some(name.to_string()),
                format!("{op} {elem} {acc}, {}", src[0]),
            ));
        }
        return Ok(Some(e));
    }

    // --- elementwise families -------------------------------------------
    let (prefix, suffix, overload_lanes) = split_vector_overload(iname)
        .ok_or_else(|| format!("vector intrinsic `{iname}` (no `.vN<ty>` overload)"))?;
    let family = prefix.strip_prefix("llvm.").unwrap_or(prefix);
    if !ELEMENTWISE_INTRINSICS.contains(&family) {
        return Err(format!("vector intrinsic `{iname}` (not elementwise)"));
    }
    let (elem, lanes) =
        ret_vec.ok_or_else(|| format!("`{iname}` result type `{ret_ty}` is not a vector"))?;
    if lanes != overload_lanes {
        return Err(format!(
            "`{iname}` overload lane count {overload_lanes} != result lane count {lanes}"
        ));
    }
    let name = result.ok_or_else(|| format!("`{iname}` without result"))?;
    let mut arg_lanes: Vec<Vec<String>> = Vec::with_capacity(args.len());
    for a in &args {
        let (aty, aval) = split_ty_val(a)?;
        if aty != ret_ty {
            return Err(format!(
                "`{iname}` argument type `{aty}` differs from result `{ret_ty}` \
                 (not a uniform elementwise shape)"
            ));
        }
        arg_lanes.push(lane_ops(&aval, &elem, lanes)?);
    }
    let scalar_callee = format!("@{prefix}.{suffix}");
    let mut e = Expansion::new();
    for i in 0..lanes as usize {
        let arg_text = arg_lanes
            .iter()
            .map(|la| format!("{elem} {}", la[i]))
            .collect::<Vec<_>>()
            .join(", ");
        e.insts.push((
            Some(lane_name(name, i as u32)),
            format!("call {elem} {scalar_callee}({arg_text})"),
        ));
    }
    Ok(Some(e))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn texts(result: Option<&str>, rest: &str) -> Vec<String> {
        let e = expand(result, rest, 0).unwrap().unwrap();
        e.insts
            .iter()
            .map(|(r, t)| match r {
                Some(n) => format!("%{n} = {t}"),
                None => t.clone(),
            })
            .collect()
    }

    #[test]
    fn scalar_instructions_are_left_alone() {
        assert!(
            expand(Some("r"), "add nsw i32 %a, %b", 0)
                .unwrap()
                .is_none()
        );
        assert!(expand(None, "store i32 %a, ptr %p", 0).unwrap().is_none());
        assert!(expand(Some("r"), "load i32, ptr %p", 0).unwrap().is_none());
    }

    #[test]
    fn packed_struct_type_is_not_a_vector() {
        assert_eq!(vector_shape("<{ i32, i8 }>").unwrap(), None);
        assert!(!mentions_vector_type("%r = load <{ i32, i8 }>, ptr %p"));
    }

    #[test]
    fn binop_expands_lanewise_and_keeps_flags() {
        assert_eq!(
            texts(Some("r"), "add nsw <4 x i32> %a, %b"),
            vec![
                "%r#v0 = add nsw i32 %a#v0, %b#v0",
                "%r#v1 = add nsw i32 %a#v1, %b#v1",
                "%r#v2 = add nsw i32 %a#v2, %b#v2",
                "%r#v3 = add nsw i32 %a#v3, %b#v3",
            ]
        );
    }

    #[test]
    fn constant_vector_operands_expand_elementwise() {
        assert_eq!(
            texts(Some("r"), "mul <2 x i64> %a, <i64 3, i64 5>"),
            vec!["%r#v0 = mul i64 %a#v0, 3", "%r#v1 = mul i64 %a#v1, 5",]
        );
        assert_eq!(
            texts(Some("r"), "fadd <2 x double> %a, zeroinitializer"),
            vec![
                "%r#v0 = fadd double %a#v0, 0.000000e+00",
                "%r#v1 = fadd double %a#v1, 0.000000e+00",
            ]
        );
        assert_eq!(
            texts(Some("r"), "add <2 x i32> %a, splat (i32 7)"),
            vec!["%r#v0 = add i32 %a#v0, 7", "%r#v1 = add i32 %a#v1, 7"]
        );
    }

    #[test]
    fn compare_and_select_thread_the_mask_lanewise() {
        assert_eq!(
            texts(Some("c"), "icmp samesign slt <2 x i32> %a, %b"),
            vec![
                "%c#v0 = icmp samesign slt i32 %a#v0, %b#v0",
                "%c#v1 = icmp samesign slt i32 %a#v1, %b#v1",
            ]
        );
        assert_eq!(
            texts(Some("r"), "select <2 x i1> %c, <2 x i32> %a, <2 x i32> %b"),
            vec![
                "%r#v0 = select i1 %c#v0, i32 %a#v0, i32 %b#v0",
                "%r#v1 = select i1 %c#v1, i32 %a#v1, i32 %b#v1",
            ]
        );
        // A SCALAR condition broadcasts to every lane.
        assert_eq!(
            texts(Some("r"), "select i1 %c, <2 x i32> %a, <2 x i32> %b"),
            vec![
                "%r#v0 = select i1 %c, i32 %a#v0, i32 %b#v0",
                "%r#v1 = select i1 %c, i32 %a#v1, i32 %b#v1",
            ]
        );
    }

    #[test]
    fn load_and_store_address_each_lane_by_element_offset() {
        assert_eq!(
            texts(Some("r"), "load <3 x i32>, ptr %p, align 16"),
            vec![
                "%r#v0 = load i32, ptr %p",
                "%#vt0p1 = getelementptr inbounds i32, ptr %p, i64 1",
                "%r#v1 = load i32, ptr %#vt0p1",
                "%#vt0p2 = getelementptr inbounds i32, ptr %p, i64 2",
                "%r#v2 = load i32, ptr %#vt0p2",
            ]
        );
        assert_eq!(
            texts(None, "store <2 x double> %v, ptr %p, align 16"),
            vec![
                "store double %v#v0, ptr %p",
                "%#vt0p1 = getelementptr inbounds double, ptr %p, i64 1",
                "store double %v#v1, ptr %#vt0p1",
            ]
        );
    }

    #[test]
    fn bit_packed_and_qualified_memory_fails_closed() {
        assert!(expand(Some("r"), "load <4 x i1>, ptr %p", 0).is_err());
        assert!(expand(None, "store <4 x i1> %v, ptr %p", 0).is_err());
        assert!(expand(Some("r"), "load volatile <4 x i32>, ptr %p", 0).is_err());
        assert!(expand(None, "store volatile <4 x i32> %v, ptr %p", 0).is_err());
    }

    #[test]
    fn element_ops_are_pure_renaming() {
        let e = expand(Some("r"), "extractelement <4 x i32> %v, i64 2", 0)
            .unwrap()
            .unwrap();
        assert!(e.insts.is_empty());
        assert_eq!(e.aliases, vec![("r".to_string(), "%v#v2".to_string())]);

        let e = expand(Some("r"), "insertelement <2 x i32> %v, i32 %x, i64 1", 0)
            .unwrap()
            .unwrap();
        assert!(e.insts.is_empty());
        assert_eq!(
            e.aliases,
            vec![
                ("r#v0".to_string(), "%v#v0".to_string()),
                ("r#v1".to_string(), "%x".to_string()),
            ]
        );

        let e = expand(
            Some("r"),
            "shufflevector <2 x i32> %a, <2 x i32> %b, <4 x i32> <i32 0, i32 3, i32 undef, i32 1>",
            0,
        )
        .unwrap()
        .unwrap();
        assert!(e.insts.is_empty());
        assert_eq!(
            e.aliases,
            vec![
                ("r#v0".to_string(), "%a#v0".to_string()),
                ("r#v1".to_string(), "%b#v1".to_string()),
                // undef mask lane refines to an existing lane
                ("r#v2".to_string(), "%a#v0".to_string()),
                ("r#v3".to_string(), "%a#v1".to_string()),
            ]
        );
    }

    #[test]
    fn splat_shuffle_of_a_constant_vector_yields_literals() {
        let e = expand(
            Some("r"),
            "shufflevector <2 x i32> <i32 9, i32 8>, <2 x i32> poison, <2 x i32> zeroinitializer",
            0,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            e.aliases,
            vec![
                ("r#v0".to_string(), "9".to_string()),
                ("r#v1".to_string(), "9".to_string()),
            ]
        );
    }

    #[test]
    fn dynamic_lane_index_fails_closed() {
        assert!(expand(Some("r"), "extractelement <4 x i32> %v, i32 %i", 0).is_err());
        assert!(expand(Some("r"), "insertelement <4 x i32> %v, i32 %x, i32 %i", 0).is_err());
        assert!(expand(Some("r"), "extractelement <4 x i32> %v, i32 9", 0).is_err());
    }

    #[test]
    fn relaning_bitcast_fails_closed() {
        assert!(expand(Some("r"), "bitcast <4 x i32> %a to <2 x i64>", 0).is_err());
        assert!(expand(Some("r"), "bitcast <2 x i32> %a to i64", 0).is_err());
        assert!(expand(Some("r"), "bitcast i64 %a to <2 x i32>", 0).is_err());
        // Same-lane-count bitcast IS exact lane-by-lane.
        assert_eq!(
            texts(Some("r"), "bitcast <2 x float> %a to <2 x i32>"),
            vec![
                "%r#v0 = bitcast float %a#v0 to i32",
                "%r#v1 = bitcast float %a#v1 to i32",
            ]
        );
    }

    #[test]
    fn widening_casts_expand_lanewise() {
        assert_eq!(
            texts(Some("r"), "sext <2 x i16> %a to <2 x i32>"),
            vec![
                "%r#v0 = sext i16 %a#v0 to i32",
                "%r#v1 = sext i16 %a#v1 to i32",
            ]
        );
        assert_eq!(
            texts(Some("r"), "zext nneg <2 x i8> %a to <2 x i64>"),
            vec![
                "%r#v0 = zext nneg i8 %a#v0 to i64",
                "%r#v1 = zext nneg i8 %a#v1 to i64",
            ]
        );
    }

    #[test]
    fn phi_expands_one_per_lane() {
        assert_eq!(
            texts(
                Some("r"),
                "phi <2 x i32> [ %a, %bb1 ], [ zeroinitializer, %bb2 ]"
            ),
            vec![
                "%r#v0 = phi i32 [ %a#v0, %bb1 ], [ 0, %bb2 ]",
                "%r#v1 = phi i32 [ %a#v1, %bb1 ], [ 0, %bb2 ]",
            ]
        );
    }

    #[test]
    fn elementwise_intrinsics_expand_to_the_scalar_overload() {
        assert_eq!(
            texts(
                Some("r"),
                "call <2 x double> @llvm.fmuladd.v2f64(<2 x double> %a, <2 x double> %b, <2 x double> %c)"
            ),
            vec![
                "%r#v0 = call double @llvm.fmuladd.f64(double %a#v0, double %b#v0, double %c#v0)",
                "%r#v1 = call double @llvm.fmuladd.f64(double %a#v1, double %b#v1, double %c#v1)",
            ]
        );
        assert_eq!(
            texts(
                Some("r"),
                "call <2 x i32> @llvm.smax.v2i32(<2 x i32> %a, <2 x i32> %b)"
            ),
            vec![
                "%r#v0 = call i32 @llvm.smax.i32(i32 %a#v0, i32 %b#v0)",
                "%r#v1 = call i32 @llvm.smax.i32(i32 %a#v1, i32 %b#v1)",
            ]
        );
    }

    #[test]
    fn ordered_fp_reduction_folds_left_to_right() {
        assert_eq!(
            texts(
                Some("r"),
                "call double @llvm.vector.reduce.fadd.v4f64(double %s, <4 x double> %v)"
            ),
            vec![
                "%r#vr0 = fadd double %s, %v#v0",
                "%r#vr1 = fadd double %r#vr0, %v#v1",
                "%r#vr2 = fadd double %r#vr1, %v#v2",
                "%r = fadd double %r#vr2, %v#v3",
            ]
        );
        assert_eq!(
            texts(
                Some("r"),
                "call i32 @llvm.vector.reduce.xor.v4i32(<4 x i32> %v)"
            ),
            vec![
                "%r#vr1 = xor i32 %v#v0, %v#v1",
                "%r#vr2 = xor i32 %r#vr1, %v#v2",
                "%r = xor i32 %r#vr2, %v#v3",
            ]
        );
    }

    #[test]
    fn unmodelled_vector_intrinsics_fail_closed() {
        assert!(
            expand(
                None,
                "call void @llvm.masked.store.v4f64.p0(<4 x double> %a, ptr %p, i32 8, <4 x i1> %m)",
                0
            )
            .is_err()
        );
        assert!(
            expand(
                Some("r"),
                "call double @llvm.vector.reduce.fmax.v4f64(<4 x double> %v)",
                0
            )
            .is_err()
        );
        assert!(
            expand(
                Some("r"),
                "call <4 x float> @llvm.powi.v4f32.i32(<4 x float> %a, i32 %n)",
                0
            )
            .is_err()
        );
        assert!(expand(Some("r"), "call <4 x i32> @user_fn(<4 x i32> %a)", 0).is_err());
    }

    #[test]
    fn scalable_and_oversized_vectors_fail_closed() {
        assert!(expand(Some("r"), "add <vscale x 4 x i32> %a, %b", 0).is_err());
        assert!(expand(Some("r"), "add <128 x i8> %a, %b", 0).is_err());
    }

    #[test]
    fn unmodelled_vector_opcodes_hit_the_backstop() {
        assert!(expand(Some("r"), "ret <4 x i32> %a", 0).is_err());
        assert!(
            expand(
                Some("r"),
                "getelementptr inbounds i32, <2 x ptr> %p, i64 1",
                0
            )
            .is_err()
        );
        assert!(expand(Some("r"), "extractvalue { <4 x i32>, i1 } %a, 0", 0).is_err());
        assert!(expand(Some("r"), "va_arg <4 x i32> %a, <4 x i32>", 0).is_err());
    }
}
