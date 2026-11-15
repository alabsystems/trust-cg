// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared TrustIR corpus and C driver for the AArch64 niche-encoded enum
//! native controls (`e2e_aarch64_niche_enum.rs` on Darwin,
//! `e2e_aarch64_niche_enum_linux.rs` on Linux).
//!
//! Every enum carries the producer layout rustc gives it, so its C spelling is
//! the plain scalar or struct the niche lives in:
//!
//! ```text
//! Option<&u64>        uint64_t *   NULL = None   (payload spelled Ptr and Ref)
//! Option<NonZeroU32>  uint32_t     0 = None
//! Option<bool>        uint8_t      0/1 = Some(false/true), 2 = None
//! Option<char>        uint32_t     0x110000 = None
//! Tri                 uint8_t      0/1 = Data(false/true), 2 = Low, 3 = High
//! Wrapped             uint8_t      254 = Low, 0 = High, else Data(byte)
//! ```
//!
//! For each Option shape the corpus reads the discriminant (`ExtractField`
//! element 0), switches on it and reads the payload, and constructs either
//! variant from constants plus a runtime payload `InsertField`. This corpus's
//! `Ref`-typed `Option<&u64>` (`nq`) is read only; the `Ptr`-typed one (`nr`)
//! is also constructed. `Tri` selects and stores a complete fieldless variant
//! at runtime. Canonical `InsertField` cannot rewrite an enum discriminant;
//! the original invalid retagging shape is retained as a refusal fixture. The
//! driver's oracle is the C meaning of each spelling above; for the byte lanes
//! it additionally checks all 256 byte images against the niche formula
//! written in C. `oc_byte0` reads byte 0 as if it were a tag, and the driver
//! requires it to DISAGREE with the oracle, which shows the oracle can tell a
//! tag read from a niche decode. Execution evidence, not proof.
#![allow(dead_code)]

use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::{
    CastOp, Constant, Endianness, EnumDef, EnumId, EnumVariant, FieldDef, Module, StructDef,
    StructId, StructPassingPolicy, StructRepr, SwitchCase, TargetInfo, Ty,
};
use trust_ir_build::{ModuleBuilder, validate_module};

/// Exact driver output for a complete, successful run.
pub const EXPECTED_PASS: &str = "PASS 882 niche checks";

/// Every function the corpus defines, in definition order.
pub const SYMBOLS: &[&str] = &[
    "nr_disc",
    "nr_classify",
    "nr_make",
    "nq_disc",
    "nq_classify",
    "nz_disc",
    "nz_classify",
    "nz_make",
    "nb_disc",
    "nb_classify",
    "nb_make",
    "nc_disc",
    "nc_classify",
    "nc_make",
    "tri_disc",
    "tri_classify",
    "tri_make",
    "tri_set_disc",
    "wrapped_disc",
    "oc_byte0",
];

const OPTION_REF: u32 = 0;
const OPTION_NONZERO: u32 = 1;
const OPTION_BOOL: u32 = 2;
const OPTION_CHAR: u32 = 3;
const TRI: u32 = 4;
const WRAPPED: u32 = 5;
const OPTION_REF_TYPED: u32 = 6;
const NONZERO_STRUCT: u32 = 0;

fn target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: Vec::new(),
    }
}

#[allow(clippy::too_many_arguments)]
fn niche_enum(
    id: u32,
    name: &str,
    variants: Vec<EnumVariant>,
    (untagged, start, end): (u32, u32, u32),
    niche_start: u128,
    niche_ty: EnumTagRepr,
    (size, align): (u64, u64),
    offsets: Vec<Vec<u64>>,
) -> EnumDef {
    EnumDef {
        id: EnumId::new(id),
        name: name.into(),
        origin: None,
        variants,
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: untagged,
                niche_variants_start: start,
                niche_variants_end: end,
                niche_start,
                niche_offset: 0,
                niche_ty,
            },
            size,
            align,
            variant_field_offsets: offsets,
        }),
    }
}

fn option(id: u32, name: &str, payload: Ty, start: u128, repr: EnumTagRepr, size: u64) -> EnumDef {
    niche_enum(
        id,
        name,
        vec![variant("None", vec![]), variant("Some", vec![payload])],
        (1, 0, 0),
        start,
        repr,
        (size, size),
        vec![vec![], vec![0]],
    )
}

/// The enum table: rustc's measured layouts for each shape.
fn enums() -> Vec<EnumDef> {
    vec![
        option(OPTION_REF, "OptionPtrU64", Ty::Ptr, 0, EnumTagRepr::U64, 8),
        option(
            OPTION_NONZERO,
            "OptionNonZeroU32",
            Ty::Struct(StructId::new(NONZERO_STRUCT)),
            0,
            EnumTagRepr::U32,
            4,
        ),
        option(OPTION_BOOL, "OptionBool", Ty::Bool, 2, EnumTagRepr::U8, 1),
        option(
            OPTION_CHAR,
            "OptionChar",
            Ty::Char,
            0x11_0000,
            EnumTagRepr::U32,
            4,
        ),
        niche_enum(
            TRI,
            "Tri",
            vec![
                variant("Data", vec![Ty::Bool]),
                variant("Low", vec![]),
                variant("High", vec![]),
            ],
            (0, 1, 2),
            2,
            EnumTagRepr::U8,
            (1, 1),
            vec![vec![0], vec![], vec![]],
        ),
        niche_enum(
            WRAPPED,
            "Wrapped",
            vec![
                variant("Low", vec![]),
                variant("Data", vec![Ty::U8]),
                variant("High", vec![]),
            ],
            (1, 0, 2),
            254,
            EnumTagRepr::U8,
            (1, 1),
            vec![vec![], vec![0], vec![]],
        ),
        option(
            OPTION_REF_TYPED,
            "OptionRefU64",
            Ty::Ref(Box::new(Ty::U64)),
            0,
            EnumTagRepr::U64,
            8,
        ),
    ]
}

fn enum_ty(id: u32) -> Ty {
    Ty::Enum(EnumId::new(id))
}

fn case(value: i128, target: trust_ir::BlockId) -> SwitchCase {
    SwitchCase {
        value: Constant::Int(value),
        target,
        args: vec![],
    }
}

/// `{prefix}_disc(p) = (u64) discriminant(*p)`.
fn define_disc(m: &mut ModuleBuilder, prefix: &str, id: u32) {
    let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let mut f = m.function(format!("{prefix}_disc"), sig);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let value = f.load(enum_ty(id), p);
    let disc = f.extract_field(Ty::U8, value, 0);
    let wide = f.zext(Ty::U8, Ty::U64, disc);
    f.ret(vec![wide]);
    f.build();
}

/// `{prefix}_classify(p)`: switch on the discriminant; `None` returns
/// 0xDEAD, `Some(x)` returns `widen(x)`, an impossible discriminant 0xBAD.
fn define_classify(
    m: &mut ModuleBuilder,
    prefix: &str,
    id: u32,
    payload: Ty,
    widen: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>, trust_ir::ValueId) -> trust_ir::ValueId,
) {
    let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let mut f = m.function(format!("{prefix}_classify"), sig);
    let entry = f.create_block();
    let none = f.create_block();
    let some = f.create_block();
    let bad = f.create_block();
    let p = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let value = f.load(enum_ty(id), p);
    let disc = f.extract_field(Ty::U8, value, 0);
    f.switch(disc, vec![case(0, none), case(1, some)], bad, vec![]);
    f.switch_to_block(none);
    let dead = f.iconst(Ty::U64, 0xDEAD);
    f.ret(vec![dead]);
    f.switch_to_block(some);
    let x = f.extract_field(payload, value, 1);
    let wide = widen(&mut f, x);
    f.ret(vec![wide]);
    f.switch_to_block(bad);
    let bad_value = f.iconst(Ty::U64, 0xBAD);
    f.ret(vec![bad_value]);
    f.build();
}

/// `{prefix}_make(out, which, x)`: `which == 0` stores the constant `None`;
/// otherwise a `Some(placeholder)` constant gets the runtime payload
/// `wrap(x)` inserted and is stored.
fn define_make(
    m: &mut ModuleBuilder,
    prefix: &str,
    id: u32,
    param: Ty,
    placeholder: Constant,
    wrap: impl FnOnce(&mut trust_ir_build::FunctionBuilder<'_>, trust_ir::ValueId) -> trust_ir::ValueId,
) {
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U8, param.clone()], vec![]);
    let mut f = m.function(format!("{prefix}_make"), sig);
    let entry = f.create_block();
    let none = f.create_block();
    let some = f.create_block();
    let out = f.add_block_param(entry, Ty::Ptr);
    let which = f.add_block_param(entry, Ty::U8);
    let x = f.add_block_param(entry, param);
    f.switch_to_block(entry);
    f.switch(which, vec![case(0, none)], some, vec![]);
    f.switch_to_block(none);
    let value = f.const_value(enum_ty(id), Constant::Aggregate(vec![Constant::Int(0)]));
    f.store(enum_ty(id), out, value);
    f.ret(vec![]);
    f.switch_to_block(some);
    let seed = f.const_value(
        enum_ty(id),
        Constant::Aggregate(vec![Constant::Int(1), placeholder]),
    );
    let wrapped = wrap(&mut f, x);
    let value = f.insert_field(enum_ty(id), seed, 1, wrapped);
    f.store(enum_ty(id), out, value);
    f.ret(vec![]);
    f.build();
}

/// The corpus, for `triple`.
pub fn corpus(triple: &str) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("niche_enum", target(triple));
    m.add_struct(StructDef {
        origin: None,
        id: StructId::new(NONZERO_STRUCT),
        name: "NonZeroU32".into(),
        fields: vec![FieldDef {
            name: "0".into(),
            ty: Ty::U32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Transparent,
    });
    let nonzero = Ty::Struct(StructId::new(NONZERO_STRUCT));

    // Option<&u64>, payload spelled as a pointer: read and constructed.
    define_disc(&mut m, "nr", OPTION_REF);
    define_classify(&mut m, "nr", OPTION_REF, Ty::Ptr, |f, r| f.load(Ty::U64, r));
    define_make(
        &mut m,
        "nr",
        OPTION_REF,
        Ty::Ptr,
        Constant::Int(8),
        |_, x| x,
    );
    // Option<&u64>, payload spelled as a reference: read only.
    define_disc(&mut m, "nq", OPTION_REF_TYPED);
    define_classify(
        &mut m,
        "nq",
        OPTION_REF_TYPED,
        Ty::Ref(Box::new(Ty::U64)),
        |f, r| f.load(Ty::U64, r),
    );

    // Option<NonZeroU32>.
    define_disc(&mut m, "nz", OPTION_NONZERO);
    let nz = nonzero.clone();
    define_classify(&mut m, "nz", OPTION_NONZERO, nz, |f, s| {
        let raw = f.extract_field(Ty::U32, s, 0);
        f.zext(Ty::U32, Ty::U64, raw)
    });
    let nz = nonzero.clone();
    define_make(
        &mut m,
        "nz",
        OPTION_NONZERO,
        Ty::U32,
        Constant::Aggregate(vec![Constant::Int(1)]),
        move |f, x| {
            let seed = f.const_value(nz.clone(), Constant::Aggregate(vec![Constant::Int(1)]));
            f.insert_field(nz, seed, 0, x)
        },
    );

    // Option<bool>.
    define_disc(&mut m, "nb", OPTION_BOOL);
    define_classify(&mut m, "nb", OPTION_BOOL, Ty::Bool, |f, b| {
        f.zext(Ty::Bool, Ty::U64, b)
    });
    define_make(
        &mut m,
        "nb",
        OPTION_BOOL,
        Ty::Bool,
        Constant::Bool(false),
        |_, x| x,
    );

    // Option<char>.
    define_disc(&mut m, "nc", OPTION_CHAR);
    define_classify(&mut m, "nc", OPTION_CHAR, Ty::Char, |f, c| {
        f.zext(Ty::Char, Ty::U64, c)
    });
    define_make(
        &mut m,
        "nc",
        OPTION_CHAR,
        Ty::Char,
        Constant::Int(0x41),
        |_, x| x,
    );

    // Tri { Data(bool), Low, High }.
    define_disc(&mut m, "tri", TRI);
    {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("tri_classify", sig);
        let entry = f.create_block();
        let data = f.create_block();
        let low = f.create_block();
        let high = f.create_block();
        let bad = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let value = f.load(enum_ty(TRI), p);
        let disc = f.extract_field(Ty::U8, value, 0);
        f.switch(
            disc,
            vec![case(0, data), case(1, low), case(2, high)],
            bad,
            vec![],
        );
        f.switch_to_block(data);
        let b = f.extract_field(Ty::Bool, value, 1);
        let wide = f.zext(Ty::Bool, Ty::U64, b);
        f.ret(vec![wide]);
        f.switch_to_block(low);
        let r = f.iconst(Ty::U64, 100);
        f.ret(vec![r]);
        f.switch_to_block(high);
        let r = f.iconst(Ty::U64, 200);
        f.ret(vec![r]);
        f.switch_to_block(bad);
        let r = f.iconst(Ty::U64, 0xBAD);
        f.ret(vec![r]);
        f.build();
    }
    {
        let sig = m.add_func_type(vec![Ty::Ptr, Ty::U8, Ty::Bool], vec![]);
        let mut f = m.function("tri_make", sig);
        let entry = f.create_block();
        let data = f.create_block();
        let low = f.create_block();
        let high = f.create_block();
        let out = f.add_block_param(entry, Ty::Ptr);
        let which = f.add_block_param(entry, Ty::U8);
        let b = f.add_block_param(entry, Ty::Bool);
        f.switch_to_block(entry);
        f.switch(which, vec![case(0, data), case(1, low)], high, vec![]);
        f.switch_to_block(data);
        let seed = f.const_value(
            enum_ty(TRI),
            Constant::Aggregate(vec![Constant::Int(0), Constant::Bool(false)]),
        );
        let value = f.insert_field(enum_ty(TRI), seed, 1, b);
        f.store(enum_ty(TRI), out, value);
        f.ret(vec![]);
        f.switch_to_block(low);
        let value = f.const_value(enum_ty(TRI), Constant::Aggregate(vec![Constant::Int(1)]));
        f.store(enum_ty(TRI), out, value);
        f.ret(vec![]);
        f.switch_to_block(high);
        let value = f.const_value(enum_ty(TRI), Constant::Aggregate(vec![Constant::Int(2)]));
        f.store(enum_ty(TRI), out, value);
        f.ret(vec![]);
        f.build();
    }
    {
        // Select a complete fieldless variant, preserving canonical value
        // semantics instead of rewriting a loaded enum's discriminant.
        let sig = m.add_func_type(vec![Ty::Ptr, Ty::U8], vec![]);
        let mut f = m.function("tri_set_disc", sig);
        let entry = f.create_block();
        let low = f.create_block();
        let high = f.create_block();
        let bad = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        let d = f.add_block_param(entry, Ty::U8);
        f.switch_to_block(entry);
        f.switch(d, vec![case(1, low), case(2, high)], bad, vec![]);
        for (block, disc) in [(low, 1), (high, 2)] {
            f.switch_to_block(block);
            let value = f.const_value(enum_ty(TRI), Constant::Aggregate(vec![Constant::Int(disc)]));
            f.store(enum_ty(TRI), p, value);
            f.ret(vec![]);
        }
        f.switch_to_block(bad);
        f.unreachable();
        f.build();
    }

    // Wrapped { Low, Data(u8), High }.
    define_disc(&mut m, "wrapped", WRAPPED);

    // Negative control: byte 0 read as if it were a tag.
    {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("oc_byte0", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let byte = f.load(Ty::U8, p);
        let wide = f.cast(CastOp::ZExt, Ty::U8, Ty::U64, byte);
        f.ret(vec![wide]);
        f.build();
    }

    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    module.enums = enums();
    let errors = validate_module(&module);
    assert!(
        errors.is_empty(),
        "the niche corpus must validate: {errors:?}"
    );
    module
}

/// Original invalid runtime-retagging input, retained as a negative control.
pub fn discriminant_write_module(triple: &str) -> Module {
    let template = corpus(triple);
    let mut m = ModuleBuilder::new_with_target_info("niche_retag_refusal", target(triple));
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U8], vec![]);
    let mut f = m.function("tri_retag", sig);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::Ptr);
    let d = f.add_block_param(entry, Ty::U8);
    f.switch_to_block(entry);
    let old = f.load(enum_ty(TRI), p);
    let value = f.insert_field(enum_ty(TRI), old, 0, d);
    f.store(enum_ty(TRI), p, value);
    f.ret(vec![]);
    f.build();
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    module.enums = template.enums;
    module.structs = template.structs;
    module
}

/// C driver: the oracle is the C meaning of each niche spelling.
pub const DRIVER: &str = r#"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t nr_disc(uint64_t *const *p);
extern uint64_t nr_classify(uint64_t *const *p);
extern void nr_make(uint64_t **out, uint8_t which, uint64_t *x);
extern uint64_t nq_disc(uint64_t *const *p);
extern uint64_t nq_classify(uint64_t *const *p);
extern uint64_t nz_disc(const uint32_t *p);
extern uint64_t nz_classify(const uint32_t *p);
extern void nz_make(uint32_t *out, uint8_t which, uint32_t x);
extern uint64_t nb_disc(const uint8_t *p);
extern uint64_t nb_classify(const uint8_t *p);
extern void nb_make(uint8_t *out, uint8_t which, bool x);
extern uint64_t nc_disc(const uint32_t *p);
extern uint64_t nc_classify(const uint32_t *p);
extern void nc_make(uint32_t *out, uint8_t which, uint32_t x);
extern uint64_t tri_disc(const uint8_t *p);
extern uint64_t tri_classify(const uint8_t *p);
extern void tri_make(uint8_t *out, uint8_t which, bool b);
extern void tri_set_disc(uint8_t *p, uint8_t d);
extern uint64_t wrapped_disc(const uint8_t *p);
extern uint64_t oc_byte0(const void *p);

static unsigned checks, failures;
#define CHECK(cond, ...)                                              \
    do {                                                              \
        checks++;                                                     \
        if (!(cond)) {                                                \
            failures++;                                               \
            printf("FAIL line %d: ", __LINE__);                       \
            printf(__VA_ARGS__);                                      \
            printf("\n");                                             \
        }                                                             \
    } while (0)

static uint64_t targets[3] = {0x1122334455667788ull, 0, 0xffffffffffffffffull};

/* The niche formula, written independently in C for 8-bit lanes. */
static uint64_t formula8(uint8_t lane, uint8_t niche_start, uint8_t span,
                         uint64_t start, uint64_t untagged) {
    uint8_t relative = (uint8_t)(lane - niche_start);
    return relative <= span ? start + relative : untagged;
}

int main(void) {
    /* Option<&u64>: NULL is None. */
    uint64_t *refs[4] = {0, &targets[0], &targets[1], &targets[2]};
    for (int i = 0; i < 4; i++) {
        uint64_t *img = refs[i];
        CHECK(nr_disc(&img) == (img ? 1u : 0u), "nr_disc %d", i);
        CHECK(nr_classify(&img) == (img ? *img : 0xDEADu), "nr_classify %d", i);
        CHECK(nq_disc(&img) == (img ? 1u : 0u), "nq_disc %d", i);
        CHECK(nq_classify(&img) == (img ? *img : 0xDEADu), "nq_classify %d", i);
    }
    for (int i = 1; i < 4; i++) {
        uint64_t *out = (uint64_t *)0x5a5a5a5a5a5a5a58ull;
        nr_make(&out, 0, refs[i]);
        CHECK(out == 0, "nr_make None %d", i);
        nr_make(&out, 1, refs[i]);
        CHECK(out == refs[i], "nr_make Some %d", i);
        CHECK(nr_disc(&out) == 1 && nr_classify(&out) == *refs[i], "nr round trip %d", i);
    }

    /* Option<NonZeroU32>: 0 is None. */
    uint32_t nzs[7] = {0, 1, 2, 0x7fffffffu, 0x80000000u, 0xffffffffu, 0x12345678u};
    for (int i = 0; i < 7; i++) {
        uint32_t img = nzs[i];
        CHECK(nz_disc(&img) == (img ? 1u : 0u), "nz_disc %u", img);
        CHECK(nz_classify(&img) == (img ? (uint64_t)img : 0xDEADu), "nz_classify %u", img);
        if (img) {
            uint32_t out = 0xa5a5a5a5u;
            nz_make(&out, 1, img);
            CHECK(out == img, "nz_make Some %u -> %u", img, out);
            nz_make(&out, 0, img);
            CHECK(out == 0, "nz_make None -> %u", out);
        }
    }

    /* Option<bool>: 2 is None. */
    for (unsigned img = 0; img < 3; img++) {
        uint8_t b = (uint8_t)img;
        CHECK(nb_disc(&b) == (img == 2 ? 0u : 1u), "nb_disc %u", img);
        CHECK(nb_classify(&b) == (img == 2 ? 0xDEADu : img), "nb_classify %u", img);
    }
    for (int x = 0; x < 2; x++) {
        uint8_t out = 0x5a;
        nb_make(&out, 1, x != 0);
        CHECK(out == (uint8_t)x, "nb_make Some(%d) -> %u", x, out);
        nb_make(&out, 0, x != 0);
        CHECK(out == 2, "nb_make None -> %u", out);
    }

    /* Option<char>: 0x110000 is None. */
    uint32_t chars[7] = {0, 'A', 0xD7FFu, 0xE000u, 0x10FFFFu, 0x1F600u, 0x110000u};
    for (int i = 0; i < 7; i++) {
        uint32_t img = chars[i];
        int none = img == 0x110000u;
        CHECK(nc_disc(&img) == (none ? 0u : 1u), "nc_disc %#x", img);
        CHECK(nc_classify(&img) == (none ? 0xDEADu : (uint64_t)img), "nc_classify %#x", img);
        if (!none) {
            uint32_t out = 0xa5a5a5a5u;
            nc_make(&out, 1, img);
            CHECK(out == img, "nc_make Some(%#x) -> %#x", img, out);
            nc_make(&out, 0, img);
            CHECK(out == 0x110000u, "nc_make None -> %#x", out);
        }
    }

    /* Tri { Data(bool) = 0/1, Low = 2, High = 3 }. */
    static const uint64_t tri_disc_of[4] = {0, 0, 1, 2};
    static const uint64_t tri_class_of[4] = {0, 1, 100, 200};
    for (unsigned img = 0; img < 4; img++) {
        uint8_t t = (uint8_t)img;
        CHECK(tri_disc(&t) == tri_disc_of[img], "tri_disc %u", img);
        CHECK(tri_classify(&t) == tri_class_of[img], "tri_classify %u", img);
    }
    for (int b = 0; b < 2; b++) {
        uint8_t out = 0x5a;
        tri_make(&out, 0, b != 0);
        CHECK(out == (uint8_t)b, "tri_make Data(%d) -> %u", b, out);
        tri_make(&out, 1, b != 0);
        CHECK(out == 2, "tri_make Low -> %u", out);
        tri_make(&out, 2, b != 0);
        CHECK(out == 3, "tri_make High -> %u", out);
    }
    for (unsigned from = 2; from < 4; from++) {
        for (unsigned d = 1; d < 3; d++) {
            uint8_t t = (uint8_t)from;
            tri_set_disc(&t, (uint8_t)d);
            CHECK(t == (uint8_t)(d + 1), "tri_set_disc %u <- %u gives %u", from, d, t);
            CHECK(tri_disc(&t) == d, "tri_set_disc round trip %u", d);
        }
    }

    /* Every byte image of the 8-bit lanes against the formula. */
    for (unsigned lane = 0; lane < 256; lane++) {
        uint8_t byte = (uint8_t)lane;
        CHECK(nb_disc(&byte) == formula8(byte, 2, 0, 0, 1), "nb formula %u", lane);
        CHECK(tri_disc(&byte) == formula8(byte, 2, 1, 1, 0), "tri formula %u", lane);
        CHECK(wrapped_disc(&byte) == formula8(byte, 254, 2, 0, 1), "wrapped formula %u", lane);
    }
    /* Wrapped: Low = 254, High WRAPS to 0, Data otherwise. */
    uint8_t w = 254;
    CHECK(wrapped_disc(&w) == 0, "wrapped Low");
    w = 0;
    CHECK(wrapped_disc(&w) == 2, "wrapped High");
    w = 42;
    CHECK(wrapped_disc(&w) == 1, "wrapped Data");

    /* Negative control: reading byte 0 as a tag disagrees with the oracle. */
    uint32_t some_a = 'A';
    CHECK(oc_byte0(&some_a) != nc_disc(&some_a), "byte-0 tag read must not look right");
    uint64_t *some_ref = &targets[0];
    CHECK(oc_byte0(&some_ref) != nr_disc(&some_ref), "byte-0 tag read of a pointer");

    if (failures) {
        printf("FAILED %u of %u niche checks\n", failures, checks);
        return 1;
    }
    printf("PASS %u niche checks\n", checks);
    return 0;
}
"#;
