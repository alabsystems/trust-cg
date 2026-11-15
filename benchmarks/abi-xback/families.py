#!/usr/bin/env python3
"""Deterministic AAPCS64 signature families for the cross-backend ABI gate.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

`gen.py` draws random many-argument signatures from a fixed scalar and
two-aggregate table, so register-bank exhaustion is frequent across seeds but
never guaranteed per seed, and whole families (HFA/HVA, `bool`, variadics,
callbacks, by-reference copies, narrow returns) are outside its domain. This
generator names one case per placement rule instead: every case is a
signature built to land a specific argument in a specific register, at a
specific register/stack boundary, or on the stack, plus a return through a
specific path (x0, x0:x1, v0-v3, q0-q3, or the x8 indirect-result buffer).

Each case is one callee function and one caller statement block. A group
(one family under one ABI) becomes one callee crate and one caller crate:

* the callee folds every bit of every parameter, in order, into a 64-bit
  accumulator and builds its return value (and, for `&mut` parameters, the
  stored-back value) from that accumulator;
* the caller passes `black_box`ed literals, folds what came back, and prints
  one line per case.

The generator evaluates the same fold in Python, so every case carries an
independently computed expected line; the LLVM x LLVM oracle must print
exactly that line before any cross-backend cell is compared with it.

C-ABI groups declare the callee in an `extern "C"` block of the caller (the
FFI shape); Rust-ABI groups call it by path through `extern crate`. A
`via_pointer` case instead calls the callee through the C-variadic `fn`
pointer a getter in the callee crate returns. Narrow
integer arguments are passed out of a wider `black_box`ed value truncated at
the call (`bb(0x..u64) as i8`), so the upper register bits a caller leaves
behind are not zero and a callee that skips its own extension reads a
different value.

Usage:
  families.py --list                     JSON list of groups and cases
  families.py --emit DIR [--group NAME] [--case NAME]
                                         write callee.rs, caller.rs and
                                         expected.json for each group (or one
                                         single-case group) under DIR
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import random
import struct
import sys
import zlib

MASK = (1 << 64) - 1
MUL = 0x2545F4914F6CDD1D
GOLDEN = 0x9E3779B97F4A7C15


def salt_key(salt: int) -> int:
    return (salt * GOLDEN) & MASK


def mix(acc: int, salt: int) -> int:
    m = ((acc ^ salt_key(salt)) * MUL) & MASK
    return m ^ (m >> 29)


def mix_rs(acc: str, salt: int) -> str:
    return (f"{{ let m = ({acc} ^ 0x{salt_key(salt):016x}u64).wrapping_mul(0x{MUL:016x}u64); "
            f"m ^ (m >> 29) }}")


def fold_word(acc: int, word: int) -> int:
    return (acc * 31 + word) & MASK


def f32_bits(value: float) -> int:
    return struct.unpack("<I", struct.pack("<f", value))[0]


def f64_bits(value: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", value))[0]


def float_literal(value: float) -> str:
    text = repr(float(value))
    return text if "e" not in text else f"{value:.6f}"


# --- the type model -------------------------------------------------------
#
# Every type knows: its Rust spelling, how to draw an input value, how to
# write that value as a Rust literal, the u64 words the fold reads from a
# value (Python) and from an expression (Rust), and how to build a value from
# the accumulator (Python and Rust, salt by salt).

class Int:
    def __init__(self, name: str, bits: int, signed: bool):
        self.name, self.bits, self.signed = name, bits, signed
        self.narrow = bits < 64

    def rust(self) -> str:
        return self.name

    def wrap(self, value: int) -> int:
        value &= (1 << self.bits) - 1
        if self.signed and value >> (self.bits - 1):
            value -= 1 << self.bits
        return value

    def draw(self, rng: random.Random):
        return self.wrap(rng.getrandbits(self.bits))

    def literal(self, value) -> str:
        return f"({value}{self.name})"

    def dirty_literal(self, value, rng: random.Random) -> str:
        # The low `bits` hold the value; every higher bit is set at random.
        low = value & ((1 << self.bits) - 1)
        wide = (rng.getrandbits(64) & ~((1 << self.bits) - 1) & MASK) | low
        if wide >> self.bits == 0:
            wide |= 1 << 63
        return f"(bb(0x{wide:016x}u64) as {self.name})"

    def words(self, value) -> list[int]:
        if self.bits == 128:
            return [value & MASK, (value >> 64) & MASK]
        return [value & MASK]

    def fold(self, expr: str) -> list[str]:
        if self.bits == 128:
            return [f"({expr}) as u64", f"(({expr}) >> 64) as u64"]
        return [f"({expr}) as i64 as u64"]

    def build(self, acc: int, salt: int):
        if self.bits == 128:
            value = (mix(acc, salt) << 64) | mix(acc, salt + 1)
            return self.wrap(value), salt + 2
        return self.wrap(mix(acc, salt)), salt + 1

    def build_rs(self, acc: str, salt: int):
        if self.bits == 128:
            expr = (f"((({mix_rs(acc, salt)}) as u128) << 64 | (({mix_rs(acc, salt + 1)}) as u128))"
                    f" as {self.name}")
            return expr, salt + 2
        return f"({mix_rs(acc, salt)}) as {self.name}", salt + 1


class Bool:
    narrow = False

    def rust(self) -> str:
        return "bool"

    def draw(self, rng):
        return bool(rng.getrandbits(1))

    def literal(self, value) -> str:
        return "true" if value else "false"

    def words(self, value):
        return [1 if value else 0]

    def fold(self, expr):
        return [f"({expr}) as u64"]

    def build(self, acc, salt):
        return bool((mix(acc, salt) >> 7) & 1), salt + 1

    def build_rs(self, acc, salt):
        return f"((({mix_rs(acc, salt)}) >> 7) & 1) != 0", salt + 1


class Char:
    narrow = False

    def rust(self) -> str:
        return "char"

    def draw(self, rng):
        return rng.randrange(0x20, 0xD000)

    def literal(self, value) -> str:
        return f"'\\u{{{value:x}}}'"

    def words(self, value):
        return [value]

    def fold(self, expr):
        return [f"({expr}) as u64"]

    def build(self, acc, salt):
        return mix(acc, salt) % 0xD000, salt + 1

    def build_rs(self, acc, salt):
        return (f"unsafe {{ char::from_u32_unchecked((({mix_rs(acc, salt)}) % 0xD000) as u32) }}",
                salt + 1)


class Float:
    narrow = False

    def __init__(self, bits: int):
        self.bits = bits
        self.name = f"f{bits}"

    def rust(self) -> str:
        return self.name

    def draw(self, rng):
        # Quarter steps: exact in f32 and f64, and not integral, so a value
        # that crossed through the other precision changes its bits.
        return rng.randrange(-400000, 400000) * 0.25

    def literal(self, value) -> str:
        return f"({float_literal(value)}{self.name})"

    def words(self, value):
        return [f32_bits(value) if self.bits == 32 else f64_bits(value)]

    def fold(self, expr):
        return [f"({expr}).to_bits() as u64"]

    def build(self, acc, salt):
        quarter = ((mix(acc, salt) >> 11) & 0xFFFFF) - 0x80000
        return quarter * 0.25, salt + 1

    def build_rs(self, acc, salt):
        return (f"((((({mix_rs(acc, salt)}) >> 11) & 0xFFFFF) as i64 - 0x80000) as {self.name})"
                f" * 0.25{self.name}", salt + 1)


class Vector:
    """An AArch64 short vector type from core::arch::aarch64."""

    narrow = False

    def __init__(self, name: str, lane, lanes: int):
        self.name, self.lane, self.lanes = name, lane, lanes

    def rust(self) -> str:
        return self.name

    def array(self) -> str:
        return f"[{self.lane.rust()}; {self.lanes}]"

    def draw(self, rng):
        return [self.lane.draw(rng) for _ in range(self.lanes)]

    def literal(self, value) -> str:
        lanes = ", ".join(self.lane.literal(lane) for lane in value)
        return f"unsafe {{ core::mem::transmute::<{self.array()}, {self.name}>([{lanes}]) }}"

    def words(self, value):
        return [word for lane in value for word in self.lane.words(lane)]

    def fold(self, expr):
        words = []
        for index in range(self.lanes):
            lane = f"unsafe {{ core::mem::transmute::<{self.name}, {self.array()}>({expr}) }}[{index}]"
            words.extend(self.lane.fold(lane))
        return words

    def build(self, acc, salt):
        lanes = []
        for _ in range(self.lanes):
            value, salt = self.lane.build(acc, salt)
            lanes.append(value)
        return lanes, salt

    def build_rs(self, acc, salt):
        lanes = []
        for _ in range(self.lanes):
            expr, salt = self.lane.build_rs(acc, salt)
            lanes.append(expr)
        return (f"unsafe {{ core::mem::transmute::<{self.array()}, {self.name}>([{', '.join(lanes)}]) }}",
                salt)


class Array:
    narrow = False

    def __init__(self, element, count: int):
        self.element, self.count = element, count

    def rust(self) -> str:
        return f"[{self.element.rust()}; {self.count}]"

    def draw(self, rng):
        return [self.element.draw(rng) for _ in range(self.count)]

    def literal(self, value) -> str:
        return "[" + ", ".join(self.element.literal(item) for item in value) + "]"

    def words(self, value):
        return [word for item in value for word in self.element.words(item)]

    def fold(self, expr):
        return [word for index in range(self.count) for word in self.element.fold(f"({expr})[{index}]")]

    def build(self, acc, salt):
        items = []
        for _ in range(self.count):
            value, salt = self.element.build(acc, salt)
            items.append(value)
        return items, salt

    def build_rs(self, acc, salt):
        items = []
        for _ in range(self.count):
            expr, salt = self.element.build_rs(acc, salt)
            items.append(expr)
        return "[" + ", ".join(items) + "]", salt


class Struct:
    """A named struct.

    `repr` is the text of its `#[repr(..)]` attribute (`"C"` by default;
    `"C, align(16)"`, `"C, packed"`, `"align(16)"`, ...); `repr_c=False` with no
    `repr` leaves the layout, field order included, to rustc. Fields of a
    packed struct are read by value only (never through a reference).
    """

    narrow = False

    def __init__(self, name: str, fields, repr_c: bool = True, repr: str | None = None):
        self.name, self.fields = name, fields
        self.repr = repr if repr is not None else ("C" if repr_c else None)

    def rust(self) -> str:
        return self.name

    def declaration(self) -> str:
        fields = "".join(f"    pub {name}: {ty.rust()},\n" for name, ty in self.fields)
        attributes = f"#[repr({self.repr})]\n" if self.repr else ""
        return f"{attributes}#[derive(Clone, Copy)]\npub struct {self.name} {{\n{fields}}}\n"

    def draw(self, rng):
        return [ty.draw(rng) for _, ty in self.fields]

    def literal(self, value) -> str:
        fields = ", ".join(f"{name}: {ty.literal(item)}" for (name, ty), item in zip(self.fields, value))
        return f"{self.name} {{ {fields} }}"

    def words(self, value):
        return [word for (_, ty), item in zip(self.fields, value) for word in ty.words(item)]

    def fold(self, expr):
        return [word for name, ty in self.fields for word in ty.fold(f"({expr}).{name}")]

    def build(self, acc, salt):
        items = []
        for _, ty in self.fields:
            value, salt = ty.build(acc, salt)
            items.append(value)
        return items, salt

    def build_rs(self, acc, salt):
        fields = []
        for name, ty in self.fields:
            expr, salt = ty.build_rs(acc, salt)
            fields.append(f"{name}: {expr}")
        return f"{self.name} {{ {', '.join(fields)} }}", salt


class Tuple:
    narrow = False

    def __init__(self, *items):
        self.items = items

    def rust(self) -> str:
        return "(" + ", ".join(item.rust() for item in self.items) + ("," if len(self.items) == 1 else "") + ")"

    def draw(self, rng):
        return [item.draw(rng) for item in self.items]

    def literal(self, value) -> str:
        return "(" + ", ".join(ty.literal(item) for ty, item in zip(self.items, value)) + ")"

    def words(self, value):
        return [word for ty, item in zip(self.items, value) for word in ty.words(item)]

    def fold(self, expr):
        return [word for index, ty in enumerate(self.items) for word in ty.fold(f"({expr}).{index}")]

    def build(self, acc, salt):
        items = []
        for ty in self.items:
            value, salt = ty.build(acc, salt)
            items.append(value)
        return items, salt

    def build_rs(self, acc, salt):
        items = []
        for ty in self.items:
            expr, salt = ty.build_rs(acc, salt)
            items.append(expr)
        return "(" + ", ".join(items) + ")", salt


class Opt:
    """`Option<T>`: words are (is_some, then each payload word or 0)."""

    narrow = False

    def __init__(self, inner):
        self.inner = inner

    def rust(self) -> str:
        return f"Option<{self.inner.rust()}>"

    def draw(self, rng):
        return None if rng.random() < 0.3 else self.inner.draw(rng)

    def literal(self, value) -> str:
        return "None" if value is None else f"Some({self.inner.literal(value)})"

    def words(self, value):
        if value is None:
            return [0] * (1 + len(self.inner.fold("v")))
        return [1, *self.inner.words(value)]

    def fold(self, expr):
        payload = self.inner.fold("v")
        return [f"({expr}).is_some() as u64",
                *(f"(match {expr} {{ Some(v) => {word}, None => 0 }})" for word in payload)]

    def build(self, acc, salt):
        present = (mix(acc, salt) >> 3) & 1
        value, salt = self.inner.build(acc, salt + 1)
        return (value if present else None), salt

    def build_rs(self, acc, salt):
        inner, next_salt = self.inner.build_rs(acc, salt + 1)
        return (f"if ((({mix_rs(acc, salt)}) >> 3) & 1) != 0 {{ Some({inner}) }} else {{ None }}",
                next_salt)


class NonZero:
    """`core::num::NonZeroU32` and the like: a niche-carrying integer."""

    narrow = False

    def __init__(self, inner: Int):
        self.inner = inner
        self.path = f"core::num::NonZero{inner.name[0].upper()}{inner.name[1:]}"

    def rust(self) -> str:
        return self.path

    def draw(self, rng):
        return self.inner.draw(rng) or 1

    def literal(self, value) -> str:
        return f"unsafe {{ {self.path}::new_unchecked({self.inner.literal(value)}) }}"

    def words(self, value):
        return self.inner.words(value)

    def fold(self, expr):
        return self.inner.fold(f"({expr}).get()")

    def build(self, acc, salt):
        value, salt = self.inner.build(acc, salt)
        return self.inner.wrap(value | 1), salt

    def build_rs(self, acc, salt):
        expr, salt = self.inner.build_rs(acc, salt)
        return f"unsafe {{ {self.path}::new_unchecked(({expr}) | 1) }}", salt


class Union:
    """A union written and read through its FIRST field, which covers every
    byte the value defines; the other fields only shape its classification."""

    narrow = False

    def __init__(self, name: str, fields, repr: str | None = "C"):
        self.name, self.fields, self.repr = name, fields, repr

    def rust(self) -> str:
        return self.name

    def declaration(self) -> str:
        fields = "".join(f"    pub {name}: {ty.rust()},\n" for name, ty in self.fields)
        attributes = f"#[repr({self.repr})]\n" if self.repr else ""
        return f"{attributes}#[derive(Clone, Copy)]\npub union {self.name} {{\n{fields}}}\n"

    def carrier(self):
        return self.fields[0]

    def draw(self, rng):
        return self.carrier()[1].draw(rng)

    def literal(self, value) -> str:
        name, ty = self.carrier()
        return f"{self.name} {{ {name}: {ty.literal(value)} }}"

    def words(self, value):
        return self.carrier()[1].words(value)

    def fold(self, expr):
        name, ty = self.carrier()
        return ty.fold(f"unsafe {{ ({expr}).{name} }}")

    def build(self, acc, salt):
        return self.carrier()[1].build(acc, salt)

    def build_rs(self, acc, salt):
        name, ty = self.carrier()
        expr, salt = ty.build_rs(acc, salt)
        return f"{self.name} {{ {name}: {expr} }}", salt


def salt_use(ty) -> int:
    """How many salts building one value of `ty` consumes."""
    return ty.build(0, 0)[1]


class Enum:
    """An enum with payload variants (each one payload value, or none).

    Words: the variant index, then the payload's words, zero-padded to the
    widest payload; a fieldless variant contributes zeros.
    """

    narrow = False

    def __init__(self, name: str, variants, repr: str | None = None):
        self.name, self.variants, self.repr = name, variants, repr
        self.width = max((len(payload.fold("v")) for _, payload in variants if payload is not None), default=0)

    def rust(self) -> str:
        return self.name

    def declaration(self) -> str:
        arms = "".join(f"    {name}({payload.rust()}),\n" if payload is not None else f"    {name},\n"
                       for name, payload in self.variants)
        attributes = f"#[repr({self.repr})]\n" if self.repr else ""
        return f"{attributes}#[derive(Clone, Copy)]\npub enum {self.name} {{\n{arms}}}\n"

    def draw(self, rng):
        index = rng.randrange(len(self.variants))
        payload = self.variants[index][1]
        return index, (None if payload is None else payload.draw(rng))

    def variant_expr(self, index: int, payload_expr: str | None) -> str:
        name = self.variants[index][0]
        return f"{self.name}::{name}" if payload_expr is None else f"{self.name}::{name}({payload_expr})"

    def literal(self, value) -> str:
        index, payload = value
        ty = self.variants[index][1]
        return self.variant_expr(index, None if ty is None else ty.literal(payload))

    def words(self, value):
        index, payload = value
        ty = self.variants[index][1]
        words = [] if ty is None else ty.words(payload)
        return [index, *words, *([0] * (self.width - len(words)))]

    def fold(self, expr):
        def arm(index, word):
            name, payload = self.variants[index]
            if payload is None:
                return f"{self.name}::{name} => 0u64"
            words = payload.fold("v")
            if word < len(words):
                return f"{self.name}::{name}(v) => {words[word]}"
            return f"{self.name}::{name}(_) => 0u64"

        def pattern(index):
            name, payload = self.variants[index]
            return f"{self.name}::{name}" if payload is None else f"{self.name}::{name}(_)"

        index = ", ".join(f"{pattern(i)} => {i}u64" for i in range(len(self.variants)))
        out = [f"(match {expr} {{ {index} }})"]
        for word in range(self.width):
            out.append(f"(match {expr} {{ {', '.join(arm(i, word) for i in range(len(self.variants)))} }})")
        return out

    def next_salt(self, salt: int) -> int:
        return salt + 1 + max((salt_use(payload) for _, payload in self.variants if payload is not None),
                              default=0)

    def build(self, acc, salt):
        index = mix(acc, salt) % len(self.variants)
        payload = self.variants[index][1]
        value = None if payload is None else payload.build(acc, salt + 1)[0]
        return (index, value), self.next_salt(salt)

    def build_rs(self, acc, salt):
        arms = []
        for index, (_, payload) in enumerate(self.variants):
            expr = None if payload is None else payload.build_rs(acc, salt + 1)[0]
            pattern = f"{index}" if index + 1 < len(self.variants) else "_"
            arms.append(f"{pattern} => {self.variant_expr(index, expr)}")
        return (f"match ({mix_rs(acc, salt)}) % {len(self.variants)}u64 {{ {', '.join(arms)} }}",
                self.next_salt(salt))


# Parameter-only wrappers: the caller owns the referent.
class Ref:
    def __init__(self, inner, mutable: bool):
        self.inner, self.mutable = inner, mutable

    def rust(self) -> str:
        return ("&mut " if self.mutable else "&") + self.inner.rust()


class Slice:
    """`&[T]` / `&mut [T]` / `&str` over a caller-owned array of `count` items."""

    def __init__(self, element, count: int, mutable: bool = False, text: bool = False):
        self.element, self.count, self.mutable, self.text = element, count, mutable, text

    def rust(self) -> str:
        if self.text:
            return "&str"
        return ("&mut [" if self.mutable else "&[") + self.element.rust() + "]"


class OptRef:
    """`Option<&T>` (a nullable pointer)."""

    def __init__(self, inner):
        self.inner = inner

    def rust(self) -> str:
        return f"Option<&{self.inner.rust()}>"


class Mutated:
    """A by-value C composite the callee overwrites through a volatile store."""

    def __init__(self, inner):
        self.inner = inner

    def rust(self) -> str:
        return self.inner.rust()


U8, I8 = Int("u8", 8, False), Int("i8", 8, True)
U16, I16 = Int("u16", 16, False), Int("i16", 16, True)
U32, I32 = Int("u32", 32, False), Int("i32", 32, True)
U64, I64 = Int("u64", 64, False), Int("i64", 64, True)
USIZE, ISIZE = Int("usize", 64, False), Int("isize", 64, True)
U128, I128 = Int("u128", 128, False), Int("i128", 128, True)
BOOL, CHAR = Bool(), Char()
F32, F64 = Float(32), Float(64)
F32X4 = Vector("float32x4_t", F32, 4)
F64X2 = Vector("float64x2_t", F64, 2)
I32X4 = Vector("int32x4_t", I32, 4)
F32X2 = Vector("float32x2_t", F32, 2)
U8X16 = Vector("uint8x16_t", U8, 16)
I16X4 = Vector("int16x4_t", I16, 4)

H1F = Struct("H1f", [("a", F32)])
H2F = Struct("H2f", [("a", F32), ("b", F32)])
H3F = Struct("H3f", [("a", F32), ("b", F32), ("c", F32)])
H4F = Struct("H4f", [("a", F32), ("b", F32), ("c", F32), ("d", F32)])
H1D = Struct("H1d", [("a", F64)])
H2D = Struct("H2d", [("a", F64), ("b", F64)])
H3D = Struct("H3d", [("a", F64), ("b", F64), ("c", F64)])
H4D = Struct("H4d", [("a", F64), ("b", F64), ("c", F64), ("d", F64)])
HNEST = Struct("Hnest", [("a", H2F), ("b", Array(F32, 2))])
HARR = Struct("Harr", [("a", Array(F64, 3))])
NOT_HFA5 = Struct("NotHfa5", [("a", F64), ("b", F64), ("c", F64), ("d", F64), ("e", F64)])
MIXF = Struct("MixF", [("a", F32), ("b", F64)])
MIXFI = Struct("MixFI", [("a", F64), ("b", U64)])
V1 = Struct("V1", [("a", F32X4)])
V2 = Struct("V2", [("a", F32X4), ("b", F32X4)])
V3 = Struct("V3", [("a", F32X4), ("b", F32X4), ("c", F32X4)])
V4 = Struct("V4", [("a", F32X4), ("b", F32X4), ("c", F32X4), ("d", F32X4)])
VD2 = Struct("VD2", [("a", F64X2), ("b", F64X2)])
VI2 = Struct("VI2", [("a", I32X4), ("b", I32X4)])
VS2 = Struct("VS2", [("a", F32X2), ("b", F32X2)])
VMIX = Struct("VMix", [("a", F32X4), ("b", I32X4)])
G3 = Struct("G3", [("a", U8), ("b", U16), ("c", U32)])
G12 = Struct("G12", [("a", U32), ("b", U32), ("c", U32)])
A8 = Struct("A8", [("a", I64), ("b", I64)])
A16 = Struct("A16", [("x", I128)])
A24 = Struct("A24", [("a", I64), ("b", I64), ("c", I64)])
PAD = Struct("Pad", [("a", U8), ("b", U32), ("c", U16)])
B7 = Struct("B7", [("a", Array(U8, 7))])
S3 = Struct("S3", [("a", U8), ("b", U8), ("c", U8)])
BIG40 = Struct("Big40", [("a", Array(U64, 5))])
BOOLS = Struct("BoolS", [("a", BOOL), ("b", U8), ("c", BOOL)])
S3R = Struct("S3r", [("a", U8), ("b", U8), ("c", U8)], repr_c=False)
PAIR_U64 = Tuple(U64, U64)
PAIR_F64 = Tuple(F64, F64)
PAIR_F32 = Tuple(F32, F32)
TRIPLE_U64 = Tuple(U64, U64, U64)

STRUCTS = [
    H1F, H2F, H3F, H4F, H1D, H2D, H3D, H4D, HNEST, HARR, NOT_HFA5, MIXF, MIXFI,
    V1, V2, V3, V4, VD2, VI2, VS2, VMIX, G3, G12, A8, A16, A24, PAD, B7, S3, BIG40,
    BOOLS, S3R,
]

# Layout-attribute shapes: over-aligned, packed, unions, payload enums and
# niches. Declared only in the crates of the families that use them, so the
# older groups' sources are unchanged.
#
# Over-aligned C composites, `#[repr(C, align(N))]`: AAPCS64 places a
# composite by its NATURAL alignment (that of its most-aligned member), never
# the `aligned` attribute, so `Oa16` {u64, u64} is passed in two consecutive
# registers from any NGRN (x1:x2 after one u64), while a composite whose MEMBER
# is 16-aligned (`OaWrap16`) starts on an even register. rustc's Linux FnAbi
# says the same (`unadjusted_abi_align`); DarwinPCS uses the adjusted one.
OA2 = Struct("Oa2", [("a", U8)], repr="C, align(2)")
OA4 = Struct("Oa4", [("a", U8), ("b", U8)], repr="C, align(4)")
OA8 = Struct("Oa8", [("a", U16)], repr="C, align(8)")
OA16_U8 = Struct("Oa16U8", [("a", U8)], repr="C, align(16)")
OA16_U32 = Struct("Oa16U32", [("a", U32)], repr="C, align(16)")
OA16_U64 = Struct("Oa16U64", [("a", U64)], repr="C, align(16)")
OA16 = Struct("Oa16", [("a", U64), ("b", U64)], repr="C, align(16)")
OA16_U32X3 = Struct("Oa16U32x3", [("a", U32), ("b", U32), ("c", U32)], repr="C, align(16)")
OA8_U32X3 = Struct("Oa8U32x3", [("a", U32), ("b", U32), ("c", U32)], repr="C, align(8)")
OA16_F64X2 = Struct("Oa16F64x2", [("a", F64), ("b", F64)], repr="C, align(16)")
OA16_F32X2 = Struct("Oa16F32x2", [("a", F32), ("b", F32)], repr="C, align(16)")
OA16_MIX = Struct("Oa16Mix", [("a", F32), ("b", U32)], repr="C, align(16)")
OA32 = Struct("Oa32", [("a", U64)], repr="C, align(32)")
OA64 = Struct("Oa64", [("a", U8), ("b", U32)], repr="C, align(64)")
OA32_F32X4 = Struct("Oa32F32x4", [("a", F32), ("b", F32), ("c", F32), ("d", F32)], repr="C, align(32)")
# Nested: a repr(C) struct around an over-aligned member takes the member's
# alignment as its natural one; an over-aligned struct around a smaller one.
OA_WRAP16 = Struct("OaWrap16", [("a", OA16_U8)])
OA_WRAP8 = Struct("OaWrap8", [("a", U32), ("b", OA8)])
OA_IN16 = Struct("OaIn16", [("a", U32), ("b", OA4)], repr="C, align(16)")
OA_WRAP_HFA = Struct("OaWrapHfa", [("a", OA16_F64X2)])
# Over-aligned Rust-layout structs, `#[repr(align(N))]`.
ROA16 = Struct("Roa16", [("a", U64), ("b", U64)], repr="align(16)")
ROA16_U32 = Struct("Roa16U32", [("a", U32)], repr="align(16)")
ROA8_U8X3 = Struct("Roa8U8x3", [("a", U8), ("b", U8), ("c", U8)], repr="align(8)")
ROA16_F32X2 = Struct("Roa16F32x2", [("a", F32), ("b", F32)], repr="align(16)")
ROA32 = Struct("Roa32", [("a", U64)], repr="align(32)")
ROA4_U16 = Struct("Roa4U16", [("a", U16)], repr="align(4)")
ROA_WRAP = Struct("RoaWrap", [("a", U8), ("b", ROA8_U8X3)], repr_c=False)
# Packed.
PK = Struct("Pk", [("a", U8), ("b", U32), ("c", U16)], repr="C, packed")
PK_AL = Struct("PkAl", [("a", U32), ("b", U32)], repr="C, packed")
PK2 = Struct("Pk2", [("a", U16), ("b", U64)], repr="C, packed(2)")
PK_F = Struct("PkF", [("a", F32), ("b", F32)], repr="C, packed")
PK_BIG = Struct("PkBig", [("a", U8), ("b", U64), ("c", U64)], repr="C, packed")
RPK = Struct("Rpk", [("a", U8), ("b", U64)], repr="packed")
RPK2 = Struct("Rpk2", [("a", U8), ("b", U32)], repr="packed(2)")
# Unions, read and written through their first field.
UN_INT = Union("UnInt", [("a", U64), ("b", Array(U8, 8))])
UN_MIX = Union("UnMix", [("a", U64), ("b", F64)])
UN_HFA = Union("UnHfa", [("a", H2F), ("b", Array(F32, 2))])
UN_16 = Union("Un16", [("a", Array(U64, 2)), ("b", U32)])
UN_24 = Union("Un24", [("a", Array(U64, 3)), ("b", U8)])
UN_SMALL = Union("UnSmall", [("a", U16), ("b", U8)])
RUN_INT = Union("RunInt", [("a", U64), ("b", U32)], repr=None)
# Payload enums: Rust layout, and the RFC 2195 `repr(u8)` / `repr(C, u32)`
# layouts the C ABI admits.
EP = Enum("Ep", [("A", U32), ("B", U64), ("C", None)])
EF = Enum("Ef", [("A", F64), ("B", F64)])
EB = Enum("Eb", [("A", U8), ("B", BOOL), ("C", CHAR)])
E16 = Enum("E16", [("A", U128), ("B", None)])
E24 = Enum("E24", [("A", PAIR_U64), ("B", U32)])
ECR = Enum("Ecr", [("A", U32), ("B", U64), ("C", None)], repr="u8")
ECR32 = Enum("Ecr32", [("A", F32), ("B", U16)], repr="C, u32")
# Niches.
NZ8, NZ16 = NonZero(U8), NonZero(U16)
NZ32, NZ64, NZ128 = NonZero(U32), NonZero(U64), NonZero(U128)
NZI32 = NonZero(I32)
ONZ8, ONZ32, ONZ64, ONZ128 = Opt(NZ8), Opt(NZ32), Opt(NZ64), Opt(NZ128)
OBOOL, OCHAR = Opt(BOOL), Opt(CHAR)

LAYOUT_TYPES = [
    OA2, OA4, OA8, OA16_U8, OA16_U32, OA16_U64, OA16, OA16_U32X3, OA8_U32X3, OA16_F64X2, OA16_F32X2,
    OA16_MIX, OA32, OA64, OA32_F32X4, OA_WRAP16, OA_WRAP8, OA_IN16, OA_WRAP_HFA,
    ROA16, ROA16_U32, ROA8_U8X3, ROA16_F32X2, ROA32, ROA4_U16, ROA_WRAP,
    PK, PK_AL, PK2, PK_F, PK_BIG, RPK, RPK2,
    UN_INT, UN_MIX, UN_HFA, UN_16, UN_24, UN_SMALL, RUN_INT,
    EP, EF, EB, E16, E24, ECR, ECR32,
]
LAYOUT_FAMILIES = ("overalign", "packed", "union", "enum", "niche")


# --- cases --------------------------------------------------------------

class Case:
    def __init__(self, name, family, abi, params, ret, rule, *, variadic=None, callback=None,
                 libc=False, via_pointer=False):
        self.name, self.family, self.abi = name, family, abi
        self.params, self.ret, self.rule = list(params), ret, rule
        self.variadic = variadic          # list of anonymous argument types
        self.callback = callback          # (callback parameter types, callback return type)
        self.libc = libc                  # caller-only snprintf case
        # A C-variadic callee the caller reaches through the `fn` pointer
        # `<name>_ptr()` returns, not by a direct call.
        self.via_pointer = via_pointer
        if via_pointer and (variadic is None or abi != "C"):
            raise ValueError(f"{name}: only a C-variadic case is called through its fn pointer")
        self.seed = zlib.crc32(name.encode()) & 0xFFFFFFFF

    @property
    def group(self) -> str:
        return f"{self.family}_{'c' if self.abi == 'C' else 'rust'}"

    @property
    def sides(self) -> str:
        # A caller-only case exercises the caller's half of a call into libc;
        # its callee crate holds nothing of it.
        return "caller" if self.libc else "both"


def u64s(count):
    return [U64] * count


def f64s(count):
    return [F64] * count


def both(name, family, params, ret, rule, **kwargs):
    return [Case(f"{name}_c", family, "C", params, ret, rule, **kwargs),
            Case(f"{name}_rust", family, "Rust", params, ret, rule, **kwargs)]


def cases() -> list[Case]:
    out: list[Case] = []
    add = out.extend
    # integer: every width, narrow arguments with dirty upper bits, narrow returns.
    add(both("int_widths", "integer", [U8, I8, U16, I16, U32, I32, U64, I64], U64,
             "all eight integer widths in x0-x7; narrow values arrive with dirty upper bits"))
    for ret in (I8, U8, I16, U16, I32, U32, ISIZE, CHAR):
        add(both(f"int_ret_{ret.rust()}", "integer", [U64, I16, U8], ret,
                 f"{ret.rust()} return in w0/x0; the caller extends it"))
    add(both("int_usize_char", "integer", [USIZE, ISIZE, CHAR, I8, CHAR], I64,
             "pointer-sized and char arguments"))
    # float: both precisions, interleaved with integers, f32 return.
    add(both("float_regs", "float", [F32, F64, F32, F64, F32, F64, F32, F64], F64,
             "eight floats in v0-v7, alternating precision"))
    add(both("float_ret_f32", "float", [F32, U64], F32, "f32 return in s0"))
    add(both("float_interleave", "float", [U8, F32, U16, F64, I32, F32, I64, F64, U64, F32], F32,
             "integer and float banks are allocated independently"))
    # hfa: every member count in registers and as a return; boundary and spill.
    add(both("hfa_args", "hfa", [H1F, H2D, H3F], H4D,
             "H1f in s0, H2d in d1-d2, H3f in s3-s5; H4d return in d0-d3"))
    for ret in (H1F, H2F, H3F, H4F, H1D, H2D, H3D, H4D, HNEST, HARR):
        out.append(Case(f"hfa_ret_{ret.name.lower()}_c", "hfa", "C", [U64, F32], ret,
                        f"{ret.name} return in v0-v{len(ret.words(ret.draw(random.Random(0)))) - 1}"))
    for ret in (H2F, H3F, H4D):
        out.append(Case(f"hfa_ret_{ret.name.lower()}_rust", "hfa", "Rust", [U64, F32], ret,
                        f"{ret.name} return under the Rust ABI"))
    add(both("hfa_fit_exact", "hfa", [*f64s(4), H4D, U64], H2F,
             "four f64 then H4d exactly fills v4-v7"))
    add(both("hfa_spill_nobackfill", "hfa", [*f64s(5), H4F, F32, U64], H2F,
             "H4f needs four of the three remaining FPRs: it goes to the stack, NSRN becomes 8 "
             "and the following f32 is not back-filled into v5"))
    add(both("hfa_after_full", "hfa", [*f64s(8), H2D, H1F, F64], H3D,
             "HFAs and a scalar after all eight FPRs are on the stack"))
    add(both("hfa_stack_align", "hfa", [*f64s(8), H3F, H1D, H3F, F32], U64,
             "12-byte H3f on the stack takes a 16-byte slot"))
    # hva: short-vector aggregates and bare vectors.
    out.append(Case("hva_args_c", "hva", "C", [V1, V2, VD2], V3, "V1 q0, V2 q1-q2, VD2 q3-q4; V3 return q0-q2"))
    for ret in (V1, V2, V4, VD2, VI2, VS2):
        out.append(Case(f"hva_ret_{ret.name.lower()}_c", "hva", "C", [U64], ret,
                        f"{ret.name} return in the vector registers"))
    out.append(Case("hva_spill_c", "hva", "C", [V4, V2, V2, V1, F64, U64], U64,
                    "V4+V2+V2 fill q0-q7; V1 and the f64 after it go to the stack"))
    out.append(Case("hva_after7_c", "hva", "C", [*([F32X4] * 7), V2, F32X4, F64], V1,
                    "a two-vector HVA with one vector register left goes to the stack, no back-fill"))
    out.append(Case("hva_mix_c", "hva", "C", [VMIX, U32], VMIX, "float32x4/int32x4 aggregate"))
    add(both("vec_bare", "hva", [F32X4, I32X4, F64X2, F32X2, U8X16, I16X4], F32X4,
             "bare 64- and 128-bit vectors in v registers"))
    # Each shape a C-ABI refusal of the cases above would hide, on its own.
    out.append(Case("vec64_bare_c", "hva", "C", [F32X2, I16X4, U64], U64, "bare 64-bit vector arguments alone"))
    out.append(Case("vec64_ret_c", "hva", "C", [U64], F32X2, "bare 64-bit vector result"))
    out.append(Case("hva_vs2_arg_c", "hva", "C", [U64, VS2, U32], U64, "VS2 (two 64-bit vectors) argument"))
    # composite: GPR-class aggregates, C.8/C.10/C.13/C.14.
    add(both("comp_small", "composite", [G3, G12, A8, MIXF, MIXFI, U32], A8,
             "G3 x0, G12 x1-x2, A8 x3-x4, MixF x5-x6; MixFI does not fit x7 and goes to the stack"))
    out.append(Case("comp_mixfi_c", "composite", "C", [U64, MIXFI, U32], U64,
                    "MixFI { f64, u64 } alone (comp_small_c's MixF refusal hides it there)"))
    add(both("comp_a8_at_x7", "composite", [*u64s(7), A8, U32], U64,
             "a 16-byte composite with one GPR left goes to the stack (NGRN becomes 8)"))
    add(both("comp_a16_at_x5", "composite", [*u64s(5), A16, U64], A16,
             "16-aligned A16 after five GPRs rounds NGRN up to x6-x7"))
    add(both("comp_a16_at_x7", "composite", [*u64s(7), A16, U8], U64,
             "16-aligned A16 at x7 goes to a 16-aligned stack slot"))
    add(both("comp_padding", "composite", [PAD, B7, S3, PAD], PAD,
             "padded and odd-sized composites in GPRs; a padded return"))
    add(both("comp_stack_small", "composite", [*u64s(8), S3, U32, G3, U16, B7, U8], U64,
             "small composites and narrow scalars on the stack"))
    # i128: C.8 even-register rounding and 16-aligned stack slots.
    add(both("i128_even", "i128", [U64, I128, U64, I128], I128,
             "x0, then i128 in x2:x3 (x1 skipped), x4, i128 in x6:x7"))
    add(both("i128_at_x7", "i128", [*u64s(7), U128, U8, I128], U128,
             "u128 at NGRN 7 goes to a 16-aligned stack slot; later arguments stay on the stack"))
    add(both("i128_stack", "i128", [*u64s(8), I128, U8, U128, I16], I128,
             "i128 and u128 interleaved with narrow scalars on the stack"))
    # sret: indirect results through x8.
    add(both("sret_a24", "sret", [U64], A24, "24-byte result through the x8 buffer"))
    add(both("sret_full_gpr", "sret", [*u64s(8), U32], A24,
             "x8 result buffer with x0-x7 full and a stack argument"))
    add(both("sret_big40", "sret", [A8, F64], BIG40, "40-byte result through x8"))
    add(both("sret_not_hfa5", "sret", [F64, F64], NOT_HFA5,
             "five f64 is not an HFA: memory result, not v0-v4"))
    out.append(Case("sret_tuple3_rust", "sret", "Rust", [U64, U64], TRIPLE_U64,
                    "Rust-ABI (u64, u64, u64) result"))
    out.append(Case("sret_array5_rust", "sret", "Rust", [U32], Array(U64, 5), "Rust-ABI [u64; 5] result"))
    # byref: caller-made copies, write-back through &mut, shared and fat references.
    out.append(Case("byref_big_copy_c", "byref", "C", [Mutated(BIG40), U64], U64,
                    "a 40-byte argument is a pointer to a caller-made copy: the callee's store into "
                    "it must not reach the caller's original"))
    out.append(Case("byref_a24_x7_c", "byref", "C", [*u64s(7), Mutated(A24), Mutated(A24), U8], U64,
                    "copy pointers in x7 and on the stack"))
    add(both("byref_mut", "byref", [Ref(U64, True), Ref(H4D, True), Ref(A24, True), Ref(U8, True),
                                     Ref(I128, True)], U64,
             "stores through &mut parameters reach the caller"))
    add(both("byref_shared", "byref", [Ref(U32, False), Ref(H3F, False), Ref(V2, False), U16], U64,
             "shared references to scalar, HFA and HVA referents"))
    out.append(Case("byref_fat_rust", "byref", "Rust",
                    [*u64s(6), Slice(U64, 3), Slice(U8, 5, text=True), Slice(U32, 4, mutable=True),
                     OptRef(U64), Slice(U8, 2)], U64,
                    "a fat pointer whole in x6:x7, then fat pointers, Option<&u64> and a &mut [u32] "
                    "write-back on the stack"))
    out.append(Case("byref_fat_split_rust", "byref", "Rust",
                    [*u64s(7), Slice(U64, 3), Slice(U8, 4, text=True), U64], U64,
                    "a fat pointer split across x7 (data) and the stack (length), then a &str and a "
                    "u64 on the stack"))
    # bool: zero-extended i1 in registers and on the stack, bool returns.
    add(both("bool_regs", "bool", [BOOL, U8, BOOL, I8, BOOL], BOOL, "bool in w0, w2, w4; bool return"))
    add(both("bool_stack", "bool", [*u64s(8), BOOL, BOOL, U8, BOOL], U64, "bool on the stack"))
    add(both("bool_struct", "bool", [BOOLS, BOOL], BOOLS, "bool fields in a composite"))
    # varargs: an LLVM-built variadic callee with a trust-cg caller, and the
    # reverse where admitted; glibc snprintf from each caller.
    out.append(Case("va_ints_regs_c", "varargs", "C", [U32], U64, "four anonymous integers in x1-x4",
                    variadic=[I32, U32, I64, U64]))
    out.append(Case("va_ints_stack_c", "varargs", "C", [U32], U64,
                    "twelve anonymous integers: x1-x7 then the stack",
                    variadic=[I32, U64, U32, I64, I32, USIZE, I64, U32, I32, U64, ISIZE, I32]))
    out.append(Case("va_f64_c", "varargs", "C", [U32], U64,
                    "ten anonymous doubles: v0-v7 then the stack (AAPCS64, not DarwinPCS)",
                    variadic=[F64] * 10))
    out.append(Case("va_after_fixed_c", "varargs", "C", [*u64s(7), *f64s(7)], U64,
                    "anonymous arguments after seven fixed GPR and FPR arguments: x7, d7, then the stack",
                    variadic=[I32, F64, U64, F64, I64, F64, F64, U32]))
    # Over-aligned FIXED arguments of a C-variadic callee, which rustc's call
    # FnAbi places as for any C function: a padded newtype as [2 x i64] or one
    # integer, a struct around a 16-aligned member as i128, a 16-aligned pair
    # as [2 x i64]; at NGRN 1, and on the stack after an 8-byte slot.
    for label, ty in (("oa16u64", OA16_U64), ("oa16u8", OA16_U8), ("oa2", OA2), ("oawrap16", OA_WRAP16),
                      ("oa16", OA16)):
        out.append(Case(f"va_{label}_x1_c", "varargs", "C", [U64, ty, U64], U64,
                        f"{ty.rust()} as a fixed argument at NGRN 1 of a C-variadic callee, then a fixed "
                        "u64 and one anonymous u64",
                        variadic=[U64]))
    out.append(Case("va_oawrap16_s8_c", "varargs", "C", [*u64s(8), U8, OA_WRAP16], U64,
                    "OaWrap16 as a fixed argument on the stack after an 8-byte slot, then two anonymous u64",
                    variadic=[U64, U64]))
    # No anonymous argument, by a direct call and through a C-variadic `fn`
    # pointer. A pointer call that passes none has as many arguments as the
    # pointer has inputs, so it takes the ordinary fn-pointer call route (no
    # argument-count refusal); the fixed arguments are placed as for any C
    # function, so the over-aligned ones repeat the direct-call shapes above.
    out.append(Case("va_none_c", "varargs", "C", [U64, U32, F64, I16], U64,
                    "a direct C-variadic call with no anonymous argument", variadic=[]))
    out.append(Case("va_ptr_none_c", "varargs", "C", [U64, U32, F64, I16], U64,
                    "a call through a C-variadic fn pointer with no anonymous argument", variadic=[],
                    via_pointer=True))
    for label, ty in (("oa16u64", OA16_U64), ("oa16u8", OA16_U8), ("oa2", OA2), ("oawrap16", OA_WRAP16),
                      ("oa16", OA16)):
        out.append(Case(f"va_ptr_{label}_x1_c", "varargs", "C", [U64, ty, U64], U64,
                        f"{ty.rust()} as a fixed argument at NGRN 1, then a fixed u64, through a C-variadic "
                        "fn pointer with no anonymous argument",
                        variadic=[], via_pointer=True))
    out.append(Case("va_ptr_oawrap16_s8_c", "varargs", "C", [*u64s(8), U8, OA_WRAP16], U64,
                    "OaWrap16 on the stack after an 8-byte slot, through a C-variadic fn pointer with no "
                    "anonymous argument", variadic=[], via_pointer=True))
    out.append(Case("va_ptr_anon_c", "varargs", "C", [U32], U64,
                    "a call through a C-variadic fn pointer WITH anonymous arguments", variadic=[I32, U64],
                    via_pointer=True))
    out.append(Case("va_libc_snprintf_c", "varargs", "C", [], U64,
                    "glibc snprintf with 12 integer and 10 double anonymous arguments", libc=True))
    # callback: the callee calls back into the other crate through a fn pointer.
    add(both("cb_ints", "callback", [], U64, "callee-built narrow integer arguments to a callback",
             callback=([U8, I16, U32, I64, U64, I8, U16, I32, U64, U64], U64)))
    add(both("cb_hfa", "callback", [], U64, "HFA and float arguments to a callback, H3f result",
             callback=([H4D, F64, F64, F64, F64, F64, H2F], H3F)))
    add(both("cb_sret", "callback", [], U64, "callback result through x8",
             callback=([U64, U32], A24)))
    add(both("cb_i128", "callback", [], U64, "i128 callback arguments at C.8 and on the stack",
             callback=([U64, I128, U64, U64, U64, U64, U64, I128], I128)))
    # exhaustion: Rust-ABI Cast aggregates and scalar pairs at the register/stack
    # boundary (LIMITATIONS.md "Register exhaustion" shapes).
    rust_stack = [
        ("u8x4", Array(U8, 4), U32), ("s3", S3R, U32), ("u8x2", Array(U8, 2), U16),
        ("u8x1", Array(U8, 1), U8), ("u16x1", Array(U16, 1), U16), ("f32x1", Array(F32, 1), U32),
        ("tup", Tuple(U8, Array(U8, 2)), U8), ("u8x6", Array(U8, 6), U32),
    ]
    for label, ty, tail in rust_stack:
        out.append(Case(f"exh_{label}_rust", "exhaustion", "Rust", [*u64s(8), ty, tail], U64,
                        f"Rust-ABI {ty.rust()} after eight u64, then a {tail.rust()}"))
    for label, prefix, pair, tail in (
            ("pair_u64", U64, PAIR_U64, U64), ("pair_f64", F64, PAIR_F64, F64),
            ("pair_f32", F32, PAIR_F32, F32), ("opt_u64", U64, Opt(U64), U64)):
        out.append(Case(f"exh_{label}_rust", "exhaustion", "Rust", [*([prefix] * 7), pair, tail], U64,
                        f"Rust-ABI {pair.rust()} at the last register, then a {tail.rust()}"))
    # spill: long signatures that exhaust both banks.
    add(both("spill_ints", "spill",
             [U8, I8, U16, I16, U32, I32, U64, I64, U8, I16, U32, I64, U8, U16, I32, U64, I8, U16, U32, I64],
             U64, "twenty integers: twelve on the stack"))
    add(both("spill_floats", "spill",
             [F32, F64, F64, F32, F64, F32, F64, F64, F32, F32, F64, F32, F64, F64, F32, F64, F32, F64, F64, F32],
             F64, "twenty floats: twelve on the stack"))
    out.append(Case("spill_all_c", "spill", "C",
                    [U8, F32, H2F, I128, BOOL, A8, F64, G3, H3D, U16, I32, F32X4, A16, F64, U64, BOOL,
                     H4F, I8, S3, F32, U128, MIXF, F64, U32, V2, I64, F32, B7, H1D, U8, I16, F64],
                    A24, "thirty-two mixed arguments exhaust both banks"))
    # The same thirty-two arguments with the three shapes the bridge refuses
    # (float32x4_t, V2, MixF) replaced by executable ones of the same bank
    # (H2d, H4d, G12), so the mixed stack-placed composites run as one
    # signature.
    out.append(Case("spill_all_exec_c", "spill", "C",
                    [U8, F32, H2F, I128, BOOL, A8, F64, G3, H3D, U16, I32, H2D, A16, F64, U64, BOOL,
                     H4F, I8, S3, F32, U128, G12, F64, U32, H4D, I64, F32, B7, H1D, U8, I16, F64],
                    A24, "thirty-two mixed arguments exhaust both banks, every shape executable"))
    out.extend(layout_cases())
    out.extend(random_cases())
    names = [case.name for case in out]
    assert len(names) == len(set(names)), "duplicate case name"
    return out


def is_float_homogeneous(ty) -> bool:
    """A composite whose every leaf is f32 or f64 (it may still be no HFA)."""
    if isinstance(ty, Struct):
        return all(is_float_homogeneous(field) for _, field in ty.fields)
    if isinstance(ty, Array):
        return is_float_homogeneous(ty.element)
    if isinstance(ty, Union):
        return all(is_float_homogeneous(field) for _, field in ty.fields)
    return isinstance(ty, Float)


def type_label(ty) -> str:
    if isinstance(ty, (Struct, Union, Enum)):
        return ty.name.lower()
    return ty.rust().replace("core::num::", "").replace("Option<", "o").replace(">", "").lower()


def layout_arg_case(family: str, abi: str, ty) -> Case:
    """`ty` twice: once in registers after one scalar of its own bank (and a
    narrow scalar after it), once on the stack after that bank is exhausted,
    then a narrow scalar after it on the stack, which a slot of the wrong
    size or alignment shifts."""
    if is_float_homogeneous(ty):
        params = [F64, ty, F32, *f64s(6), ty, F32, U16]
        rule = f"{ty.rust()} after one f64, then again after the FPRs are exhausted"
    else:
        params = [U64, ty, U8, *u64s(6), ty, U16]
        rule = f"{ty.rust()} after one u64, then again on the stack after the GPRs are exhausted"
    return Case(f"{family[:2]}_{type_label(ty)}_{'c' if abi == 'C' else 'rust'}", family, abi, params, U64,
                f"{abi}-ABI {rule}")


def layout_ret_case(family: str, abi: str, ty) -> Case:
    return Case(f"{family[:2]}_ret_{type_label(ty)}_{'c' if abi == 'C' else 'rust'}", family, abi, [U64, F32],
                ty, f"{abi}-ABI {ty.rust()} result")


def layout_cases() -> list[Case]:
    """Over-aligned, packed, union, payload-enum and niche shapes."""
    out: list[Case] = []
    # overalign: every GPR position (k scalars before it, k = 0..8, 8 = the
    # stack) for the two shapes whose natural and declared alignments differ
    # most, under both ABIs; then each over-aligned shape in registers and on
    # the stack, and as a result.
    for abi, shapes in (("C", (("oa16", OA16), ("oa16u32", OA16_U32))),
                        ("Rust", (("roa16", ROA16), ("roa16u32", ROA16_U32)))):
        for label, ty in shapes:
            for k in range(9):
                where = "the stack" if k == 8 else f"NGRN {k}"
                out.append(Case(f"ov_{label}_x{k}_{'c' if abi == 'C' else 'rust'}", "overalign", abi,
                                [*u64s(k), ty, U64], U64,
                                f"{abi}-ABI {ty.rust()} ({ty.repr}) at {where}, then a u64"))
            # On the stack after an 8-byte slot: NSAA 8, where a 16-aligned
            # slot and an 8-aligned one differ.
            out.append(Case(f"ov_{label}_s8_{'c' if abi == 'C' else 'rust'}", "overalign", abi,
                            [*u64s(8), U8, ty, U64], U64,
                            f"{abi}-ABI {ty.rust()} ({ty.repr}) on the stack after one 8-byte stack slot"))
    for k in (0, 1, 5, 6, 7):
        out.append(Case(f"ov_oa16f64x2_d{k}_c", "overalign", "C", [*f64s(k), OA16_F64X2, F64], U64,
                        f"C-ABI align(16) {{f64, f64}} after {k} f64, then an f64"))
    for ty in (OA2, OA4, OA8, OA16_U8, OA16_U64, OA16_U32X3, OA8_U32X3, OA16_F64X2, OA16_F32X2, OA16_MIX,
               OA32, OA64, OA32_F32X4, OA_WRAP16, OA_WRAP8, OA_IN16, OA_WRAP_HFA):
        out.append(layout_arg_case("overalign", "C", ty))
    for ty in (ROA8_U8X3, ROA16_F32X2, ROA32, ROA4_U16, ROA_WRAP, OA2, OA16_U32X3, OA16_F64X2, OA_WRAP16, OA64):
        out.append(layout_arg_case("overalign", "Rust", ty))
    for ty in (OA2, OA4, OA8, OA16_U8, OA16_U32, OA16_U64, OA16, OA16_U32X3, OA8_U32X3, OA16_F64X2, OA16_F32X2,
               OA16_MIX, OA32, OA_WRAP16, OA_IN16):
        out.append(layout_ret_case("overalign", "C", ty))
    for ty in (ROA16, ROA16_U32, ROA8_U8X3, ROA16_F32X2, ROA32, ROA4_U16, OA16, OA16_F64X2):
        out.append(layout_ret_case("overalign", "Rust", ty))
    # packed
    for ty in (PK, PK_AL, PK2, PK_F, PK_BIG):
        out.append(layout_arg_case("packed", "C", ty))
    for ty in (PK, PK_AL, PK2, PK_F):
        out.append(layout_ret_case("packed", "C", ty))
    for ty in (RPK, RPK2, PK_AL, PK_BIG):
        out.append(layout_arg_case("packed", "Rust", ty))
    for ty in (RPK, RPK2, PK):
        out.append(layout_ret_case("packed", "Rust", ty))
    # union
    for ty in (UN_INT, UN_MIX, UN_HFA, UN_16, UN_24, UN_SMALL):
        out.append(layout_arg_case("union", "C", ty))
    for ty in (UN_INT, UN_HFA, UN_16, UN_SMALL):
        out.append(layout_ret_case("union", "C", ty))
    for ty in (UN_INT, UN_16, RUN_INT, UN_HFA):
        out.append(layout_arg_case("union", "Rust", ty))
    for ty in (RUN_INT, UN_16):
        out.append(layout_ret_case("union", "Rust", ty))
    # enum: payload enums, Rust layout under the Rust ABI, RFC 2195 layouts under C.
    for ty in (EP, EF, EB, E16, E24):
        out.append(layout_arg_case("enum", "Rust", ty))
        out.append(layout_ret_case("enum", "Rust", ty))
    for ty in (ECR, ECR32):
        out.append(layout_arg_case("enum", "C", ty))
        out.append(layout_ret_case("enum", "C", ty))
    # niche: NonZero integers, Option<NonZero*>, Option<bool>, Option<char>.
    add = out.extend
    add(both("ni_regs", "niche", [ONZ8, NZ16, ONZ32, OBOOL, OCHAR, ONZ64, NZI32], ONZ32,
             "niche-carrying scalars in x0-x6; Option<NonZeroU32> result"))
    add(both("ni_x7", "niche", [*u64s(7), ONZ64, ONZ32], OBOOL,
             "Option<NonZeroU64> at x7, then one on the stack; Option<bool> result"))
    add(both("ni_stack", "niche", [*u64s(8), ONZ8, OBOOL, ONZ64, OCHAR, NZ16], ONZ64,
             "niche-carrying scalars on the stack; Option<NonZeroU64> result"))
    add(both("ni_u128", "niche", [U64, ONZ128, U64, NZ128], ONZ128,
             "16-aligned niche scalars at C.8 even registers; Option<NonZeroU128> result"))
    add(both("ni_ret_bool", "niche", [U64], OBOOL, "Option<bool> result"))
    add(both("ni_ret_char", "niche", [U64], OCHAR, "Option<char> result"))
    return out


# The random family exists to vary PLACEMENT (which register or stack slot an
# argument lands in after which others), so its pools leave out the shapes a
# named case already pins as a trust-cg refusal under that ABI: a declined
# random signature executes nothing. Those shapes stay in the named families
# (comp_small_c and vec_bare_c for the C pool; hfa_args_rust and, for the
# result, comp_a16_at_x5_rust for the Rust pool), where each refusal is
# listed by name.
RANDOM_POOL_COMMON = [U8, I8, U16, I16, U32, I32, U64, I64, U128, I128, BOOL, F32, F64, H2F, H3F, H4F, H2D,
                      H3D, H4D, A8, A16, G3, G12, S3, PAD, V2, A24]
RANDOM_POOL = {"C": [*RANDOM_POOL_COMMON, H1F], "Rust": [*RANDOM_POOL_COMMON, MIXF, F32X4]}
RANDOM_RETS_COMMON = [U64, I8, U16, BOOL, F32, F64, I128, H2F, H4D, A8, A24, G12, V2, NOT_HFA5]
# A Rust-ABI A16 result is pinned as a refusal by comp_a16_at_x5_rust.
RANDOM_RETS = {"C": [*RANDOM_RETS_COMMON, A16], "Rust": RANDOM_RETS_COMMON}
RANDOM_SEEDS = range(1, 41)


def random_cases() -> list[Case]:
    """Seeded mixed signatures, odd seeds under the C ABI, even under Rust's."""
    out = []
    for seed in RANDOM_SEEDS:
        abi = "C" if seed % 2 else "Rust"
        rng = random.Random(0xAB1 * 1000 + seed)
        params = [rng.choice(RANDOM_POOL[abi]) for _ in range(rng.randrange(9, 26))]
        ret = rng.choice(RANDOM_RETS[abi])
        out.append(Case(f"rand{seed:02d}_{'c' if abi == 'C' else 'rust'}", "random", abi, params, ret,
                        f"seeded mixed signature of {len(params)} arguments"))
    return out


# --- emission -----------------------------------------------------------

def fold_lines(acc: str, words: list[str], indent: str) -> list[str]:
    return [f"{indent}{acc} = {acc}.wrapping_mul(31).wrapping_add({word});" for word in words]


def callee_signature(case: Case, name: str) -> str:
    params = [f"p{index}: {param.rust()}" for index, param in enumerate(case.params)]
    if case.callback is not None:
        cb_params, cb_ret = case.callback
        pointer = "extern \"C\" fn" if case.abi == "C" else "fn"
        params = [f"cb: {pointer}({', '.join(ty.rust() for ty in cb_params)}) -> {cb_ret.rust()}",
                  "seed: u64"]
    if case.variadic is not None:
        params.append("...")
    return f"{name}({', '.join(params)}) -> {case.ret.rust()}"


def variadic_pointer_type(case: Case) -> str:
    """The C-variadic `fn` pointer type a `via_pointer` case is called through."""
    inputs = [param.rust() for param in case.params] + ["..."]
    return f"unsafe extern \"C\" fn({', '.join(inputs)}) -> {case.ret.rust()}"


def param_words_rs(param, name: str) -> list[str]:
    if isinstance(param, Ref):
        return param.inner.fold(f"*{name}")
    if isinstance(param, Mutated):
        return param.inner.fold(name)
    if isinstance(param, OptRef):
        payload = param.inner.fold("*r")
        return [f"{name}.is_some() as u64", f"(match {name} {{ Some(r) => {payload[0]}, None => 0 }})"]
    raise TypeError(param)


def first_leaf(ty, path: str):
    """The place expression and type of the first scalar inside `ty`."""
    if isinstance(ty, Struct):
        name, field = ty.fields[0]
        return first_leaf(field, f"{path}.{name}")
    if isinstance(ty, Array):
        return first_leaf(ty.element, f"{path}[0]")
    if isinstance(ty, Tuple):
        return first_leaf(ty.items[0], f"{path}.0")
    return path, ty


def emit_callee_fn(case: Case) -> str:
    lines = []
    attributes = "#[inline(never)]\n"
    if case.abi == "C":
        attributes += "#[no_mangle]\n"
        qualifier = "pub unsafe extern \"C\" fn" if case.variadic is not None else "pub extern \"C\" fn"
    else:
        qualifier = "pub fn"
    signature = callee_signature(case, case.name)
    if case.variadic is not None:
        signature = signature.replace("...", "mut ap: ...")
    lines.append(f"{attributes}{qualifier} {signature} {{")
    lines.append(f"    let mut acc: u64 = 0x{case.seed:08x}u64;")
    if case.callback is not None:
        cb_params, cb_ret = case.callback
        lines.append("    acc = acc.wrapping_mul(31).wrapping_add(seed);")
        salt = 1
        args = []
        for index, ty in enumerate(cb_params):
            expr, salt = ty.build_rs("acc", salt)
            lines.append(f"    let a{index}: {ty.rust()} = {expr};")
            args.append(f"a{index}")
        lines.append(f"    let r: {cb_ret.rust()} = cb({', '.join(args)});")
        lines.extend(fold_lines("acc", cb_ret.fold("r"), "    "))
        lines.append("    acc")
        lines.append("}")
        return "\n".join(lines) + "\n"
    for index, param in enumerate(case.params):
        name = f"p{index}"
        if isinstance(param, Slice):
            lines.append(f"    acc = acc.wrapping_mul(31).wrapping_add({name}.len() as u64);")
            if param.text:
                lines.append(f"    let b{index} = {name}.as_bytes();")
                lines.append(f"    let mut i{index} = 0usize;")
                lines.append(f"    while i{index} < b{index}.len() {{ acc = acc.wrapping_mul(31)"
                             f".wrapping_add(b{index}[i{index}] as u64); i{index} += 1; }}")
            else:
                lines.append(f"    let mut i{index} = 0usize;")
                words = param.element.fold(f"{name}[i{index}]")
                body = " ".join(f"acc = acc.wrapping_mul(31).wrapping_add({word});" for word in words)
                lines.append(f"    while i{index} < {name}.len() {{ {body} i{index} += 1; }}")
        elif isinstance(param, (Ref, Mutated, OptRef)):
            lines.extend(fold_lines("acc", param_words_rs(param, name), "    "))
        else:
            lines.extend(fold_lines("acc", param.fold(name), "    "))
    for index, ty in enumerate(case.variadic or []):
        lines.append(f"    let v{index}: {ty.rust()} = ap.next_arg::<{ty.rust()}>();")
        lines.extend(fold_lines("acc", ty.fold(f"v{index}"), "    "))
    # Stores, after the whole fold, in parameter order.
    for index, param in enumerate(case.params):
        name = f"p{index}"
        if isinstance(param, Ref) and param.mutable:
            expr, _ = param.inner.build_rs("acc", 1000 + 100 * index)
            lines.append(f"    *{name} = {expr};")
        elif isinstance(param, Slice) and param.mutable:
            expr, _ = param.element.build_rs("acc", 1000 + 100 * index)
            lines.append(f"    {name}[0] = {expr};")
        elif isinstance(param, Mutated):
            # The store is to the callee's own copy and is otherwise dead;
            # black-boxing the copy's address keeps it. It overwrites the first
            # scalar of the copy, so a caller that handed over its original
            # (instead of a fresh copy) sees its value change. (A volatile
            # store would do the same, but the bridge refuses the
            # `volatile_store` intrinsic.)
            path, leaf = first_leaf(param.inner, name)
            expr, _ = leaf.build_rs("acc", 1000 + 100 * index)
            lines.append(f"    {path} = {expr};")
            lines.append(f"    core::hint::black_box(&mut {name});")
    expr, _ = case.ret.build_rs("acc", 1)
    lines.append(f"    {expr}")
    lines.append("}")
    if case.via_pointer:
        # The getter the caller reaches the callee through (a Rust-ABI call
        # returning the C-variadic fn pointer).
        lines.append("#[inline(never)]")
        lines.append(f"pub fn {case.name}_ptr() -> {variadic_pointer_type(case)} {{")
        lines.append(f"    {case.name}")
        lines.append("}")
    text = "\n".join(lines) + "\n"
    if any(isinstance(param, Mutated) for param in case.params):
        for index, param in enumerate(case.params):
            if isinstance(param, Mutated):
                text = text.replace(f"p{index}: {param.rust()}", f"mut p{index}: {param.rust()}", 1)
    return text


def emit_callback_impl(case: Case) -> str:
    cb_params, cb_ret = case.callback
    qualifier = "extern \"C\" fn" if case.abi == "C" else "fn"
    params = ", ".join(f"q{index}: {ty.rust()}" for index, ty in enumerate(cb_params))
    lines = ["#[inline(never)]", f"{qualifier} cbimpl_{case.name}({params}) -> {cb_ret.rust()} {{",
             f"    let mut acc: u64 = 0x{case.seed ^ 0x5A5A5A5A:08x}u64;"]
    for index, ty in enumerate(cb_params):
        lines.extend(fold_lines("acc", ty.fold(f"q{index}"), "    "))
    expr, _ = cb_ret.build_rs("acc", 7)
    lines.append(f"    {expr}")
    lines.append("}")
    return "\n".join(lines) + "\n"


def case_inputs(case: Case):
    rng = random.Random(case.seed)
    return [draw_param(param, rng) for param in case.params], \
        [ty.draw(rng) for ty in (case.variadic or [])], rng


def draw_param(param, rng):
    if isinstance(param, (Ref, Mutated)):
        return param.inner.draw(rng)
    if isinstance(param, OptRef):
        return None if rng.random() < 0.3 else param.inner.draw(rng)
    if isinstance(param, Slice):
        if param.text:
            return "".join(rng.choice("abcdefghijklmnopqrstuvwxyz") for _ in range(param.count))
        return [param.element.draw(rng) for _ in range(param.count)]
    return param.draw(rng)


def opaque(ty, value, rng: random.Random) -> str:
    """A caller-side expression for `value` the optimizer cannot fold.

    `black_box` is applied to SCALAR leaves only: it is itself a Rust-ABI call,
    so a black-boxed aggregate would put a second, unrelated call (with its own
    Rust-ABI aggregate placement) in front of the C call under test. Narrow
    integers are truncated from a wider black-boxed value, so their upper
    register bits are not zero.
    """
    if isinstance(ty, Struct):
        fields = ", ".join(f"{name}: {opaque(field, item, rng)}"
                           for (name, field), item in zip(ty.fields, value))
        return f"{ty.name} {{ {fields} }}"
    if isinstance(ty, Array):
        return "[" + ", ".join(opaque(ty.element, item, rng) for item in value) + "]"
    if isinstance(ty, Tuple):
        return "(" + ", ".join(opaque(item_ty, item, rng) for item_ty, item in zip(ty.items, value)) + ")"
    if isinstance(ty, Vector):
        lanes = ", ".join(opaque(ty.lane, lane, rng) for lane in value)
        return f"unsafe {{ core::mem::transmute::<{ty.array()}, {ty.name}>([{lanes}]) }}"
    if isinstance(ty, Opt):
        return "None" if value is None else f"Some({opaque(ty.inner, value, rng)})"
    if isinstance(ty, Union):
        name, field = ty.carrier()
        return f"{ty.name} {{ {name}: {opaque(field, value, rng)} }}"
    if isinstance(ty, Enum):
        index, payload = value
        payload_ty = ty.variants[index][1]
        return ty.variant_expr(index, None if payload_ty is None else opaque(payload_ty, payload, rng))
    if isinstance(ty, NonZero):
        return f"unsafe {{ {ty.path}::new_unchecked({opaque(ty.inner, value, rng)}) }}"
    if getattr(ty, "narrow", False):
        return ty.dirty_literal(value, rng)
    return f"bb({ty.literal(value)})"


LIVE_INTS, LIVE_FLOATS = 10, 8


def live_across(seed: int) -> tuple[list[str], list[str], int]:
    """Values the caller keeps live across the call under test.

    Ten u64 and eight f64 black-boxed before the call and folded after it.
    Where they live across the call is each compiler's choice: a callee-saved
    register (x19-x28, d8-d15) or the caller's own frame. A callee that
    clobbers a callee-saved register or the caller's frame without restoring
    it changes the printed `live=` field, and so does a caller that parks one
    in a caller-saved register across the call. Nothing here forces a value
    into a particular register. Returns the setup lines, the fold lines and
    the expected fold.
    """
    rng = random.Random(seed ^ 0x11FE5AFE)
    ints = [rng.getrandbits(64) for _ in range(LIVE_INTS)]
    floats = [F64.draw(rng) for _ in range(LIVE_FLOATS)]
    setup = [f"    let s{index}: u64 = bb(0x{value:016x}u64);" for index, value in enumerate(ints)]
    setup += [f"    let t{index}: f64 = bb({F64.literal(value)});" for index, value in enumerate(floats)]
    fold = ["    let mut live: u64 = 0;"]
    fold += [f"    live = live.wrapping_mul(31).wrapping_add(s{index});" for index in range(LIVE_INTS)]
    fold += [f"    live = live.wrapping_mul(31).wrapping_add(t{index}.to_bits());" for index in range(LIVE_FLOATS)]
    fold += ["    put_str(&mut line, &mut n, b\" live=\");", "    put_hex(&mut line, &mut n, live);"]
    expected = fold_all(0, [*ints, *(f64_bits(value) for value in floats)])
    return setup, fold, expected


def emit_caller_case(case: Case) -> str:
    if case.libc:
        return emit_libc_case(case)
    values, anonymous, rng = case_inputs(case)
    lines = ["#[inline(never)]", f"fn case_{case.name}() {{"]
    args = []
    printed = []
    for index, (param, value) in enumerate(zip(case.params, values)):
        if isinstance(param, Ref):
            binding = "mut " if param.mutable else ""
            lines.append(f"    let {binding}l{index}: {param.inner.rust()} = {opaque(param.inner, value, rng)};")
            args.append(f"&mut l{index}" if param.mutable else f"&l{index}")
            if param.mutable:
                printed.append((f"l{index}", param.inner))
        elif isinstance(param, Mutated):
            lines.append(f"    let l{index}: {param.inner.rust()} = {opaque(param.inner, value, rng)};")
            args.append(f"l{index}")
            printed.append((f"l{index}", param.inner))
        elif isinstance(param, OptRef):
            payload = 0 if value is None else value
            lines.append(f"    let l{index}: {param.inner.rust()} = {opaque(param.inner, payload, rng)};")
            args.append("None" if value is None else f"Some(&l{index})")
        elif isinstance(param, Slice):
            if param.text:
                lines.append(f"    let l{index}: &str = bb(\"{value}\");")
                args.append(f"l{index}")
            else:
                array = Array(param.element, param.count)
                binding = "mut " if param.mutable else ""
                lines.append(f"    let {binding}l{index}: {array.rust()} = {opaque(array, value, rng)};")
                args.append(f"&mut l{index}[..]" if param.mutable else f"&l{index}[..]")
                if param.mutable:
                    printed.append((f"l{index}", array))
        else:
            args.append(opaque(param, value, rng))
    for ty, value in zip(case.variadic or [], anonymous):
        args.append(f"bb({ty.literal(value)})")
    if case.callback is not None:
        args = [f"cbimpl_{case.name}", f"bb(0x{case.seed * 7 & MASK:x}u64)"]
    if case.via_pointer:
        lines.append(f"    let f: {variadic_pointer_type(case)} = bb(xcallee::{case.name}_ptr());")
    live_setup, live_fold, _ = live_across(case.seed)
    lines.extend(live_setup)
    if case.via_pointer:
        call = f"f({', '.join(args)})"
    elif case.abi == "C":
        call = f"{case.name}({', '.join(args)})"
    else:
        call = f"xcallee::{case.name}({', '.join(args)})"
    lines.append(f"    let r: {case.ret.rust()} = unsafe {{ {call} }};" if case.abi == "C"
                 else f"    let r: {case.ret.rust()} = {call};")
    lines.append("    let mut acc: u64 = 0;")
    lines.extend(fold_lines("acc", case.ret.fold("r"), "    "))
    lines.append("    let mut line = [0u8; 512];")
    lines.append("    let mut n = 0usize;")
    lines.append(f"    put_str(&mut line, &mut n, b\"{case.name} ret=\");")
    lines.append("    put_hex(&mut line, &mut n, acc);")
    for index, (local, ty) in enumerate(printed):
        lines.append(f"    let mut k{index}: u64 = 0;")
        lines.extend(fold_lines(f"k{index}", ty.fold(local), "    "))
        lines.append(f"    put_str(&mut line, &mut n, b\" {local}=\");")
        lines.append(f"    put_hex(&mut line, &mut n, k{index});")
    lines.extend(live_fold)
    lines.append("    emit_line(&mut line, n);")
    lines.append("}")
    return "\n".join(lines) + "\n"


LIBC_INTS = [I32, U32, I64, U64, I32, I64, U32, I32, U64, I64, I32, U32]
LIBC_FMT = {"i32": "%d", "u32": "%u", "i64": "%ld", "u64": "%lu"}


def libc_values(case: Case):
    rng = random.Random(case.seed)
    ints = [ty.draw(rng) for ty in LIBC_INTS]
    doubles = [F64.draw(rng) for _ in range(10)]
    return ints, doubles


def emit_libc_case(case: Case) -> str:
    ints, doubles = libc_values(case)
    fmt = "|".join([LIBC_FMT[ty.rust()] for ty in LIBC_INTS] + ["%.2f"] * 10)
    args = [f"bb({ty.literal(value)})" for ty, value in zip(LIBC_INTS, ints)]
    args += [f"bb({F64.literal(value)})" for value in doubles]
    live_setup, live_fold, _ = live_across(case.seed)
    return (
        "#[inline(never)]\n"
        f"fn case_{case.name}() {{\n"
        + "".join(line + "\n" for line in live_setup) +
        "    let mut buf = [0u8; 512];\n"
        f"    let fmt = b\"{fmt}\\0\";\n"
        "    let n = unsafe { snprintf(buf.as_mut_ptr(), buf.len(), fmt.as_ptr(), "
        f"{', '.join(args)}) }};\n"
        "    let mut acc: u64 = n as i64 as u64;\n"
        "    let mut i = 0usize;\n"
        "    while i < buf.len() { acc = acc.wrapping_mul(31).wrapping_add(buf[i] as u64); i += 1; }\n"
        "    let mut line = [0u8; 512];\n"
        "    let mut n = 0usize;\n"
        f"    put_str(&mut line, &mut n, b\"{case.name} ret=\");\n"
        "    put_hex(&mut line, &mut n, acc);\n"
        + "".join(line + "\n" for line in live_fold) +
        "    emit_line(&mut line, n);\n"
        "}\n"
    )


def expected_line(case: Case) -> str:
    if case.libc:
        ints, doubles = libc_values(case)
        text = "|".join([str(value) for value in ints] + [f"{value:.2f}" for value in doubles])
        data = text.encode()
        buffer = data + bytes(512 - len(data))
        acc = len(data) & MASK
        for byte in buffer:
            acc = fold_word(acc, byte)
        return f"{case.name} ret={acc:016x} live={live_across(case.seed)[2]:016x}"
    values, anonymous, _ = case_inputs(case)
    acc = case.seed
    printed = []
    if case.callback is not None:
        cb_params, cb_ret = case.callback
        acc = fold_word(acc, (case.seed * 7) & MASK)
        salt = 1
        args = []
        for ty in cb_params:
            value, salt = ty.build(acc, salt)
            args.append(value)
        inner = (case.seed ^ 0x5A5A5A5A) & MASK
        for ty, value in zip(cb_params, args):
            for word in ty.words(value):
                inner = fold_word(inner, word)
        result, _ = cb_ret.build(inner, 7)
        for word in cb_ret.words(result):
            acc = fold_word(acc, word)
        ret_words = U64.words(acc)
        return f"{case.name} ret={fold_all(0, ret_words):016x} live={live_across(case.seed)[2]:016x}"
    for param, value in zip(case.params, values):
        if isinstance(param, Slice):
            if param.text:
                data = value.encode()
                acc = fold_word(acc, len(data))
                for byte in data:
                    acc = fold_word(acc, byte)
            else:
                acc = fold_word(acc, len(value))
                for item in value:
                    for word in param.element.words(item):
                        acc = fold_word(acc, word)
        elif isinstance(param, OptRef):
            acc = fold_word(acc, 0 if value is None else 1)
            acc = fold_word(acc, 0 if value is None else param.inner.words(value)[0])
        elif isinstance(param, (Ref, Mutated)):
            for word in param.inner.words(value):
                acc = fold_word(acc, word)
        else:
            for word in param.words(value):
                acc = fold_word(acc, word)
    for ty, value in zip(case.variadic or [], anonymous):
        for word in ty.words(value):
            acc = fold_word(acc, word)
    for index, (param, value) in enumerate(zip(case.params, values)):
        if isinstance(param, Ref) and param.mutable:
            stored, _ = param.inner.build(acc, 1000 + 100 * index)
            printed.append((f"l{index}", param.inner.words(stored)))
        elif isinstance(param, Slice) and param.mutable:
            stored, _ = param.element.build(acc, 1000 + 100 * index)
            items = [stored, *value[1:]]
            printed.append((f"l{index}", [w for item in items for w in param.element.words(item)]))
        elif isinstance(param, Mutated):
            # The caller's original is unchanged by the callee's store.
            printed.append((f"l{index}", param.inner.words(value)))
    result, _ = case.ret.build(acc, 1)
    parts = [f"{case.name} ret={fold_all(0, case.ret.words(result)):016x}"]
    parts += [f"{local}={fold_all(0, words):016x}" for local, words in printed]
    parts.append(f"live={live_across(case.seed)[2]:016x}")
    return " ".join(parts)


def fold_all(acc: int, words: list[int]) -> int:
    for word in words:
        acc = fold_word(acc, word)
    return acc


PRELUDE = """#![allow(unused, dead_code, improper_ctypes, improper_ctypes_definitions)]
use core::arch::aarch64::*;
"""

# The caller prints with plain byte stores and one write(2) per line: no
# `core::fmt`, so the printing path is the same small code under either
# backend, and a line already written survives a crash later in the process.
CALLER_RUNTIME = """extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

#[inline(never)]
fn put_str(line: &mut [u8; 512], n: &mut usize, text: &[u8]) {
    let mut i = 0usize;
    while i < text.len() {
        line[*n] = text[i];
        *n += 1;
        i += 1;
    }
}

#[inline(never)]
fn put_hex(line: &mut [u8; 512], n: &mut usize, value: u64) {
    let mut k = 0u32;
    while k < 16 {
        let digit = ((value >> (60 - 4 * k)) & 0xF) as u8;
        line[*n] = if digit < 10 { b'0' + digit } else { b'a' + digit - 10 };
        *n += 1;
        k += 1;
    }
}

#[inline(never)]
fn emit_line(line: &mut [u8; 512], n: usize) {
    line[n] = b'\\n';
    unsafe {
        write(1, line.as_ptr(), n + 1);
    }
}
"""


def uses_layout_types(case: Case) -> bool:
    """Whether the case's crate needs the layout families' type declarations:
    it belongs to one, or its signature names one of their types directly."""
    if case.family in LAYOUT_FAMILIES:
        return True
    signature = [*case.params, case.ret, *(case.variadic or [])]
    return any(ty is layout for ty in signature for layout in LAYOUT_TYPES)


def group_sources(group: str, members: list[Case]) -> tuple[str, str, dict]:
    variadic = any(case.variadic is not None for case in members)
    callee = ["// Generated by benchmarks/abi-xback/families.py; do not edit.\n"]
    if variadic:
        callee.append("#![feature(c_variadic)]\n")
    callee.append(f"#![crate_type = \"rlib\"]\n#![crate_name = \"xcallee\"]\n{PRELUDE}\n")
    callee.extend(struct.declaration() + "\n" for struct in STRUCTS)
    if any(uses_layout_types(case) for case in members):
        callee.extend(ty.declaration() + "\n" for ty in LAYOUT_TYPES)
    for case in members:
        if not case.libc:
            callee.append(emit_callee_fn(case) + "\n")
    # A bare SIMD vector in an `extern "C"` block declaration is a hard
    # frontend error without `simd_ffi`; the definitions in the callee need
    # no feature.
    caller = ["// Generated by benchmarks/abi-xback/families.py; do not edit.\n",
              "#![feature(simd_ffi)]\n#![no_main]\n", PRELUDE, "extern crate xcallee;\nuse xcallee::*;\n",
              "use std::hint::black_box as bb;\n\n", CALLER_RUNTIME, "\n"]
    externs = []
    for case in members:
        if case.abi == "C" and not case.libc and not case.via_pointer:
            externs.append(f"    fn {callee_signature(case, case.name)};\n")
    if any(case.libc for case in members):
        externs.append("    fn snprintf(buf: *mut u8, n: usize, fmt: *const u8, ...) -> i32;\n")
    if externs:
        caller.append("extern \"C\" {\n" + "".join(externs) + "}\n\n")
    for case in members:
        if case.callback is not None:
            caller.append(emit_callback_impl(case) + "\n")
        caller.append(emit_caller_case(case) + "\n")
    # Case selection by argument COUNT: `argc == 2 + k` runs case k. This keeps
    # the dispatcher free of argument parsing, so every cell runs each case in
    # its own process and a crash is attributed to exactly one case.
    arms = "".join(f"        {index + 2} => case_{case.name}(),\n" for index, case in enumerate(members))
    caller.append(
        "#[no_mangle]\n"
        "pub extern \"C\" fn main(argc: i32, _argv: *const *const u8) -> i32 {\n"
        "    match argc {\n" + arms + "        _ => return 3,\n    }\n    0\n}\n"
    )
    expected = {
        "group": group,
        "cases": [
            {"name": case.name, "family": case.family, "abi": case.abi, "argc": index + 2,
             "sides": case.sides, "rule": case.rule, "expected": expected_line(case)}
            for index, case in enumerate(members)
        ],
    }
    return "".join(callee), "".join(caller), expected


def groups(selected: list[Case]) -> dict[str, list[Case]]:
    result: dict[str, list[Case]] = {}
    for case in selected:
        result.setdefault(case.group, []).append(case)
    return result


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--emit", type=Path)
    parser.add_argument("--group")
    parser.add_argument("--case")
    args = parser.parse_args(argv)
    every = cases()
    if args.list:
        listing = [{"group": name, "cases": [case.name for case in members]}
                   for name, members in groups(every).items()]
        print(json.dumps(listing, indent=1))
        return 0
    if args.emit is None:
        parser.error("--list or --emit DIR is required")
    if args.case is not None:
        chosen = [case for case in every if case.name == args.case]
        if len(chosen) != 1:
            print(f"unknown case {args.case!r}", file=sys.stderr)
            return 2
        selection = {chosen[0].name: chosen}
    else:
        selection = groups(every)
        if args.group is not None:
            if args.group not in selection:
                print(f"unknown group {args.group!r}", file=sys.stderr)
                return 2
            selection = {args.group: selection[args.group]}
    for name, members in selection.items():
        directory = args.emit / name
        directory.mkdir(parents=True, exist_ok=False)
        callee, caller, expected = group_sources(name, members)
        (directory / "callee.rs").write_text(callee)
        (directory / "caller.rs").write_text(caller)
        (directory / "expected.json").write_text(json.dumps(expected, indent=1) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
