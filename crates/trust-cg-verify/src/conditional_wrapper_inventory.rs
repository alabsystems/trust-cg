// Copyright 2026 Andrew Yates | Apache-2.0

//! Resource-only preflight of all serde-visible retained LIR payloads before
//! canonical identity rendering. No copied encoding or semantic interpretation.
use serde::ser::{self, Serialize};

const MAX_NODES: usize = 262_144;
const MAX_BYTES: usize = 4 * 1024 * 1024;
const MAX_DEPTH: usize = 32;

#[derive(Debug)]
pub(super) struct Limit;
impl std::fmt::Display for Limit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("conditional retained payload limit")
    }
}
impl std::error::Error for Limit {}
impl ser::Error for Limit {
    fn custom<T: std::fmt::Display>(_: T) -> Self {
        Self
    }
}

type R<T = ()> = Result<T, Limit>;
#[derive(Default)]
pub(super) struct Inventory {
    nodes: usize,
    bytes: usize,
}
impl Inventory {
    pub(super) fn charge(&mut self, nodes: usize, bytes: usize) -> R {
        let n = self
            .nodes
            .checked_add(nodes)
            .filter(|n| *n <= MAX_NODES)
            .ok_or(Limit)?;
        let b = self
            .bytes
            .checked_add(bytes)
            .filter(|n| *n <= MAX_BYTES)
            .ok_or(Limit)?;
        self.nodes = n;
        self.bytes = b;
        Ok(())
    }
    pub(super) fn inspect<T: Serialize>(&mut self, value: &T) -> R {
        value.serialize(Walk {
            inventory: self,
            depth: 0,
        })
    }
}
struct Walk<'a> {
    inventory: &'a mut Inventory,
    depth: usize,
}
impl Walk<'_> {
    fn child<T: Serialize + ?Sized>(&mut self, value: &T) -> R {
        if self.depth >= MAX_DEPTH {
            return Err(Limit);
        }
        value.serialize(Walk {
            inventory: self.inventory,
            depth: self.depth + 1,
        })
    }
    fn container(self, len: usize) -> R<Self> {
        if self.depth >= MAX_DEPTH {
            return Err(Limit);
        }
        self.inventory.charge(len.checked_add(1).ok_or(Limit)?, 0)?;
        Ok(self)
    }
}
macro_rules! scalar {
    ($($method:ident($t:ty)),*)=>{$(fn $method(self,_:$t)->R {self.inventory.charge(1,std::mem::size_of::<$t>())})*};
}
impl<'a> ser::Serializer for Walk<'a> {
    type Ok = ();
    type Error = Limit;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;
    scalar!(
        serialize_bool(bool),
        serialize_i8(i8),
        serialize_i16(i16),
        serialize_i32(i32),
        serialize_i64(i64),
        serialize_i128(i128),
        serialize_u8(u8),
        serialize_u16(u16),
        serialize_u32(u32),
        serialize_u64(u64),
        serialize_u128(u128),
        serialize_f32(f32),
        serialize_f64(f64),
        serialize_char(char)
    );
    fn serialize_str(self, v: &str) -> R {
        self.inventory.charge(1, v.len())
    }
    fn serialize_bytes(self, v: &[u8]) -> R {
        self.inventory.charge(1, v.len())
    }
    fn serialize_none(self) -> R {
        self.inventory.charge(1, 0)
    }
    fn serialize_some<T: Serialize + ?Sized>(mut self, v: &T) -> R {
        self.inventory.charge(1, 0)?;
        self.child(v)
    }
    fn serialize_unit(self) -> R {
        self.inventory.charge(1, 0)
    }
    fn serialize_unit_struct(self, _: &'static str) -> R {
        self.inventory.charge(1, 0)
    }
    fn serialize_unit_variant(self, _: &'static str, _: u32, _: &'static str) -> R {
        self.inventory.charge(1, 0)
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(mut self, _: &'static str, v: &T) -> R {
        self.inventory.charge(1, 0)?;
        self.child(v)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        mut self,
        _: &'static str,
        _: u32,
        _: &'static str,
        v: &T,
    ) -> R {
        self.inventory.charge(1, 0)?;
        self.child(v)
    }
    fn serialize_seq(self, len: Option<usize>) -> R<Self> {
        self.container(len.ok_or(Limit)?)
    }
    fn serialize_tuple(self, len: usize) -> R<Self> {
        self.container(len)
    }
    fn serialize_tuple_struct(self, _: &'static str, len: usize) -> R<Self> {
        self.container(len)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        len: usize,
    ) -> R<Self> {
        self.container(len)
    }
    fn serialize_map(self, len: Option<usize>) -> R<Self> {
        self.container(len.ok_or(Limit)?.checked_mul(2).ok_or(Limit)?)
    }
    fn serialize_struct(self, _: &'static str, len: usize) -> R<Self> {
        self.container(len)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        len: usize,
    ) -> R<Self> {
        self.container(len)
    }
    fn collect_str<T: std::fmt::Display + ?Sized>(self, _: &T) -> R {
        Err(Limit)
    }
}
impl ser::SerializeSeq for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
impl ser::SerializeTuple for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
impl ser::SerializeTupleStruct for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
impl ser::SerializeTupleVariant for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
impl ser::SerializeMap for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, v: &T) -> R {
        self.child(v)
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
impl ser::SerializeStruct for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, _: &'static str, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
impl ser::SerializeStructVariant for Walk<'_> {
    type Ok = ();
    type Error = Limit;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, _: &'static str, v: &T) -> R {
        self.child(v)
    }
    fn end(self) -> R {
        Ok(())
    }
}
