#![no_std]
#![allow(dead_code)]
type Observe = extern "C" fn(u64, usize);
trait Family {
    type Owned;
}
struct Leaf {
    tag: u8,
    id: u64,
    observe: Observe,
}
impl Drop for Leaf {
    #[inline(never)]
    fn drop(&mut self) {
        (self.observe)(self.id ^ u64::from(self.tag), self as *mut Self as usize);
    }
}
#[inline(always)]
fn leaf(id: u64, observe: Observe) -> Leaf {
    Leaf {
        tag: 0x5a,
        id,
        observe,
    }
}
struct LeafKind;
impl Family for LeafKind {
    type Owned = Leaf;
}
struct ArrayKind;
impl Family for ArrayKind {
    type Owned = [Leaf; 3];
}
struct Zero;
unsafe extern "C" {
    fn associated_zero();
}
impl Drop for Zero {
    fn drop(&mut self) {
        unsafe { associated_zero() };
    }
}
struct ZeroKind;
impl Family for ZeroKind {
    type Owned = Zero;
}
struct TupleKind;
impl Family for TupleKind {
    type Owned = (Leaf, u8, Leaf);
}
struct Nested<T: Family> {
    value: T::Owned,
    marker: Leaf,
}
struct NestedKind;
impl Family for NestedKind {
    type Owned = Nested<LeafKind>;
}
enum CowLike<'a, T: Family> {
    Borrowed(&'a u64),
    Owned(T::Owned),
}
struct Envelope<T: Family> {
    before: Leaf,
    payload: Option<T::Owned>,
    after: Leaf,
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_leaf(seed: u64, cb: Observe, owned: bool) {
    let _v: CowLike<'_, LeafKind> = if owned {
        CowLike::Owned(leaf(seed, cb))
    } else {
        CowLike::Borrowed(&seed)
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_array(seed: u64, cb: Observe, owned: bool) {
    let _v: CowLike<'_, ArrayKind> = if owned {
        CowLike::Owned([leaf(seed, cb), leaf(seed ^ 123, cb), leaf(seed ^ 234, cb)])
    } else {
        CowLike::Borrowed(&seed)
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_tuple(seed: u64, cb: Observe, owned: bool) {
    let _v: CowLike<'_, TupleKind> = if owned {
        CowLike::Owned((leaf(seed, cb), 7, leaf(seed ^ 123, cb)))
    } else {
        CowLike::Borrowed(&seed)
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_nested(seed: u64, cb: Observe, owned: bool) {
    let _v: CowLike<'_, NestedKind> = if owned {
        CowLike::Owned(Nested {
            value: leaf(seed, cb),
            marker: leaf(seed ^ 123, cb),
        })
    } else {
        CowLike::Borrowed(&seed)
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_option(seed: u64, cb: Observe, owned: bool) {
    let _v = Envelope::<LeafKind> {
        before: leaf(seed, cb),
        payload: if owned {
            Some(leaf(seed ^ 123, cb))
        } else {
            None
        },
        after: leaf(seed ^ 234, cb),
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_zero_case(seed: u64, owned: bool) {
    let _v: CowLike<'_, ZeroKind> = if owned {
        CowLike::Owned(Zero)
    } else {
        CowLike::Borrowed(&seed)
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn associated_replace(seed: u64, cb: Observe, owned: bool) {
    let mut v: CowLike<'_, LeafKind> = if owned {
        CowLike::Owned(leaf(seed, cb))
    } else {
        CowLike::Borrowed(&seed)
    };
    v = CowLike::Owned(leaf(seed ^ 123, cb));
    drop(v);
}
unsafe extern "C" {
    fn associated_allocate(value: u64) -> *mut u64;
    fn associated_release(pointer: *mut u64);
}
struct Buffer {
    capacity: usize,
    data: *mut u64,
    len: usize,
    observe: Observe,
}
impl Drop for Buffer {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            (self.observe)(
                *self.data ^ (self.capacity as u64) ^ (self.len as u64),
                self.data as usize,
            );
            associated_release(self.data);
        }
    }
}
trait ToBuffer {
    type Owned;
}
impl ToBuffer for [u64] {
    type Owned = Buffer;
}
enum SliceCow<'a, T: ?Sized + ToBuffer> {
    Borrowed(&'a T),
    Owned(T::Owned),
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn associated_buffer(
    seed: u64,
    cb: Observe,
    ptr: *const u64,
    len: usize,
    owned: bool,
) {
    let v: SliceCow<'_, [u64]> = if owned {
        SliceCow::Owned(Buffer {
            capacity: 7,
            data: unsafe { associated_allocate(seed) },
            len: 1,
            observe: cb,
        })
    } else {
        SliceCow::Borrowed(unsafe { core::slice::from_raw_parts(ptr, len) })
    };
    drop(v);
}
