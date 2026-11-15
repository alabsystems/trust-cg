#![no_std]
#![allow(dead_code)]
type Observe = extern "C" fn(u64, usize);
struct Leaf {
    small: u8,
    id: u64,
    observe: Observe,
}
impl Drop for Leaf {
    #[inline(never)]
    fn drop(&mut self) {
        (self.observe)(self.id ^ u64::from(self.small), self as *mut Self as usize);
    }
}
#[inline(always)]
fn leaf(id: u64, observe: Observe) -> Leaf {
    Leaf {
        small: 0x5a,
        id,
        observe,
    }
}
struct Pair {
    a: Leaf,
    tag: u8,
    b: Leaf,
}
struct Parent {
    small: u8,
    pair: Pair,
    observe: Observe,
}
impl Drop for Parent {
    #[inline(never)]
    fn drop(&mut self) {
        (self.observe)(900, 0);
        self.pair.a.id ^= 0x1234;
        self.pair.b.id ^= 0x4321;
    }
}
enum Choice {
    Empty,
    One(Leaf),
    Two { tag: u8, a: Leaf, b: Leaf },
}
struct Zero;
unsafe extern "C" {
    fn structural_zero();
}
impl Drop for Zero {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { structural_zero() };
    }
}
struct WithZero {
    first: Zero,
    leaf: Leaf,
    last: Zero,
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_pair(seed: u64, cb: Observe) {
    let _pair = Pair {
        a: leaf(seed, cb),
        tag: 7,
        b: leaf(seed ^ 123, cb),
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_parent(seed: u64, cb: Observe) {
    let _parent = Parent {
        small: 3,
        pair: Pair {
            a: leaf(seed, cb),
            tag: 7,
            b: leaf(seed ^ 123, cb),
        },
        observe: cb,
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_partial(seed: u64, cb: Observe, flag: bool) {
    let pair = Pair {
        a: leaf(seed, cb),
        tag: 7,
        b: leaf(seed ^ 123, cb),
    };
    if flag {
        drop(pair.b);
    } else {
        drop(pair.a);
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_tuple(seed: u64, cb: Observe) {
    let _tuple = (leaf(seed, cb), 7_u8, (leaf(seed ^ 123, cb), ()), ());
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_choice(seed: u64, cb: Observe, flag: u8) {
    let _choice = if flag == 0 {
        Choice::Empty
    } else if flag == 1 {
        Choice::One(leaf(seed, cb))
    } else {
        Choice::Two {
            tag: 9,
            a: leaf(seed, cb),
            b: leaf(seed ^ 123, cb),
        }
    };
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_option(seed: u64, cb: Observe, flag: bool) {
    let _choice = if flag { Some(leaf(seed, cb)) } else { None };
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_array(seed: u64, cb: Observe) {
    let _array = [leaf(seed, cb), leaf(seed ^ 123, cb), leaf(seed ^ 234, cb)];
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_replace(seed: u64, cb: Observe) {
    let mut pair = Pair {
        a: leaf(seed, cb),
        tag: 7,
        b: leaf(seed ^ 123, cb),
    };
    pair.a = leaf(seed ^ 345, cb);
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_pointer(seed: u64, cb: Observe) {
    let mut pair = core::mem::ManuallyDrop::new(Pair {
        a: leaf(seed, cb),
        tag: 7,
        b: leaf(seed ^ 123, cb),
    });
    let ptr = &mut pair as *mut core::mem::ManuallyDrop<Pair> as *mut Pair;
    unsafe {
        cb(1000, &raw mut (*ptr).a as usize);
        cb(1001, &raw mut (*ptr).b as usize);
        core::ptr::drop_in_place(ptr);
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_zero_field(seed: u64, cb: Observe) {
    let _with_zero = WithZero {
        first: Zero,
        leaf: leaf(seed, cb),
        last: Zero,
    };
}
unsafe extern "C" {
    fn structural_allocate(value: u64) -> *mut u64;
    fn structural_release(pointer: *mut u64);
}
struct Owner {
    tag: u8,
    pointer: *mut u64,
    observe: Observe,
}
impl Drop for Owner {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            (self.observe)(*self.pointer ^ u64::from(self.tag), self.pointer as usize);
            structural_release(self.pointer);
        }
    }
}
struct OwnedPair {
    a: Owner,
    b: Owner,
}
#[unsafe(no_mangle)]
pub extern "C" fn structural_owned(seed: u64, cb: Observe, reverse: bool) {
    unsafe {
        let pair = OwnedPair {
            a: Owner {
                tag: 0x5a,
                pointer: structural_allocate(seed),
                observe: cb,
            },
            b: Owner {
                tag: 0x5a,
                pointer: structural_allocate(seed ^ 123),
                observe: cb,
            },
        };
        if reverse {
            drop(pair.b);
            drop(pair.a);
        } else {
            drop(pair);
        }
    }
}
