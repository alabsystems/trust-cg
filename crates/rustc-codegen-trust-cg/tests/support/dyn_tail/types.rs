#![no_std]

pub trait Payload: Left + Right {
    fn read(&self) -> u64;
    fn bump(&mut self, by: u64) -> u64;
}
#[repr(C)]
pub struct Header<T: ?Sized> {
    pub marker: u8,
    pub epoch: u64,
    pub value: T,
}
#[repr(C, align(32))]
pub struct Inner<T: ?Sized> {
    pub prefix: [u8; 3],
    pub node: Header<T>,
}
#[repr(C, align(16))]
pub struct Outer<T: ?Sized> {
    pub lead: u16,
    pub nested: Inner<T>,
}
#[repr(transparent)]
pub struct Transparent<T: ?Sized>(pub Outer<T>);
pub struct RustHeader<T: ?Sized> {
    pub marker: u8,
    pub count: u128,
    pub value: T,
}
#[repr(transparent)]
pub struct Small(pub u8);
impl Payload for Small {
    #[inline(never)]
    fn read(&self) -> u64 {
        self.0 as u64
    }
    #[inline(never)]
    fn bump(&mut self, by: u64) -> u64 {
        self.0 = self.0.wrapping_add(by as u8);
        self.read()
    }
}
#[repr(transparent)]
pub struct Word(pub u64);
impl Payload for Word {
    #[inline(never)]
    fn read(&self) -> u64 {
        self.0
    }
    #[inline(never)]
    fn bump(&mut self, by: u64) -> u64 {
        self.0 = self.0.wrapping_add(by);
        self.0
    }
}
#[repr(C, align(64))]
pub struct Wide(pub [u64; 4]);
impl Payload for Wide {
    #[inline(never)]
    fn read(&self) -> u64 {
        self.0[0] ^ self.0[1] ^ self.0[2] ^ self.0[3]
    }
    #[inline(never)]
    fn bump(&mut self, by: u64) -> u64 {
        self.0[3] = self.0[3].wrapping_add(by);
        self.read()
    }
}
#[repr(align(256))]
pub struct Empty;
impl Payload for Empty {
    #[inline(never)]
    fn read(&self) -> u64 {
        0x2ac9
    }
    #[inline(never)]
    fn bump(&mut self, _by: u64) -> u64 {
        self.read()
    }
}

pub trait Left {
    fn left(&self) -> u64;
}
pub trait Right {
    fn right(&self) -> u64;
}
macro_rules! supers {
    ($($ty:ty),*) => {$(
        impl Left for $ty {
            #[inline(never)]
            fn left(&self) -> u64 { self.read().wrapping_add(0x371) }
        }
        impl Right for $ty {
            #[inline(never)]
            fn right(&self) -> u64 { self.read().rotate_left(19) ^ 0x7173 }
        }
    )*};
}
supers!(Small, Word, Wide, Empty);
