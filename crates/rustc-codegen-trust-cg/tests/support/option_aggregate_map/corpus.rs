#![no_std]
struct Marker;
struct Mapping<'a> {
    iter: core::slice::Iter<'a, u8>,
    marker: Marker,
}
impl<'a> Mapping<'a> {
    #[inline(never)]
    fn into_inner(self) -> core::slice::Iter<'a, u8> {
        self.iter
    }
}
#[inline(never)]
fn unwrap_mapping<'a>(value: Option<Mapping<'a>>) -> Option<core::slice::Iter<'a, u8>> {
    value.map(Mapping::into_inner)
}
#[unsafe(no_mangle)]
pub fn mapped_cursor(bytes: &[u8], present: bool) -> (usize, usize) {
    let value = if present {
        Some(Mapping {
            iter: bytes.iter(),
            marker: Marker,
        })
    } else {
        None
    };
    match unwrap_mapping(value) {
        Some(it) => {
            let rest = it.as_slice();
            (rest.as_ptr() as usize, rest.len())
        }
        None => (0, usize::MAX),
    }
}

#[unsafe(no_mangle)]
pub fn mapped_advanced_cursor(
    bytes: &[u8],
    present: bool,
    front: bool,
    back: bool,
) -> (usize, usize) {
    let mut iter = bytes.iter();
    if front {
        iter.next();
    }
    if back {
        iter.next_back();
    }
    let value = if present {
        Some(Mapping {
            iter,
            marker: Marker,
        })
    } else {
        None
    };
    match unwrap_mapping(value) {
        Some(it) => {
            let rest = it.as_slice();
            (rest.as_ptr() as usize, rest.len())
        }
        None => (0, usize::MAX),
    }
}
