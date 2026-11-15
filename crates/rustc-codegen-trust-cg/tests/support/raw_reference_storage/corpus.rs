#![no_std]
#[inline(never)]
unsafe fn read_byte(p: *const u8) -> u8 {
    unsafe { *p }
}
#[unsafe(no_mangle)]
pub extern "C" fn array_field_ref(a: u8, b: u8, c: u8, d: u8) -> u64 {
    let values = [a, b, c, d];
    let (first, last) = (&values[0], &values[3]);
    unsafe { read_byte(first as *const u8) as u64 | ((read_byte(last as *const u8) as u64) << 8) }
}
struct Block {
    bytes: [u8; 4],
}
struct Outer {
    before: u64,
    block: Block,
}
#[inline(never)]
unsafe fn read_indirect(p: *const &Block) -> u64 {
    let block = unsafe { *p };
    block.bytes[0] as u64 | ((block.bytes[3] as u64) << 8)
}
#[unsafe(no_mangle)]
pub extern "C" fn aggregate_field_ref(a: u8, b: u8, c: u8, d: u8) -> u64 {
    let outer = Outer {
        before: 17,
        block: Block {
            bytes: [a, b, c, d],
        },
    };
    let r = &outer.block;
    let rr = &r;
    (unsafe { read_indirect(rr as *const &Block) }) ^ outer.before
}

#[unsafe(no_mangle)]
pub extern "C" fn dynamic_array_ref(a: u8, b: u8, c: u8, d: u8, index: usize) -> u64 {
    let values = [a, b, c, d];
    let r = &values[index & 3];
    unsafe { read_byte(r as *const u8) as u64 }
}
#[inline(never)]
fn entry_read(outer: &Outer) -> u64 {
    let r = &outer.block;
    let rr = &r;
    (unsafe { read_indirect(rr as *const &Block) }) ^ outer.before
}
#[unsafe(no_mangle)]
pub extern "C" fn aggregate_entry_ref(a: u8, b: u8, c: u8, d: u8) -> u64 {
    let outer = Outer {
        before: 23,
        block: Block {
            bytes: [a, b, c, d],
        },
    };
    entry_read(&outer)
}
struct Record<'a> {
    value: &'a u16,
    tag: u64,
}
#[inline(never)]
fn make_record(data: &u16) -> Record<'_> {
    Record {
        value: data,
        tag: 29,
    }
}
#[inline(never)]
unsafe fn read_word_indirect(p: *const &u16) -> u64 {
    unsafe { **p as u64 }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn loaded_reference(data: *const u16) -> u64 {
    let record = make_record(unsafe { &*data });
    let r = record.value;
    ((unsafe { read_word_indirect(&r as *const &u16) }) ^ record.tag)
        | (((r as *const u16 == data) as u64) << 32)
}
#[inline(never)]
fn select_ref<'a>(first: &'a u16, second: &'a u16, choose: bool) -> &'a u16 {
    if choose { second } else { first }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn returned_reference(data: *const u16, choose: bool) -> u64 {
    let r = select_ref(unsafe { &*data }, unsafe { &*data.add(1) }, choose);
    (unsafe { read_word_indirect(&r as *const &u16) })
        | (((r as *const u16 == unsafe { data.add(choose as usize) }) as u64) << 32)
}
#[inline(never)]
unsafe fn read_range(p: *const core::ops::Range<usize>) -> usize {
    unsafe { (*p).start ^ (*p).end.rotate_left(11) }
}
#[unsafe(no_mangle)]
pub extern "C" fn whole_range_ref(first: usize, last: usize) -> usize {
    let range = first..last;
    let r = &range;
    unsafe { read_range(r as *const core::ops::Range<usize>) }
}

#[inline(never)]
unsafe fn replace_ref<'a>(slot: *mut &'a u16, replacement: &'a u16) {
    unsafe {
        *slot = replacement;
    }
}
#[inline(never)]
fn mutate_ref<'a>(mut current: &'a u16, replacement: &'a u16) -> u64 {
    let before = *current as u64;
    unsafe {
        replace_ref(&raw mut current, replacement);
    }
    before
        | ((*current as u64) << 16)
        | (((current as *const u16 == replacement as *const u16) as u64) << 32)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn mutated_reference(data: *const u16) -> u64 {
    mutate_ref(unsafe { &*data }, unsafe { &*data.add(1) })
}
