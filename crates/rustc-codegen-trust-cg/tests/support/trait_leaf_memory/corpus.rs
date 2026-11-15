#![no_std]
trait Sink {
    fn push(&mut self, value: u64) -> u64;
}
#[repr(transparent)]
struct Base(u64);
impl Sink for Base {
    fn push(&mut self, value: u64) -> u64 {
        self.0 = self.0.wrapping_add(value);
        self.0
    }
}
struct Adapter<'a, 'b> {
    sink: &'a mut dyn Sink,
    state: &'b mut u64,
}
impl Sink for Adapter<'_, '_> {
    fn push(&mut self, value: u64) -> u64 {
        *self.state = self.state.wrapping_add(1);
        self.sink.push(value.wrapping_add(*self.state))
    }
}
struct Holder<'a> {
    sink: &'a mut dyn Sink,
    options: u64,
}
impl Holder<'_> {
    #[inline(never)]
    fn wrap<'b, 'c, F>(&'b mut self, wrap: F) -> Holder<'c>
    where
        'b: 'c,
        F: FnOnce(&'b mut (dyn Sink + 'b)) -> &'c mut (dyn Sink + 'c),
    {
        Holder {
            sink: wrap(self.sink),
            options: self.options,
        }
    }
}
#[inline(never)]
fn adapt<'slot, 'buf, 'fmt: 'buf + 'slot>(
    holder: &'fmt mut Holder<'_>,
    slot: &'slot mut Option<Adapter<'buf, 'slot>>,
    state: &'slot mut u64,
) -> Holder<'slot> {
    holder.wrap(move |sink| slot.insert(Adapter { sink, state }))
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn projected_trait_wrapper(seed: u64, value: u64, storage: *mut u64) -> u64 {
    let base = unsafe { &mut *storage.cast::<Base>() };
    base.0 = seed;
    let mut holder = Holder {
        sink: base,
        options: 17,
    };
    let mut slot = None;
    let mut state = 0;
    let mut wrapper = adapt(&mut holder, &mut slot, &mut state);
    let result = wrapper.sink.push(value);
    result.wrapping_add(wrapper.options)
}

trait Read {
    fn read(&self) -> u64;
}
impl Read for Base {
    fn read(&self) -> u64 {
        self.0
    }
}
#[repr(transparent)]
struct Mirror(u64);
impl Read for Mirror {
    fn read(&self) -> u64 {
        !self.0
    }
}
#[repr(C)]
struct SharedHolder<'a> {
    prefix: u64,
    value: &'a dyn Read,
    suffix: u64,
}
#[repr(C)]
struct RawHolder {
    prefix: u64,
    value: *const dyn Read,
}
#[inline(never)]
fn return_shared(value: &dyn Read) -> &dyn Read {
    value
}
#[inline(never)]
fn return_raw(value: *const dyn Read) -> *const dyn Read {
    value
}
#[inline(never)]
fn make_shared(value: &dyn Read) -> SharedHolder<'_> {
    SharedHolder {
        prefix: 17,
        value: return_shared(value),
        suffix: 29,
    }
}
#[inline(never)]
fn make_raw(value: *const dyn Read) -> RawHolder {
    RawHolder {
        prefix: 0x77,
        value: return_raw(value),
    }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trait_leaf_shared(storage: *const u64, mode: u64) -> u64 {
    let value: &dyn Read = if mode == 0 {
        unsafe { &*storage.cast::<Base>() }
    } else {
        unsafe { &*storage.cast::<Mirror>() }
    };
    let holder = make_shared(value);
    holder
        .prefix
        .wrapping_add(holder.value.read())
        .wrapping_add(holder.suffix)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn trait_leaf_raw(storage: *const u64, mode: u64) -> u64 {
    let value: &dyn Read = if mode == 0 {
        unsafe { &*storage.cast::<Base>() }
    } else {
        unsafe { &*storage.cast::<Mirror>() }
    };
    let holder = make_raw(value as *const dyn Read);
    holder.prefix ^ unsafe { (*holder.value).read() }
}
