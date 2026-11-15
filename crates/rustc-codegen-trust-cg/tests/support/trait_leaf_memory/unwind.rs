#![no_std]
unsafe extern "C" {
    fn note_drop();
}
unsafe extern "C-unwind" {
    fn maybe_panic();
}
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe {
            note_drop();
        }
    }
}
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
        let _guard = Guard;
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
    holder.wrap(move |sink| {
        unsafe {
            maybe_panic();
        }
        slot.insert(Adapter { sink, state })
    })
}
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn projected_trait_wrapper(
    seed: u64,
    value: u64,
    storage: *mut u64,
) -> u64 {
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
