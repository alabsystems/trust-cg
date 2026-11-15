extern crate box_pointer_entry_provider as provider;

trait Read {
    fn read(&self) -> i64;
}

impl Read for i64 {
    #[inline(never)]
    fn read(&self) -> i64 {
        provider::observe(self as *const i64, *self)
    }
}

#[inline(never)]
pub fn consume_untouched(value: Box<i64>) -> i64 {
    let object: Box<dyn Read> = value;
    let result = object.read();
    drop(object);
    result
}

#[inline(never)]
pub fn consume_retargeted(mut value: Box<i64>, replacement: Box<i64>) -> i64 {
    provider::replace_box(&mut value, replacement);
    let object: Box<dyn Read> = value;
    let result = object.read();
    drop(object);
    result
}
