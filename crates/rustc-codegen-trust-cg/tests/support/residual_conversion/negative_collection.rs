#![no_std]
extern crate alloc;
pub struct Owner {
    pub values: alloc::vec::Vec<u64>,
}
impl From<u64> for Owner {
    #[inline(never)]
    fn from(v: u64) -> Self {
        Owner {
            values: alloc::vec![v],
        }
    }
}
#[inline(never)]
fn inner(v: u64) -> Result<(), u64> {
    Err(v)
}
#[unsafe(no_mangle)]
pub fn rejected(v: u64) -> Result<(), Owner> {
    inner(v)?;
    Ok(())
}
