extern crate cleanup_state_provider as provider;

/// Branches construct different owned pointers and call different genuine
/// may-unwind sites, then converge before a third call and the final drop.
#[inline(never)]
pub fn box_join(branch: bool, panic_site: u8, base: u64) -> u64 {
    let owned;
    if branch {
        owned = Box::new(base + 11);
        unsafe { provider::observe_box((&*owned as *const u64) as usize) };
        provider::may_unwind(1, panic_site);
    } else {
        owned = Box::new(base + 21);
        unsafe { provider::observe_box((&*owned as *const u64) as usize) };
        provider::may_unwind(2, panic_site);
    }
    provider::may_unwind(3, panic_site);
    *owned
}

/// The replacement's call result is usable only on the normal edge. If its
/// call unwinds, cleanup must still drop the original box, without storing
/// an undefined replacement pointer over the original ownership state.
#[inline(never)]
pub fn box_replace_call_result(panic_site: u8, base: u64) -> u64 {
    let mut owned = provider::make_box(base + 11, 1, panic_site);
    unsafe { provider::observe_box((&*owned as *const u64) as usize) };
    provider::may_unwind(2, panic_site);
    owned = provider::make_box(base + 21, 3, panic_site);
    unsafe { provider::observe_box((&*owned as *const u64) as usize) };
    provider::may_unwind(4, panic_site);
    *owned
}

struct ScalarOwner(u64);
impl Drop for ScalarOwner {
    fn drop(&mut self) { provider::record_drop(self.0); }
}

/// The cleanup's destructor observes scalar state through the source-owned
/// field, rather than an SSA value supplied by the unwinder.
#[inline(never)]
pub fn scalar_join(branch: bool, panic_site: u8, base: u64) -> u64 {
    let owned;
    if branch {
        owned = ScalarOwner(base + 31);
        provider::may_unwind(1, panic_site);
    } else {
        owned = ScalarOwner(base + 41);
        provider::may_unwind(2, panic_site);
    }
    provider::may_unwind(3, panic_site);
    owned.0
}
