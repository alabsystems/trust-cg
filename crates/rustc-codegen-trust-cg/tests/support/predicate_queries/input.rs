#![no_std]
pub trait CaseRoot {}
pub trait CaseMid: CaseRoot {}
pub trait CaseLeaf: CaseMid {
    type Assoc: CaseRoot;
}
pub trait CaseAssocBase {
    type Assoc;
}
pub trait CaseAssoc: CaseAssocBase<Assoc: CaseRoot> {}
pub struct CaseInferred<'a, T>(pub &'a T);
pub trait CaseDiamond: CaseMid + CaseRoot {}
pub trait CaseBorrow<T> {}
pub trait CaseHigher: for<'a> CaseBorrow<&'a u8> {}
pub trait CaseGeneric<T: CaseRoot> {
    fn case_trait_method<U: CaseMid>(_: U)
    where
        T: CaseMid;
}
pub struct CaseContainer<T>(pub T);
impl<T: CaseRoot> CaseContainer<T> {
    pub fn case_method<U: CaseMid>(&self, _: U)
    where
        T: CaseMid,
    {
    }
}
pub fn case_plain() {}
pub fn case_function<T: CaseLeaf>(_: T)
where
    T::Assoc: CaseMid,
{
}
pub fn case_higher<F: for<'a> Fn(&'a u8) -> &'a u8>(_: F) {}
