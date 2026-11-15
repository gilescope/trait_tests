//! GAT-lite acceptance test for Aeneas: a trait with a generic associated type with one type
//! parameter, no bounds, no lifetimes; an impl giving it a type-level value; a generic function
//! whose signature mentions `S::Layer<X>`; and a concrete caller. No closures and no recursion
//! through trait methods, so this isolates GAT translation from the other known limitations.
#![no_std]

pub trait Shape {
    type Layer<X>;
    fn wrap<X>(x: X) -> Self::Layer<X>;
    fn unwrap<X>(l: Self::Layer<X>) -> Option<X>;
}

/// Nil | Cons(head, rest) with a `u32` head.
pub struct ListF;
impl Shape for ListF {
    type Layer<X> = Option<(u32, X)>;
    fn wrap<X>(x: X) -> Option<(u32, X)> { Some((0, x)) }
    fn unwrap<X>(l: Option<(u32, X)>) -> Option<X> {
        match l { None => None, Some((_, x)) => Some(x) }
    }
}

/// Generic over the shape: the signature and body mention `S::Layer<X>`.
pub fn roundtrip<S: Shape, X>(x: X) -> Option<X> {
    let l: S::Layer<X> = S::wrap(x);
    S::unwrap(l)
}

/// Concrete instantiation.
pub fn roundtrip_list(x: u32) -> Option<u32> { roundtrip::<ListF, u32>(x) }

#[cfg(test)]
mod t {
    #[test]
    fn roundtrips() { assert_eq!(super::roundtrip_list(7), Some(7)); }
}
