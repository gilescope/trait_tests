//! Knuth 4.5.2 and 4.6.3: Euclid and repeated squaring as plans over the iteration shape.
use crate::algebra::{Euclidean, Monoid};
use crate::shape::{hylo_iter, Iter, IterPlan, Last};

/// gcd by remainders. Recursive because the remainder strictly decreases in norm.
pub struct Euclid;
impl<T: Euclidean> IterPlan<T> for Euclid {
    type Seed = (T, T);
    fn unfold(&mut self, (a, b): (T, T)) -> Iter<T, (T, T)> {
        if b == T::zero() { Iter::Done(a) } else { Iter::Step((b, a.rem(b))) }
    }
}
pub fn gcd<T: Euclidean>(a: T, b: T) -> T { hylo_iter(&mut Euclid, &mut Last, (a, b)) }

/// xⁿ by repeated squaring over any monoid. Recursive because the exponent halves.
pub struct Square;
impl<M: Monoid> IterPlan<M> for Square {
    type Seed = (M, u64, M); // (base, exponent, accumulator)
    fn unfold(&mut self, (x, n, acc): (M, u64, M)) -> Iter<M, (M, u64, M)> {
        if n == 0 { return Iter::Done(acc); }
        let acc = if n & 1 == 1 { acc.op(x) } else { acc };
        Iter::Step((x.op(x), n >> 1, acc))
    }
}
pub fn power<M: Monoid>(x: M, n: u64) -> M { hylo_iter(&mut Square, &mut Last, (x, n, M::unit())) }
