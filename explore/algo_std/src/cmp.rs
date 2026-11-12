use core::cmp::Ordering;
#[cfg(test)]
use crate::laws::*;

/// One comparator abstraction replaces the `_by` / `_by_key` triplication.
pub trait Comparator<T: ?Sized> {
    fn compare(&mut self, a: &T, b: &T) -> Ordering;

    fn lt(&mut self, a: &T, b: &T) -> bool {
        self.compare(a, b) == Ordering::Less
    }
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Natural;

#[cfg_attr(test, trait_tests::test_impl)]
impl<T: Ord + ?Sized> Comparator<T> for Natural {
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        a.cmp(b)
    }
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Reverse<C>(pub C);

impl<T: ?Sized, C: Comparator<T>> Comparator<T> for Reverse<C> {
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        self.0.compare(b, a)
    }
}

pub struct ByKey<F>(pub F);

impl<T: ?Sized, K: Ord, F: FnMut(&T) -> K> Comparator<T> for ByKey<F> {
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        (self.0)(a).cmp(&(self.0)(b))
    }
}

impl<T: ?Sized, F: FnMut(&T, &T) -> Ordering> Comparator<T> for F {
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        self(a, b)
    }
}

// `#[test_impl]` cannot pick a concrete `C`, so spell out what it would have generated.
#[cfg(test)]
impl ComparatorTests for Reverse<Natural> {}
#[cfg(test)]
#[test]
fn reverse_natural_comparator() {
    <Reverse<Natural> as ComparatorTests>::test_all()
}
