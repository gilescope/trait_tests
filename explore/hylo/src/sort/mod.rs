//! Knuth 5.2: four sorts as four (shape, plan, algebra) triples.
use crate::shape::{LeafTree, LeafTreeF, ListF, NodeTreeF};
use crate::{hylo, Algebra, Plan};
use alloc::vec::Vec;

// ---- 5.2.1 insertion: fold over the list, inserting each head into the sorted tail.
pub struct Uncons;
impl<T> Plan<ListF<T>> for Uncons {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> Option<(T, Vec<T>)> {
        if v.is_empty() { None } else { let h = v.remove(0); Some((h, v)) }
    }
}
pub struct Insert;
impl<T: Ord> Algebra<ListF<T>> for Insert {
    type Out = Vec<T>;
    fn fold(&mut self, l: Option<(T, Vec<T>)>) -> Vec<T> {
        match l { None => Vec::new(), Some((h, mut t)) => { let i = t.partition_point(|x| *x < h); t.insert(i, h); t } }
    }
}

// ---- 5.2.3 selection: unfold by extracting the minimum, fold by consing.
pub struct SelectMin;
impl<T: Ord> Plan<ListF<T>> for SelectMin {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> Option<(T, Vec<T>)> {
        let i = (0..v.len()).min_by(|&a, &b| v[a].cmp(&v[b]))?;
        let m = v.swap_remove(i);
        Some((m, v))
    }
}
pub struct Cons;
impl<T> Algebra<ListF<T>> for Cons {
    type Out = Vec<T>;
    fn fold(&mut self, l: Option<(T, Vec<T>)>) -> Vec<T> {
        match l { None => Vec::new(), Some((h, mut t)) => { t.insert(0, h); t } }
    }
}

// ---- 5.2.2 exchanging: hard split (pivot), easy join (concat).
pub struct Pivot;
impl<T: Ord> Plan<NodeTreeF<T>> for Pivot {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> Option<(T, Vec<T>, Vec<T>)> {
        let p = v.pop()?;
        let (l, r): (Vec<T>, Vec<T>) = v.into_iter().partition(|x| *x < p);
        Some((p, l, r))
    }
}
pub struct Concat;
impl<T> Algebra<NodeTreeF<T>> for Concat {
    type Out = Vec<T>;
    fn fold(&mut self, l: Option<(T, Vec<T>, Vec<T>)>) -> Vec<T> {
        match l { None => Vec::new(), Some((p, mut a, b)) => { a.push(p); a.extend(b); a } }
    }
}

// ---- 5.2.4 merging: easy split (halve), hard join (merge).
pub struct Halve;
impl<T> Plan<LeafTreeF<T>> for Halve {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> LeafTree<T, Vec<T>> {
        if v.len() <= 1 { LeafTree::Leaf(v.pop()) } else { let r = v.split_off(v.len() / 2); LeafTree::Node(v, r) }
    }
}
pub struct Merge;
impl<T: Ord> Algebra<LeafTreeF<T>> for Merge {
    type Out = Vec<T>;
    fn fold(&mut self, l: LeafTree<T, Vec<T>>) -> Vec<T> {
        match l {
            LeafTree::Leaf(t) => t.into_iter().collect(),
            LeafTree::Node(a, b) => {
                let (mut a, mut b) = (a.into_iter().peekable(), b.into_iter().peekable());
                let mut out = Vec::new();
                loop {
                    match (a.peek(), b.peek()) {
                        (Some(x), Some(y)) => if x <= y { out.push(a.next().unwrap()) } else { out.push(b.next().unwrap()) },
                        (Some(_), None) => out.extend(a.by_ref()),
                        (None, Some(_)) => out.extend(b.by_ref()),
                        (None, None) => return out,
                    }
                }
            }
        }
    }
}

// The named algorithms are the pairs.
pub fn insertion_sort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo::<ListF<T>, _, _>(&mut Uncons, &mut Insert, v) }
pub fn selection_sort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo::<ListF<T>, _, _>(&mut SelectMin, &mut Cons, v) }
pub fn quicksort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo::<NodeTreeF<T>, _, _>(&mut Pivot, &mut Concat, v) }
pub fn mergesort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo::<LeafTreeF<T>, _, _>(&mut Halve, &mut Merge, v) }
