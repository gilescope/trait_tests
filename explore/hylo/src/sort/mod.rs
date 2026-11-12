//! Knuth 5.2: four sorts as four (shape, plan, algebra) triples.
use crate::shape::{hylo_leaf_tree, hylo_list, hylo_node_tree, LeafTree, LeafTreeAlgebra, LeafTreePlan, ListAlgebra, ListPlan, NodeTreeAlgebra, NodeTreePlan};
use alloc::vec::Vec;

// ---- 5.2.1 insertion: fold over the list, inserting each head into the sorted tail.
pub struct Uncons;
impl<T> ListPlan<T> for Uncons {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> Option<(T, Vec<T>)> {
        if v.is_empty() { None } else { let h = v.remove(0); Some((h, v)) }
    }
}
pub struct Insert;
impl<T: Ord> ListAlgebra<T> for Insert {
    type Out = Vec<T>;
    fn fold(&mut self, l: Option<(T, Vec<T>)>) -> Vec<T> {
        match l { None => Vec::new(), Some((h, mut t)) => { let i = t.partition_point(|x| *x < h); t.insert(i, h); t } }
    }
}

// ---- 5.2.3 selection: unfold by extracting the minimum, fold by consing.
pub struct SelectMin;
impl<T: Ord> ListPlan<T> for SelectMin {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> Option<(T, Vec<T>)> {
        let i = (0..v.len()).min_by(|&a, &b| v[a].cmp(&v[b]))?;
        let m = v.swap_remove(i);
        Some((m, v))
    }
}
pub struct Cons;
impl<T> ListAlgebra<T> for Cons {
    type Out = Vec<T>;
    fn fold(&mut self, l: Option<(T, Vec<T>)>) -> Vec<T> {
        match l { None => Vec::new(), Some((h, mut t)) => { t.insert(0, h); t } }
    }
}

// ---- 5.2.2 exchanging: hard split (pivot), easy join (concat).
pub struct Pivot;
impl<T: Ord> NodeTreePlan<T> for Pivot {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> Option<(T, Vec<T>, Vec<T>)> {
        let p = v.pop()?;
        let (mut l, mut r) = (Vec::new(), Vec::new());
        while let Some(x) = v.pop() { if x < p { l.push(x) } else { r.push(x) } }
        Some((p, l, r))
    }
}
pub struct Concat;
impl<T> NodeTreeAlgebra<T> for Concat {
    type Out = Vec<T>;
    fn fold(&mut self, l: Option<(T, Vec<T>, Vec<T>)>) -> Vec<T> {
        match l { None => Vec::new(), Some((p, mut a, b)) => { a.push(p); a.extend(b); a } }
    }
}

// ---- 5.2.4 merging: easy split (halve), hard join (merge).
pub struct Halve;
impl<T> LeafTreePlan<T> for Halve {
    type Seed = Vec<T>;
    fn unfold(&mut self, mut v: Vec<T>) -> LeafTree<T, Vec<T>> {
        if v.len() <= 1 { LeafTree::Leaf(v.pop()) } else { let r = v.split_off(v.len() / 2); LeafTree::Node(v, r) }
    }
}
pub struct Merge;
impl<T: Ord> LeafTreeAlgebra<T> for Merge {
    type Out = Vec<T>;
    fn fold(&mut self, l: LeafTree<T, Vec<T>>) -> Vec<T> {
        match l {
            LeafTree::Leaf(t) => t.into_iter().collect(),
            LeafTree::Node(mut a, mut b) => {
                // consume from the back so no element is ever moved out by index
                a.reverse();
                b.reverse();
                let mut out = Vec::new();
                // no `return` inside the loop: Aeneas does not translate those
                while !a.is_empty() && !b.is_empty() {
                    let take_a = a[a.len() - 1] <= b[b.len() - 1];
                    if take_a { out.push(a.pop().unwrap()) } else { out.push(b.pop().unwrap()) }
                }
                while let Some(x) = a.pop() { out.push(x) }
                while let Some(y) = b.pop() { out.push(y) }
                out
            }
        }
    }
}

// The named algorithms are the pairs.
pub fn insertion_sort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo_list(&mut Uncons, &mut Insert, v) }
pub fn selection_sort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo_list(&mut SelectMin, &mut Cons, v) }
pub fn quicksort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo_node_tree(&mut Pivot, &mut Concat, v) }
pub fn mergesort<T: Ord>(v: Vec<T>) -> Vec<T> { hylo_leaf_tree(&mut Halve, &mut Merge, v) }
