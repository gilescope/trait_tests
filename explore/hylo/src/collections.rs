//! Plan-state collections written over `Vec` with index loops, so that Charon/Aeneas have a model
//! for everything (there is none for `BinaryHeap` or `VecDeque` upstream or in the fork).
use alloc::vec::Vec;

/// First-in first-out over a `Vec` with a moving head. Memory is bounded by total pushes.
pub struct Fifo<T> { items: Vec<T>, head: usize }
impl<T> Default for Fifo<T> { fn default() -> Self { Fifo { items: Vec::new(), head: 0 } } }
impl<T: Copy> Fifo<T> {
    pub fn push(&mut self, t: T) { self.items.push(t) }
    pub fn pop(&mut self) -> Option<T> {
        if self.head < self.items.len() { let t = self.items[self.head]; self.head += 1; Some(t) } else { None }
    }
}

/// Binary min-heap on `(key, value)` pairs, ordered by key only.
pub struct MinHeap<K, V> { data: Vec<(K, V)> }
impl<K, V> Default for MinHeap<K, V> { fn default() -> Self { MinHeap { data: Vec::new() } } }
impl<K: Ord + Copy, V: Copy> MinHeap<K, V> {
    pub fn push(&mut self, k: K, v: V) {
        self.data.push((k, v));
        let mut i = self.data.len() - 1;
        while i > 0 {
            let p = (i - 1) / 2;
            if self.data[p].0 <= self.data[i].0 { break; }
            self.data.swap(p, i);
            i = p;
        }
    }
    pub fn pop(&mut self) -> Option<V> {
        let n = self.data.len();
        if n == 0 { return None; }
        self.data.swap(0, n - 1);
        let (_, v) = self.data.pop()?;
        let n = n - 1;
        let mut i = 0;
        loop {
            let (l, r) = (2 * i + 1, 2 * i + 2);
            let mut m = i;
            if l < n && self.data[l].0 < self.data[m].0 { m = l; }
            if r < n && self.data[r].0 < self.data[m].0 { m = r; }
            if m == i { break; }
            self.data.swap(i, m);
            i = m;
        }
        Some(v)
    }
}

#[cfg(test)]
mod t {
    extern crate std;
    use super::*;
    #[test]
    fn heap_pops_in_key_order() {
        let mut h = MinHeap::default();
        let mut x = 7u64;
        let mut keys = std::vec::Vec::new();
        for i in 0..200u32 { x = x.wrapping_mul(6364136223846793005).wrapping_add(1); let k = x >> 40; keys.push(k); h.push(k, i); }
        let mut out = std::vec::Vec::new();
        while let Some(v) = h.pop() { out.push(keys[v as usize]); }
        let mut want = keys.clone(); want.sort();
        assert_eq!(out, want);
    }
}
