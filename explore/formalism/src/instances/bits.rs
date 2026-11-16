//! Bit vectors with exactly `k` ones: the worked example of the Lean model (`Bits.lean`).
//!
//! A candidate is an assignment of the leaves (variables) to `0` or `1`; its trace is the
//! number of ones, so a node needs only one row per count. The count is kept in a `u64` with
//! wrapping addition: the Lean proof reads that as the model's modular `Counter`, and the
//! exact one when the tree is small enough not to wrap.
use crate::expr::{Val, Var};
use crate::scheme::{Step, Traced};
use alloc::vec::Vec;

/// A leaf owns one variable; a node only combines its children.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    Leaf(Var),
    Node,
}

/// Solutions are the assignments with exactly `k` ones.
#[derive(Clone, Debug)]
pub struct Bits {
    pub k: u64,
}

/// The sum of the children's counts, wrapping.
fn sum(child_traces: &[u64]) -> u64 {
    let mut acc: u64 = 0;
    let mut i = 0;
    while i < child_traces.len() {
        acc = acc.wrapping_add(child_traces[i]);
        i += 1;
    }
    acc
}

impl Traced for Bits {
    type Op = Op;
    type Tau = u64;

    fn step(&self, op: &Op, child_traces: &[u64]) -> Step<u64> {
        let s = sum(child_traces);
        let mut out: Step<u64> = Vec::new();
        match op {
            Op::Leaf(v) => {
                let mut zero: Vec<(Var, Val)> = Vec::new();
                zero.push((*v, 0));
                out.push((s, zero));
                let mut one: Vec<(Var, Val)> = Vec::new();
                one.push((*v, 1));
                out.push((s.wrapping_add(1), one));
            }
            Op::Node => {
                let empty: Vec<(Var, Val)> = Vec::new();
                out.push((s, empty));
            }
        }
        out
    }

    fn accept(&self, tau: &u64) -> bool {
        *tau == self.k
    }
}
