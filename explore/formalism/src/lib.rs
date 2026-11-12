//! A formalism that parameterised algorithms fit within.
//!
//! An algorithm is three things, each independently checkable:
//!
//! 1. **Construction** (`scheme::Node`): the input is built by a grammar of operations
//!    (a nice tree decomposition, a k-expression, a list, ...).
//! 2. **Trace** (`scheme::Traced`): a finite summary of a partial candidate, such that the
//!    trace after a construction step depends only on the traces before it
//!    (Remark 3 of the paper). Distinct traces have disjoint candidate sets.
//! 3. **Algebra** (`semiring::Semiring` + `expr::Measure`): what question is asked.
//!    Boolean = decision, Nat = counting, Tropical = optimisation,
//!    `Delta<Tropical, Nat>` = counting optima.
//!
//! The DP in `scheme::run` is written once. It produces a *join/union expression*
//! (`expr::Expr`) of the solution set, independent of any algebra. `expr::eval` then
//! evaluates it in any commutative semiring in linear time (Lemma 1).
//!
//! What is correct by construction, what is proved once, what is tested:
//! see `FORMALISM.md`.
//!
//! The crate is `no_std` + `alloc` and avoids closures, iterators adaptors, hash maps and
//! `&mut` through generics in the core modules, so that Charon/Aeneas can translate it.

#![no_std]
extern crate alloc;

#[cfg(feature = "trait-tests")]
#[macro_use]
pub mod laws;

pub mod expr;
pub mod instances;
pub mod scheme;
pub mod semiring;
