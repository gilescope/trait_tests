#![no_std]
//! Exploration: algorithms as traits so their contracts can be trait-tested.

// First, with `#[macro_use]`: the per-law test macros are textually scoped
// and must precede the modules that `#[test_impl]` their implementors.
#[cfg(feature = "trait-tests")]
#[macro_use]
pub mod laws;

pub mod cmp;
pub mod search;
pub mod semiring;
pub mod sort;
