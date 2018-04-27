# trait_tests
A compiler plugin to enable tests to be defined upon rust's traits.

See https://github.com/gilescope/iunit for example test suites.

## Why

More tests are great, but less code is less bugs so we want more tests but less code. This crate attempts to break the N*M problem of repeatedly writing tests for all the individual implementations. 

The goal is one ships a std library with std tests, 
and gradually an ecosystem of people publishing std tests with their traits/interfaces.

Warning: This is still at proof of concept stage. V0.2 onwards is implemented as a procmacro rather than a compiler plugin so it's a step closer to working on stable as well as nightly.

## How: Defining a test on a Trait

To create a trait test, create a subtrait of the trait under test with static functions on it. The generic parameters should be concreted out into a type of your choosing to help you with the testing.

```rust
#[trait_tests]
pub trait SetIteratorTests: Set<char> + Sized + IntoIterator<Item=char>
{
    fn test_move_iter()
    {
        let hs = {
            let mut hs = Self::new();
            hs.insert('a');
            hs.insert('b');
            hs
        };

        let v = hs.into_iter().collect::<Vec<char>>();
        assert!(v == ['a', 'b'] || v == ['b', 'a']);
    }
}
```

The #[test_traits] attribute on the trait currently 
generates a test_all function in the trait:
```rust
pub trait SetIteratorTests: Set<char> + Sized + IntoIterator<Item=char>
{
    fn test_all() {
        Self::test_move_iter();
        ..
    }
    
    ..
}
```

(It's an open issue as to how to make these report as 
individual tests rather than running as one, but its clear 
from the stacktrace which test the failure came from.)

## How: Testing your implementation

The compiler will guide you of additional traits that the tests would need implemented in order to function. As certain traits go together this can be a nice way of ensuring your implementation is well-rounded.

## Installing

V0.3 onwards is two proc macros: `#[trait_tests]` to define the tests and `#[impl_test]` to call the tests.

Here is how to define some tests on a trait:

```rust
#![feature(proc_macro)]
extern crate trait_tests;
use trait_tests::*;

trait Hello {
    fn get_greeting(&self) -> &str;
}

#[trait_tests]
trait HelloTests : Hello + Sized + Default {
    fn test_1() {
        assert!(Self::default().get_greeting().len() < 200);
    }
}
```

To run the tests associated with the trait you need to:
   1. `use` the tests so they are imported.
   2. Add `#[test_impl]` to your impl.

```rust
#![feature(proc_macro)]
extern crate trait_tests;
use trait_tests::*;

struct SpanishHelloImpl {}

#[test_impl]
impl Hello for SpanishHelloImpl {
    fn get_greeting(&self) -> &str { "Hola" }
}
```

## Trait Test Authoring Guide

As Rust includes static functions on their interfaces creating interface tests is easier than you might have thought. As more people write more trait tests I'm sure we will discover patterns that work well.

For now, tips are:

   * Try to write trait tests using as few auxillary interfaces as possible. E.g. where possible use `&` and `&mut` references rather than restricting the tests to only work with implementations that also implement `Sized`.

### Factory Methods

To write useful tests you are generally going to need to rely 
on some static methods to instanciate your trait. While `Default`
can help you write some tests, ideally being able to inject state
can be helpful. The `std::iter::FromIterator` trait can be extreamly helpful for setting up collection style traits.

## Open Questions and limitations

  1. How do we get the test framework to enumerate 
  all the individual tests.
  2. Trait tests are currently public rather than under cfg(test)
  3. Relies on procmacro which is not yet standardised (though soon hopefully) so currently only available on nightly.

## Examples of trait tests
    
   * Fork of eclectic including trait tests on the collections traits: https://github.com/gilescope/eclectic
   * Fork of num-traits with trait tests: https://github.com/gilescope/num-traits
   * See also https://github.com/gilescope/iunit for tests that run on std traits.
   
# Discuss!

All feedback and contributions extremely welcome!

Relevant discussions:

   * First Suggested: https://github.com/rust-lang/rfcs/issues/616
   * Trait tests: https://users.rust-lang.org/t/tests-for-traits/
   * Collection Traits in Rust: https://internals.rust-lang.org/t/collection-traits-take-2/