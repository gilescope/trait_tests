#![allow(dead_code)]
#![feature(proc_macro)]

extern crate trait_tests;

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<T> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello<String> + Sized + Default
    {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    #[trait_tests]
    trait HelloTests2 : Hello<usize> + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    #[derive(Eq,PartialEq)]
    enum Dialect {
        American
    }

    #[derive(TraitTests)]
    #[trait_test(HelloTests, String)]
    #[trait_test(HelloTests2, usize)]
    struct EnglisHelloImpl<T> {
        dialect: T
    }

    impl <T> Hello<T> for EnglisHelloImpl<T> {
        fn get_greeting(&self) -> &str {
                "Howdy"
        }
    }

    //
    // This test is showing that while we can implement two interfaces and autogenerate two test methods,
    // we need to ensure the call to run the tests needs to call through the trait.
    //
    // I.e. HelloTests2::test_all() rather than Self::test_all() as the latter would be ambiguous.
    //

    impl Default for EnglisHelloImpl<String> { fn default () -> Self { EnglisHelloImpl { dialect: String::new() } } }
    impl Default for EnglisHelloImpl<usize> { fn default () -> Self { EnglisHelloImpl { dialect: 0usize } } }
}