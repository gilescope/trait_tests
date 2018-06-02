#![allow(dead_code)]
#![feature(proc_macro)]

extern crate trait_tests;

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<T> {
        fn get_greeting(&self) -> &str;
    }

    //type HelloTestsType1 = String;
    #[trait_tests]
    trait HelloTests: Hello<String> + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    //    type HelloTests2Type1 = usize;
    //    #[trait_tests]
    //    trait HelloTests2 : Hello<HelloTests2Type1> + Sized + Default {
    //        fn test() {
    //            assert!(Self::default().get_greeting().len() < 200);
    //        }
    //    }

    #[derive(Eq, PartialEq)]
    enum Dialect {
        American,
    }

    //    #[derive(TraitTests)]
    //    #[trait_test(HelloTests, HelloTestsType1)]
    //    #[trait_test(HelloTests2, HelloTests2Type1)]  TODO don't have an answer for this.
    struct EnglisHelloImpl<T> {
        dialect: T,
    }

    #[test_impl]
    impl<T> Hello<T> for EnglisHelloImpl<T> {
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

    impl Default for EnglisHelloImpl<String> {
        fn default() -> Self {
            EnglisHelloImpl {
                dialect: String::new(),
            }
        }
    }

    impl Default for EnglisHelloImpl<usize> {
        fn default() -> Self {
            EnglisHelloImpl { dialect: 0usize }
        }
    }
}
