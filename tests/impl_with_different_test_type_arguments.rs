#![feature(custom_attribute)]
#![feature(plugin)]
#![plugin(trait_tests)]
#[allow(dead_code)]

#[cfg(test)]
mod example_tests {

    trait Hello<T> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello<String> + Sized
    //+ Default  (Default will not work if there are multiple test definitions.)
    {
        fn new() -> Self;

        fn test() {
            assert!(Self::new().get_greeting().len() < 200);
        }
    }

    #[trait_tests]
    trait HelloTests2 : Hello<usize> + Sized {
        fn new() -> Self;

        fn test() {
            assert!(Self::new().get_greeting().len() < 200);
        }
    }

    #[derive(Eq,PartialEq)]
    enum Dialect {
        American
    }

    struct EnglisHelloImpl<T> {
        dialect: T
    }

    impl <T> Hello<T> for EnglisHelloImpl<T> {
        fn get_greeting(&self) -> &str {
                "Howdy"
        }
    }

    ///
    /// This test is showing that while we can implement two interfaces and autogenerate two test methods,
    /// we need to ensure the call to run the tests needs to call through the trait.
    ///
    /// I.e. HelloTests2::test_all() rather than Self::test_all() as the latter would be ambiguous.
    ///

    #[trait_tests]
    impl HelloTests for EnglisHelloImpl<String> { fn new() -> Self { EnglisHelloImpl { dialect: String::new() } } }

    #[trait_tests]
    impl HelloTests2 for EnglisHelloImpl<usize> { fn new() -> Self { EnglisHelloImpl { dialect: 3usize } } }
}