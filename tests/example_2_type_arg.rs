#![feature(custom_attribute)]
#![feature(plugin)]
#![plugin(trait_tests)]

#[cfg(test)]
mod example_tests {

    trait Hello<Dialect, String> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests<Dialect, String> : Hello<Dialect, String> + Sized {
        fn new() -> Self;

        fn test() {
            assert!(Self::new().get_greeting().len() < 200);
        }
    }

    enum Dialect {
        American
    }

    struct EnglisHelloImpl<Dialect, X> {
        dialect: Dialect,
        tag: X
    }

    impl Hello<Dialect, String> for EnglisHelloImpl<Dialect, String> {
        fn get_greeting(&self) -> &str { "Howdy" }
    }

    #[trait_tests]
    impl HelloTests<Dialect, String> for EnglisHelloImpl<Dialect, String>
    {
        fn new() -> Self { EnglisHelloImpl { dialect: Dialect::American, tag: String::new() } }
    }
}