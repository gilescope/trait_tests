#![feature(custom_attribute)]
#![feature(plugin)]
#![plugin(trait_tests)]

#[cfg(test)]
mod example_tests {

    trait Hello<Dialect> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests<Dialect> : Hello<Dialect> + Sized {
        fn new() -> Self;

        fn test() {
            assert!(Self::new().get_greeting().len() < 200);
        }
    }

    enum Dialect {
        American
    }

    struct EnglisHelloImpl<Dialect> {
        dialect: Dialect
    }

    impl Hello<Dialect> for EnglisHelloImpl<Dialect> {
        fn get_greeting(&self) -> &str { "Howdy" }
    }

    #[trait_tests]
    impl HelloTests<Dialect> for EnglisHelloImpl<Dialect> { fn new() -> Self { EnglisHelloImpl { dialect: Dialect::American } } }
}