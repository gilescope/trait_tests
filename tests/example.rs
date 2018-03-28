#![feature(custom_attribute)]
#![feature(plugin)]
#![plugin(trait_tests)]

#[cfg(test)]
mod example_tests {

    trait Hello {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello + Sized {
        fn new() -> Self;

        fn test() {
            assert!(Self::new().get_greeting().len() < 200);
        }
    }

    struct SpanishHelloImpl {}

    impl Hello for SpanishHelloImpl {
        fn get_greeting(&self) -> &str { "Hola" }
    }

    #[trait_tests]
    impl HelloTests for SpanishHelloImpl { fn new() -> Self { SpanishHelloImpl{} } }
}