extern crate trait_tests;

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests: Hello + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    struct SpanishHelloImpl {}

    #[test_impl]
    impl Hello for SpanishHelloImpl {
        fn get_greeting(&self) -> &str {
            "Hola"
        }
    }

    impl Default for SpanishHelloImpl {
        fn default() -> Self {
            SpanishHelloImpl {}
        }
    }
}
