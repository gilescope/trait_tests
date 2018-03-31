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
    trait HelloTests : Hello<String> + Sized {
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

    #[trait_tests]
    impl HelloTests for EnglisHelloImpl<String> { fn new() -> Self { EnglisHelloImpl { dialect: String::new() } } }
}