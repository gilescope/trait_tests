#![feature(proc_macro)]
extern crate trait_tests;

#[allow(dead_code)]

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<T> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello<String> + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    #[derive(Eq,PartialEq)]
    enum Dialect {
        American
    }

    #[derive(TraitTests)]
    #[trait_test(HelloTests,String)]
    struct EnglisHelloImpl<T> {
        dialect: T
    }

    impl <T> Hello<T> for EnglisHelloImpl<T> {
        fn get_greeting(&self) -> &str {
            "Howdy"
        }
    }

    impl Default for EnglisHelloImpl<String> { fn default() -> Self { EnglisHelloImpl { dialect: String::new() } } }
}