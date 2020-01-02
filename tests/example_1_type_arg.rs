extern crate trait_tests;

#[allow(dead_code)]
#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<T> {
        fn get_greeting(&self) -> &str;
    }

    //type HelloTestsType1 = String;//TODO autogen
    #[trait_tests]
    trait HelloTests: Hello<String> + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    #[derive(Eq, PartialEq)]
    enum Dialect {
        American,
    }

    struct EnglisHelloImpl<T> {
        dialect: T,
    }

    #[test_impl]
    impl<T> Hello<T> for EnglisHelloImpl<T> {
        fn get_greeting(&self) -> &str {
            "Howdy"
        }
    }

    impl Default for EnglisHelloImpl<String> {
        fn default() -> Self {
            EnglisHelloImpl {
                dialect: String::new(),
            }
        }
    }
}
