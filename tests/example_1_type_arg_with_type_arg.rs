#![feature(proc_macro)]
extern crate trait_tests;

#[allow(dead_code)]
#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<Dialect> {
        fn get_greeting(&self) -> &str;
    }

    //type HelloTestsType1 = Dialect<isize>;

    #[trait_tests]
    trait HelloTests: Hello<Dialect<isize>> + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    pub struct Dialect<T> {
        name: String,
        len: T,
    }

    struct EnglisHelloImpl<Dialect> {
        dialect: Dialect,
    }

    #[test_impl]
    impl Hello<Dialect<isize>> for EnglisHelloImpl<Dialect<isize>> {
        fn get_greeting(&self) -> &str {
            "Howdy"
        }
    }

    impl Default for EnglisHelloImpl<Dialect<isize>> {
        fn default() -> Self {
            EnglisHelloImpl {
                dialect: Dialect {
                    name: String::new(),
                    len: 10,
                },
            }
        }
    }
}
