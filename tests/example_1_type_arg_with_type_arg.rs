#![feature(proc_macro)]
extern crate trait_tests;

#[allow(dead_code)]

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<Dialect> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello<Dialect<isize>> + Sized + Default {
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    struct Dialect<T> {
        name: String,
        len: T
    }


    #[derive(TraitTests)]
    #[trait_test(HelloTests,Dialect<isize>)]
    struct EnglisHelloImpl<Dialect> {
        dialect: Dialect
    }

    impl Hello<Dialect<isize>> for EnglisHelloImpl<Dialect<isize>> {
        fn get_greeting(&self) -> &str { "Howdy" }
    }

    impl Default for EnglisHelloImpl<Dialect<isize>>
    {
        fn default() -> Self {
            EnglisHelloImpl {
                dialect: Dialect{name: String::new(), len:10 }
            }
        }
    }
}