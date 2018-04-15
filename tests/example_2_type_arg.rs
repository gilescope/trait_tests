#![feature(proc_macro)]
extern crate trait_tests;
#[allow(dead_code)]

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello<Dialect, String> {
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello<Dialect, String> + Sized + Default {
//        fn new() -> Self;

        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }
    }

    enum Dialect {
        American
    }

    #[derive(TraitTests)]
    #[trait_test(HelloTests,Dialect,String)]
    struct EnglisHelloImpl<Dialect, X> {
        dialect: Dialect,
        tag: X
    }

    impl Hello<Dialect, String> for EnglisHelloImpl<Dialect, String> {
        fn get_greeting(&self) -> &str { "Howdy" }
    }

    //#[trait_tests]
    impl Default for EnglisHelloImpl<Dialect, String>
    {
        fn default() -> Self { EnglisHelloImpl { dialect: Dialect::American, tag: String::new() } }
    }
}