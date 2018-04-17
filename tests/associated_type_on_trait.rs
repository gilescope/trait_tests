#![feature(proc_macro)]
extern crate trait_tests;

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello {
        type MyAssociatedType;
        fn get_greeting(&self) -> &str;
    }

    #[trait_tests]
    trait HelloTests : Hello<MyAssociatedType=isize> + Sized + Default{
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }

        fn this_should_not_be_a_test() -> &'static str { "not a test" }

        fn this_should_not_be_a_test_as_it_has_parameters(a: String) { }
    }

    #[derive(TraitTests)]
    #[trait_test(HelloTests)]
    struct SpanishHelloImpl {}

    impl Hello for SpanishHelloImpl {
        fn get_greeting(&self) -> &str { "Hola" }
        type MyAssociatedType = isize;
    }

    impl Default for SpanishHelloImpl { fn default() -> Self { SpanishHelloImpl{} } }
}