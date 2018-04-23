#![feature(proc_macro)]
extern crate trait_tests;

#[cfg(test)]
mod example_tests {
    use trait_tests::*;

    trait Hello {
        type MyAssociatedType;
        fn get_greeting(&self) -> &str;
    }

    //TODO: autogenerate
    type HelloTestsTypeMyAssociatedType=isize;
    #[trait_tests]
    trait HelloTests : Hello<MyAssociatedType=isize> + Sized + Default{
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }

        fn this_should_not_be_a_test() -> &'static str { panic!("not a test") }

        fn this_should_not_be_a_test_as_it_has_parameters(_a: String) { panic!("not a test") }
    }

    struct SpanishHelloImpl {}

    #[test_impl]
    impl Hello for SpanishHelloImpl {
        type MyAssociatedType = isize;
        fn get_greeting(&self) -> &str { "Hola" }
    }

    impl Default for SpanishHelloImpl { fn default() -> Self { SpanishHelloImpl{} } }
}