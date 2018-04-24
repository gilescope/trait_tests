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




#[cfg(test)]
mod associated_type_with_param {
    use ::std::marker::PhantomData;
    use trait_tests::*;

    trait Hello {
        type MyAssociatedType;
        fn get_greeting(&self) -> &str;
    }

    //TODO: autogenerate
    type HelloTestsTypeMyAssociatedType=isize;
    type HelloTestsType1=isize;
    #[trait_tests]
    trait HelloTests : Hello<MyAssociatedType=isize> + Sized + Default{
        fn test() {
            assert!(Self::default().get_greeting().len() < 200);
        }

        fn this_should_not_be_a_test() -> &'static str { panic!("not a test") }

        fn this_should_not_be_a_test_as_it_has_parameters(_a: String) { panic!("not a test") }
    }

    struct SpanishHelloImpl<T> {
        ghost_protocol: PhantomData<T>
    }

    #[test_impl]
    impl <T> Hello for SpanishHelloImpl<T> {
        type MyAssociatedType = T;
        fn get_greeting(&self) -> &str { "Hola" }
    }

    impl <T> Default for SpanishHelloImpl<T> { fn default() -> Self { SpanishHelloImpl{ghost_protocol:PhantomData::<T>{}} } }
}