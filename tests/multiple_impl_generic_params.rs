#![feature(custom_attribute)]
#![feature(plugin)]
#![plugin(trait_tests)]
#![allow(dead_code)]

trait Wrapper {}

#[trait_tests]
trait WrapperTests : Wrapper {}

struct WrapperImpl<T> {
    contents: Vec<T>
}

impl Wrapper for WrapperImpl<String>{}

impl Wrapper for WrapperImpl<i64>{}

#[trait_tests]
impl WrapperTests for WrapperImpl<String>{}

//Bugfixed: we got "previous definition of the value `trait_test_wrapperimpl_wrappertests`" here
#[trait_tests]
impl WrapperTests for WrapperImpl<i64>{}
