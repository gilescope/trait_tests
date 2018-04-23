#![allow(dead_code)]
#![feature(proc_macro)]

extern crate trait_tests;
use trait_tests::*;
trait Wrapper {}

#[trait_tests]
trait WrapperTests : Wrapper {}

struct WrapperImpl<T> {
    contents: Vec<T>
}

#[test_impl]
impl Wrapper for WrapperImpl<String>{}


#[test_impl]
impl Wrapper for WrapperImpl<i64>{}

////Bugfixed: we got "previous definition of the value `trait_test_wrapperimpl_wrappertests`" here