#![allow(dead_code)]
#![feature(proc_macro)]

extern crate trait_tests;
use trait_tests::*;
trait Wrapper {}

#[trait_tests]
trait WrapperTests : Wrapper {}

#[derive(TraitTests)]
#[trait_test(WrapperTests, String)]
#[trait_test(WrapperTests, i64)]
struct WrapperImpl<T> {
    contents: Vec<T>
}

impl Wrapper for WrapperImpl<String>{}

impl Wrapper for WrapperImpl<i64>{}
////Bugfixed: we got "previous definition of the value `trait_test_wrapperimpl_wrappertests`" here