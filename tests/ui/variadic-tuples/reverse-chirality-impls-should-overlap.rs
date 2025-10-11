//@ compile-flags: -Znext-solver=globally
#![feature(tuple_trait)]

use std::marker::Tuple;

#[allow(dead_code)]
trait Foo {}
impl<T, R: Tuple> Foo for (T, ..R) {}
impl<T, R: Tuple> Foo for (..R, T) {}
//~^ ERROR conflicting implementations of trait

fn main() {}
