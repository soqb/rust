//@ compile-flags: -Znext-solver=globally
#![feature(tuple_trait)]

use std::marker::Tuple;

#[allow(dead_code)]
trait Foo {}
impl<A, B, C, R: Tuple> Foo for (A, ..R, B, C) {}
impl<D, E, F, S: Tuple> Foo for (D, E, ..S, F) {}
//~^ ERROR conflicting implementations of trait

fn main() {}
