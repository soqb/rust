//@ compile-flags: -Znext-solver=globally
#![feature(tuple_trait)]

use std::marker::Tuple;

#[allow(dead_code)]
trait Foo {}
impl<A, B, C, D, R: Tuple> Foo for (A, B, ..R, C, D) {}
impl<A, B, C, D, R: Tuple> Foo for (D, A, ..R, B, C) {}
//~^ ERROR conflicting implementations of trait

fn main() {}
