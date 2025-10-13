//@ compile-flags: -Znext-solver=globally
#![feature(tuple_trait)]

use std::marker::Tuple;

trait Foo {}
impl<R: Tuple, S: Tuple> Foo for (..R, ..S) {}
//~^ ERROR the type parameter `R` is not constrained
//~| ERROR the type parameter `S` is not constrained

fn main() {}
