//@ compile-flags: -Znext-solver=globally
#![feature(variadic_tuples)]
#![feature(tuple_trait)]
#![allow(incomplete_features)]

use std::marker::Tuple;

trait Foo {}
impl<R: Tuple, S: Tuple> Foo for (..R, ..S) {}
//~^ ERROR the type parameter `R` is not constrained
//~| ERROR the type parameter `S` is not constrained

trait Bar {}
impl<R: Tuple, T, S: Tuple> Bar for (..R, T, ..S) {}
//~^ ERROR the type parameter `R` is not constrained
//~| ERROR the type parameter `S` is not constrained

trait Baz {}
impl<R: Tuple, S: Tuple> Baz for ((..R, ..S), (..S, ..R)) {}
//~^ ERROR the type parameter `R` is not constrained
//~| ERROR the type parameter `S` is not constrained

trait Quux {}
impl<R: Tuple, S: Tuple> Quux for ((..R, ..S), (..R, ..S)) {}
//~^ ERROR the type parameter `R` is not constrained
//~| ERROR the type parameter `S` is not constrained

fn main() {}
