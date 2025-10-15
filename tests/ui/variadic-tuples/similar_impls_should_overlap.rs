//@ compile-flags: -Znext-solver=globally
#![feature(variadic_tuples)]
#![feature(tuple_trait)]
#![allow(incomplete_features)]

use std::marker::Tuple;

trait Foo {}
impl<A, B, C, R: Tuple> Foo for (A, ..R, B, C) {}
impl<D, E, F, S: Tuple> Foo for (D, E, ..S, F) {}
//~^ ERROR conflicting implementations of trait `Foo`

trait Bar {}
impl<T> Bar for T {}
impl<R: Tuple> Bar for (..R) {}
//~^ ERROR conflicting implementations of trait `Bar`

fn main() {}
