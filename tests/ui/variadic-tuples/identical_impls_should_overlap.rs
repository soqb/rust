//@ compile-flags: -Znext-solver=globally
#![feature(variadic_tuples)]
#![feature(tuple_trait)]
#![allow(incomplete_features)]

use std::marker::Tuple;

#[allow(dead_code)]
trait Foo {}
impl<A, B, C, D, R: Tuple> Foo for (A, B, ..R, C, D) {}
impl<E, F, G, H, S: Tuple> Foo for (H, E, ..S, F, G) {}
//~^ ERROR conflicting implementations of trait

fn main() {}
