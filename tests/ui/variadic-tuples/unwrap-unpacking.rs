//@ check-pass
//@ compile-flags: -Znext-solver=globally
#![feature(variadic_tuples)]
#![feature(tuple_trait)]
#![allow(incomplete_features)]

use std::marker::Tuple;

fn identity<T: Tuple>(params: (..T)) -> T {
    params
}

fn main() {}
