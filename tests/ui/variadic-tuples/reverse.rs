//@ run-pass
//@ compile-flags: -Znext-solver=globally
#![feature(variadic_tuples)]
#![feature(tuple_trait)]
#![allow(incomplete_features)]

use std::marker::Tuple;

trait Reverse: Tuple {
    type Rev: Tuple;
}

impl Reverse for () {
    type Rev = ();
}

impl<T, R: Reverse> Reverse for (..R, T) {
    type Rev = (T, ..<R as Reverse>::Rev);
}

fn reverse<A, B, C>((a, b, c): (A, B, C)) -> <(A, B, C) as Reverse>::Rev {
    (c, b, a)
}

fn main() {
    let args = (1usize, "hello, world!", Some('x'));
    assert_eq!(reverse(args), (Some('x'), "hello, world!", 1usize));
}

