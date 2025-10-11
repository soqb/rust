//@ run-pass
//@ compile-flags: -Znext-solver=globally
#![feature(tuple_trait)]

use std::marker::Tuple;

struct One;
struct Two;
struct Three;

trait Num {
    fn value() -> usize;
}

impl Num for One {
    fn value() -> usize {
        1
    }
}
impl Num for Two {
    fn value() -> usize {
        2
    }
}
impl Num for Three {
    fn value() -> usize {
        3
    }
}

trait Sum: Tuple {
    fn sum() -> usize;
}

impl Sum for () {
    fn sum() -> usize {
        0
    }
}

impl<T: Sum, N: Num> Sum for (..T, N) {
    fn sum() -> usize {
        T::sum() + N::value()
    }
}

fn main() {
    assert_eq!(<(One, Two, Three, Two, One) as Sum>::sum(), 9)
}
