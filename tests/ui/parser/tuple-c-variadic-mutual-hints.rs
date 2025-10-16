//@ compile-flags: -Znext-solver=globally
#![feature(variadic_tuples)]
#![allow(incomplete_features)]

// traveler, rest your weary eyes somewhere else, parser tests are not fit to be seen by mortals.

type Foo = (..);
//~^ ERROR tuple unpacking `..T` must be followed by a type

type Foo<T> = (...T);
//~^ ERROR tuple unpacking `..T` must be spelled with two dots

extern "C" fn foo(args: ..);
//~^ ERROR the C-variadic type `...` must be spelled with three dots

type Foo = ..,;
//~^ ERROR tuple unpacking `..T` may not be used outside a tuple
//~| ERROR expected one of
