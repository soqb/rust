#[cfg(any())]
fn test() {
    type Foo<T> = (..T);
    //~^ ERROR variadic tuples are experimental
}

fn main() {}
