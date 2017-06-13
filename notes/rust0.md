# Rust0 - Safe Rust

Rust0 is the safe core of the Rust language.

## Examples

### A type for optional values

```rust
enum Option<T> {
    Some(T),
    None
}

impl<T> Option<T> {
    fn unwrap(self) -> T {
        match self {
            Option::Some(res) => res,
            Option::None => panic!()
        } 
    }
}
```

### An example using associated types

```rust
trait Eq<Rhs = Self> {
    fn eq(&self, other: &Rhs) -> bool;

    fn ne(&self, other: &Rhs) -> bool {
        !self.eq(other)
    }
}

struct Foo;
struct Bar;

impl Eq for Foo {
    fn eq(&self, _: &Foo) -> bool {
        true
    }
}

impl Eq<Bar> for Foo {
    fn eq(&self, _: &Bar) -> bool {
        false
    }
}
```
