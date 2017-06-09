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
