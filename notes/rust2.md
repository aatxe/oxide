# Rust2 - sharing

Rust2 is an extension that adds access to shared data through `Rc<T>` and `Arc<T>`. This makes it
possible for multiple structures to reference the same data simultaneously.

## Examples

```rust
struct Counter(Rc<usize>);

impl Counter {
    fn inc(&mut self) {
        *Rc::get_mut(&mut self.0).unwrap() += 1;
    }

    fn val(&self) -> usize {
        *self.0
    }

    fn dup(&self) -> Counter {
        Counter(self.0.clone())
    }
}
```
