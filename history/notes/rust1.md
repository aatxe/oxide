# Rust1 - the heap

Rust1 is an extension of Rust0 that adds access to the heap via the type `Vec<T>`. This makes it
possible to write more typical functional programs and data structures.

## Examples

### An implementation of Box<T>

```rust
trait AsRef<T> {
  fn as_ref(&self) -> &T;
}

struct Box<T>(Vec<T>)

impl<T> Box<T> {
    fn new(item: T) -> Box<T> {
        Box({
          let mut vec = Vec::new();
          vec.push(item);
          vec
        })
    }
    
    fn unbox(mut self) -> T {
        self.0.pop().unwrap()
    }
}

impl<T> AsRef<T> for Box<T> {
    fn as_ref(&self) -> &T {
        &self.0[0]
    }
}
```

### Peano Numbers using Box

```rust
trait Add {
    fn add(self, rhs: Self) -> Self;
}

enum Num {
    Zero,
    Succ(Box<Num>),
}

impl Add for Num {
    fn add(self, rhs: Num) -> Num {
        match rhs {
            Num::Zero => self,
            Num::Succ(rhs) => Num::Succ(Box::new(self)).add(rhs.unbox()),
        }
    }
}
```
