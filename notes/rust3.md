# Rust3 - non-atomic mutation

Rust3 is an extension that adds non-atomic mutation using `Cell<T>` and `RefCell<T>`. This makes it 
possible to write programs that mutate in several places.

## Examples

### A Peano number counter with interior mutability.

```rust
enum Num {
    Zero,
    Succ(Box<Num>),
}

impl Num {
    fn succ(&self) -> Num {
        Num::Succ(Box::new(self.clone()))
    }
}

struct Counter(Rc<RefCell<Num>>);

impl Counter {
    fn inc(&self) {
        let new = self.0.borrow().succ();
        *self.0.borrow_mut() = new;
    }
    
    fn val(&self) -> Ref<Num> {
        self.0.borrow()
    }
    
    fn dup(&self) -> Counter {
        Counter(self.0.clone())
    }
}
```
