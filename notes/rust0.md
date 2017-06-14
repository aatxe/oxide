# Rust0 - Safe Rust

Rust0 is the safe core of the Rust language.

## Syntax

n.b. this is currently a work-in-progress.

```rust
id ::= identifiers
SN ::= struct names
CN ::= constructor names
TN ::= trait names
T_i ::= type variables

T, V ::= SN
       | &T
       | (T_1, ..., T_n)

pat ::= id
      | CN(id*)

arm ::= pat => e

e ::= SN
    | SN::CN(e*)
    | e_1; e_2
    | { e }
    | let id = e
    | (e_1, e_2, ..., e_n)
    | (e)
    | match e { arm* }

arg ::= id: T

s ::= struct SN<T_1, ..., T_n> { arg* }
    | type T = V
    | fn<T_1, ..., T_n> id(arg*) -> T where T_1: bound, ..., T_n: bound { e }
    | enum SN<T_1, ..., T_n> { CN(id*)* }

tl ::= s
     | impl<T_1, ..., T_n) SN where T_1: bound, ..., T_n: bound
     | impl<T_1, ..., T_n) TN for SN where T_1: bound, ..., T_n: bound
```

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

### An example of higher-order functions

```rust
fn map_tup<A, B, F>(tup: (A, A, A), func: F) -> (B, B, B) where F: Fn(A) -> B {
    let (a, b, c) = tup;
    (func(a), func(b), func(c))
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

### Sorting for fixed-size arrays

```rust
trait Cmp {
    fn leq(&self, rhs: &Self) -> bool;
}

fn sort<T>(data: &mut [T]) where T: Cmp {
    for i in 1 .. data.len() {
        let mut j = i;
        while j > 0 && !(data[j - 1].leq(&data[j])) {
            data.swap(j, j - 1);
            j -= 1;
        }
    }
}

enum Thing {
    A,
    B,
    C,
    D,
    E,
}

impl Cmp for Thing {
    fn leq(&self, rhs: &Thing) -> bool {
        match self {
            &Thing::A => true,
            &Thing::B => match rhs {
                &Thing::A => false,
                _ => true,
            },
            &Thing::C => match rhs {
                &Thing::A | &Thing::B => false,
                _ => true,
            },
            &Thing::D => match rhs {
                &Thing::A | &Thing::B | &Thing::C => false,
                _ => true,
            },
            &Thing::E => match rhs {
                &Thing::A | &Thing::B | &Thing::C | &Thing::D => false,
                _ => true,
            }
        }
    }
}
```

### An example using explicit lifetime annotations.

```rust
struct RefPair<'a, 'b, L, R>(&'a L, &'b R) where L: 'a, R: 'b;

impl<'a, 'b, L, R> RefPair<'a, 'b, L, R> {
    fn new(left: &'a L, right: &'b R) -> RefPair<'a, 'b, L, R> {
        RefPair(left, right)
    }

    fn left(&self) -> &'a L {
        self.0
    }

    fn right(&self) -> &'b R {
        self.1
    }
}
```
