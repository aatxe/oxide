# Examples from Rust0 and Oxide0

This document contains examples in Rust0 with their compiled forms in Oxide0.

## Valid Programs

### Simple Points

#### Rust
```rust
struct Point {
    x: u32,
    y: u32,
}

let x = 5;
let y = 9;
Point {
    x, y
}
```

#### Oxide
```rust
struct Point {
    x: u32,
    y: u32,
}

// We require `mut` here because moves and mutable borrows are the same.
let mut x = alloc 5
in let mut y = alloc 9
in Point {
    x: borrow mut x.ε,
    y: borrow mut y.ε,
}
```

### Nested Structures

#### Rust
```rust
struct Point {
    x: u32,
    y: u32,
}

struct Rect(Point, Point)

Rect(
    Point {
        x: 0,
        y: 0,
    },
    Point {
        x: 4,
        y: 4,
    },
)
```

#### Oxide
```rust
struct Point {
    x: u32,
    y: u32,
}

struct Rect(Point, Point)

Rect(
    alloc Point {
        x: alloc 0,
        y: alloc 0,
    },
    alloc Point {
        x: alloc 4,
        y: alloc 4,
    },
)
```

### Mutation

#### Rust
```rust
struct Point {
    x: u32,
    y: u32,
}

let mut x = 5;
x = 4;
Point {
    x, 9
}
```

#### Oxide
```rust
struct Point {
    x: u32,
    y: u32,
}

let mut x = 5
in let () = x.ε := 4
in Point {
    x: borrow mut x.ε,
    y: alloc 9,
}
```

## Invalid Programs

...
