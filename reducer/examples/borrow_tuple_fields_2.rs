#![feature(box_syntax)]



struct Foo(Box<isize>, isize);

struct Bar(isize, isize);

fn main() {
    let mut x = (1, 2);
    let a = &x.0;
    let b = &mut x.0; //~ ERROR cannot borrow `x.0` as mutable because it is also borrowed as
    a.use_ref();
}

trait Fake { fn use_mut(&mut self) { } fn use_ref(&self) { }  }
impl<T> Fake for T { }
