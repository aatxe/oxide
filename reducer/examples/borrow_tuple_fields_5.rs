#![feature(box_syntax)]



struct Bar(isize, isize);

fn main() {
    let mut x: Bar = Bar(1, 2);
    let a: &'a isize = &x.0;
    let b: &'b isize = &mut x.0; //~ ERROR cannot borrow `x.0` as mutable because it is also borrowed as
    use_ref(a);
}


fn use_mut<'a, T>(x: &'a mut T) {}
fn use_ref<'a, T>(x: &'a T) {}
