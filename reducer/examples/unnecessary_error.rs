fn drop<T>(x : T) {}
fn random_bool() -> bool { true }

fn unnecessary_error() {
    let m: u32 = 0;
    let n: u32 = 1;
    let mut x: (&'x u32,) = (&m,);
    let mut y: (&'y u32,) = (&n,);
    let mut z: u32 = 2;

    if random_bool() {
        y.0 = x.0; // creates `'x: 'y` subset relation
    }

    if random_bool() {
        x.0 = &z; // creates `{L0} in 'x` constraint
        // at this point, we have `'x: 'y` and `{L0} in 'x`, so we also have `{L0} in 'y`
        drop::<&'x u32>(x.0);
    }

    z += 1; // polonius flags an (unnecessary) error

    drop(y.0);
}
