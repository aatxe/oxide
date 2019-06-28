// this particular example is adapted from pseudocode from Niko
fn main() {
    let m: u32 = 0;
    let q: &'q mut u32 = &mut m;
    let r: &'r mut u32 = &mut *q; // loan L0 of `*q`
    /* can't use `q` -- L0 in scope (because `r` is live) */
    let n: u32 = 0;
    q = &mut n; // kill(L0)
    /* now I can use `q` */
    drop::<&'q mut u32>(q);
    drop::<&'r mut u32>(r);
}
