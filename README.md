# Oxide

The name is tentative, but the goal of building a Featherweight Rust is not.

## Background

To get a sense of the terminology and why the semantics is structured how it is (into levels), I
highly recommend reading [Niko's post about observational equivalence in Rust][niko]. This should at
least be sufficient to understand why we're talking about "levels" of Rust.

## Terminology

- _Safe Rust_ -- the core of Rust, without _any_ unsafe code.
- _Language level_ -- a combination of _safe Rust_ and a set of _unsafe abstractions_ that increase
  the overall expressivity of the language.
- _Unsafe abstraction_ -- an abstraction that cannot be implemented in _safe Rust_ (absolute) or the
  current _language level_ (relative) without the use of Rust's `unsafe` block.

## Navigating this repository

This repository is split into five parts:

1. [`./`](./) -- the root, containing the latest version of our semantics
    - Each language level has its own file starting with safe Rust in [`oxide0.md`](oxide0.md)
2. [`notes/`](notes/) -- an assorted selection of my notes, some about the language levels of Rust
3. [`examples/`](examples/) -- a collection of examples (and counter-examples) at each level
    - Each example is in "proper" Rust syntax for that level _and_ its corresponding `oxide` form.
4. [`history/`](history/) -- largely-iterative prior attempts at building [`oxide0`](oxide0.md)
    - [`ownershipv1`](history/ownershipv1.md) and [`ownershipv2`](history/ownershipv1.md) both have
      some notes included that might be insightful to some degree. I apparently got lazy afterward.
5. [`redex/`](redex/) -- an outdated attempt at mechanizing the semantics in Redex
    - maybe I'll get back to this? maybe we'll mechanize it in Coq or F* instead?

## Related Works

- [Linear Regions Are All You Need][linrgn]
- [L3: A Linear Language with Locations][linloc]
- [Checking Interference with Fractional Permissions][fracperm]

[niko]: http://smallcultfollowing.com/babysteps/blog/2016/10/02/observational-equivalence-and-unsafe-code/
[linrgn]: http://www.ccs.neu.edu/home/amal/papers/linrgn.pdf
[linloc]: http://www.ccs.neu.edu/home/amal/papers/linloc-techrpt.pdf
[fracperm]: https://link.springer.com/content/pdf/10.1007%2F3-540-44898-5_4.pdf
