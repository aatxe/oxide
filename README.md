# Oxide

The name is tentative, but the goal of building a Featherweight Rust is not.

## Background

To get a sense of the terminology and why the semantics is structured how it is (i.e. into levels),
I highly recommend reading [Niko's post about observational equivalence in Rust][obseq]. This should
at least be sufficient to understand why we're talking about levels of Rust, but it may well provide
other useful insights as well. [A recent description of the non-lexical lifetimes analysis][nll]
also appears to be very relevant to our approach, and may aid in its understanding.

## Terminology

- _Safe Rust_ — the core of Rust, without _any_ unsafe code.
- _Language level_ — a combination of _safe Rust_ and a set of _unsafe abstractions_ that increase
  the overall expressivity of the language, e.g. Rust1 is _safe Rust_ + `Vec<T>`.
- _Unsafe abstraction_ — an abstraction that cannot be implemented in _safe Rust_ (absolute) or the
  current _language level_ (relative) without the use of Rust's `unsafe` block.
- _Lifetime_ — the span of time from when a value is allocated to when it is deallocated.
- _Region_ — the space on the stack where a value is allocated for its _lifetime_ (see also:
  [`why-regions.md`](notes/why-regions.md)).

## Navigating this repository

This repository is split into five parts:

1. [`./`](./) — the root, containing the latest version of our semantics
    - Each language level has its own file starting with safe Rust in [`oxide0.md`](oxide0.md)
2. [`notes/`](notes/) — an assorted selection of my notes, some about the language levels of Rust
3. [`examples/`](examples/) — a collection of examples (and counter-examples) at each level
    - Each example is in "proper" Rust syntax for that level _and_ its corresponding `oxide` form.
4. [`history/`](history/) — largely-iterative prior attempts at building [`oxide0`](oxide0.md)
    - [`ownershipv1`](history/ownershipv1.md) and [`ownershipv2`](history/ownershipv2.md) both have
      some notes included that might be insightful to some degree. Evidently, I got lazy afterward
      and stopped writing actual prose in the models.
5. [`redex/`](redex/) — an outdated attempt at mechanizing the semantics in Redex
    - Maybe I'll get back to this? Maybe I'll mechanize it in Coq or F* instead?
6. [`coq/`](coq/) — an ongoing effort to mechanize the Oxide _metatheory_

## Related Works

- [Linear Regions Are All You Need][linrgn]
- [L3: A Linear Language with Locations][linloc]
- [A Step-Indexed Model of Substructural State][substruct]
- [Checking Interference with Fractional Permissions][fracperm] ([[No Paywall]][fracperm-cc])

[obseq]: http://smallcultfollowing.com/babysteps/blog/2016/10/02/observational-equivalence-and-unsafe-code/
[nll]: https://internals.rust-lang.org/t/lets-push-non-lexical-lifetimes-nll-over-the-finish-line/7115/8
[linrgn]: http://www.ccs.neu.edu/home/amal/papers/linrgn.pdf
[linloc]: http://www.ccs.neu.edu/home/amal/papers/linloc-techrpt.pdf
[substruct]: http://www.ccs.neu.edu/home/amal/papers/substruct.pdf
[fracperm]: https://link.springer.com/content/pdf/10.1007%2F3-540-44898-5_4.pdf
[fracperm-cc]: https://commie.club/papers/boyland03:frac-permissions.pdf
