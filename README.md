# Oxide

Distilling the Essence of Rust.

## Background

To get a sense of the terminology and why the semantics is structured how it is (i.e. into levels),
I highly recommend reading [Niko's post about observational equivalence in Rust][obseq]. This should
at least be sufficient to understand why we're talking about levels of Rust, but it may well provide
other useful insights as well. [Niko's recent work on non-lexical lifetimes][nll] features some key
similarities to our approach, and may aid in its understanding.

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

1. [`notes/`](notes/) — an assorted selection of my notes, some about the language levels of Rust
2. [`history/`](history/) — largely-iterative prior attempts at building designing Oxide
    - [`ownershipv1`](history/ownershipv1.md) and [`ownershipv2`](history/ownershipv2.md) both have
      some notes included that might be insightful to some degree. Evidently, I got lazy afterward
      and stopped writing actual prose in the models. Afterward, I switched to LaTeX.
3. [`history/examples/`](history/examples/) — a collection of old examples (and counter-examples) at each level
    - Each example is in "proper" Rust syntax for that level _and_ its corresponding `oxide` form at the time.
4. [`redex/`](redex/) — probably my first attempt at mechanizing the semantics (in Redex)
5. [`coq/`](coq/) — a follow-up effort to mechanize the Oxide _metatheory_
6. [`ocaml/`](ocaml/) — an implementation of Oxide in OCaml
    - Currently, it's just some small parts of Oxide for experimentation.


## Related Works

- [Linear Regions Are All You Need][linrgn]
- [L3: A Linear Language with Locations][linloc]
- [A Step-Indexed Model of Substructural State][substruct]
- [Checking Interference with Fractional Permissions][fracperm] ([[No Paywall]][fracperm-cc])

[obseq]: http://smallcultfollowing.com/babysteps/blog/2016/10/02/observational-equivalence-and-unsafe-code/
[nll]: http://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/
[linrgn]: http://www.ccs.neu.edu/home/amal/papers/linrgn.pdf
[linloc]: http://www.ccs.neu.edu/home/amal/papers/linloc-techrpt.pdf
[substruct]: http://www.ccs.neu.edu/home/amal/papers/substruct.pdf
[fracperm]: https://link.springer.com/content/pdf/10.1007%2F3-540-44898-5_4.pdf
[fracperm-cc]: https://commie.club/papers/boyland03:frac-permissions.pdf
