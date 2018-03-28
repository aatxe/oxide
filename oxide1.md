# Oxide1 - Formal Rust1

**WIP**: Please note that this level is not not even remotely close to "complete." It's basically
just a sketch right now, but I'm working on it. 😊

## Table of Contents

- [Notes](#notes)
- [Summary](#summary)
- [Syntax](#syntax)

## Notes

- It seems like we probably want ranges as well to work with `Vecs** in a lot of ways.
- It appears that we might actually be able to just call `Ρ` something like "static memory" and `R`
  "memory" and put both the stack and heap inside of it without problems. This might be a nice
  simplification. It seems more promising, but also like it might make us more forgiving than Rust?

[˄ Back to top][toc]

## Summary

The general intuition I have is that we can extend `oxide0` with a heap that is essentially a less
restrained version of our stack (i.e. region environment or set), `Ρ` and `R`. Then, operations to
create `Vecs` will place things in this heap environment. The part that is left on the stack will
be a pointer to the `Vec` root coupled with the starting and ending indices in the `Vec`. Choosing
to include the starting and ending indices should give us an easy path to handling slices by simply
making them the same form as a `Vec` but with different indices.

If this approach doesn't actually end up making sense, we can try to more literally follow the Rust
`Vec` implementation which [_guarantees_ that a `Vec` is always exactly the triple
`(pointer, capacity, length)`][vec-guarantees]. I haven't thought terribly much about how this might
pan out for us though.

[˄ Back to top][toc]

[vec-guarantees]: https://doc.rust-lang.org/std/vec/struct.Vec.html#guarantees

## Syntax

```
heap pointers ϑ

heap environment Ψ ::= •
                     | Ψ, ϑ ↦ τ ⊗ { [0] ↦ ρ_0, ..., [n] ↦ ρ_n }

region environments Ρ ::= ...
                        | Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ ϑ }

types τ ::= ...
          | Vec<τ>

expressions e ::= ...
                | Vec::<τ>::new()
                | e_1[e_2]
                | e_1.push(e_2)
                | e.pop()
                | e.len()
                | e_v.swap(e_1, e_2)
                | for x in e_1 { e_2 }
```

[˄ Back to top][toc]

## Static Semantics

Judgment: `Σ; Δ; Ρ; Ψ; Γ ⊢ e : τ ⇒ Ρ'; Ψ'; Γ'`  
Meaning: In a data environment Σ, kind environment Δ, region environment Ρ, heap environment Ψ and
type environment Γ, expression e has type τ and produces the updated environments Ρ', Ψ', and Γ'.

This judgment is an extension of the main judgment in `oxide0`. I think every rule in `oxide0`
should thread through `Ψ` as they do `Ρ`.

```
fresh ϑ
------------------------------------------------------------------ T-VecNew
Σ; Δ; Ρ; Ψ; Γ ⊢ Vec::<τ>::new() : Vec<τ> ⇒ Ρ; Ψ, ϑ ↦ τ ⊗ {}; Γ

Σ; Δ; Ρ; Ψ; Γ ⊢ e_1 : Vec<τ> ⇒
--------------------------------------------------------- T-VecIndex
Σ; Δ; Ρ; Ψ; Γ ⊢ e_1[e_2] : ⇒
```

[˄ Back to top][toc]

[toc]: #table-of-contents
