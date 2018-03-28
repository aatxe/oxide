# Oxide1 - Formal Rust1

**WIP**: Please note that this level is not not even remotely close to "complete." It's basically
just a sketch right now, but I'm working on it. 😊

## Table of Contents

- [Notes](#notes)
- [Summary](#summary)
- [Syntax](#syntax)
- [Type System](#static-semantics)
- [Operational Semantics](#dynamic-semantics)

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
                     | Ψ, ϑ ↦ τ

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
                | for μ x in e_1 { e_2 }
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
------------------------------------------------------------ T-VecNew
Σ; Δ; Ρ; Ψ; Γ ⊢ Vec::<τ>::new() : Vec<τ> ⇒ Ρ; Ψ, ϑ ↦ τ; Γ

Σ; Δ; Ρ; Ψ; Γ ⊢ e_1 : &r_1 f_1 Vec<τ> ⇒ Ρ_1; Ψ_1; Γ_1
Σ; Δ; Ρ_1; Ψ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Ψ_2; Γ_2
------------------------------------------------------------ T-VecIndex
Σ; Δ; Ρ; Ψ; Γ ⊢ e_1[e_2] : &r_1 f_1 τ ⇒ Ρ_2; Ψ_2; Γ_2

Σ; Δ; Ρ; Ψ; Γ ⊢ e_1 : &r_1 1 Vec<τ> ⇒ Ρ_1; Ψ_1; Γ_1
Σ; Δ; Ρ_1; Ψ_1; Γ_1 ⊢ e_2 : &r_2 1 τ ⇒ Ρ_2; Ψ_2; Γ_2
-------------------------------------------------------- T-VecPush
Σ; Δ; Ρ; Ψ; Γ ⊢ e_1.push(e_2) : unit ⇒ Ρ_2; Ψ_2; Γ_2

Σ; Δ; Ρ; Ψ; Γ ⊢ e : &r 1 Vec<τ> ⇒ Ρ'; Ψ'; Γ'
-------------------------------------------------- T-VecPop
Σ; Δ; Ρ; Ψ; Γ ⊢ e.pop() : &r_e 1 τ ⇒ Ρ'; Ψ'; Γ'

Σ; Δ; Ρ; Ψ; Γ ⊢ e : &r 1 Vec<τ> ⇒ Ρ', Ψ', Γ'
----------------------------------------------- T-VecLen
Σ; Δ; Ρ; Ψ; Γ ⊢ e.len() : u32 ⇒ Ρ', Ψ', Γ'

Σ; Δ; Ρ; Ψ; Γ ⊢ e_v : &r_v 1 Vec<τ> ⇒ Ρ_v; Ψ_v; Γ_v
Σ; Δ; Ρ_v; Ψ_v; Γ_v ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Ψ_1; Γ_1
Σ; Δ; Ρ_1; Ψ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Ψ_2; Γ_2
------------------------------------------------------------ T-VecSwap
Σ; Δ; Ρ; Ψ; Γ ⊢ e_v.swap(e_1, e_2) : &r_1 f_1 τ ⇒ Ρ_2; Ψ_2; Γ_2
```

[˄ Back to top][toc]

## Dynamic Semantics

### Syntax Extensions

```
expressions e ::= ...
                | vec ϑ n_1 n_2

values v ::= vec ϑ n_1 n_2

heaps ψ ::= • | ψ ∪ { ϑ ↦ [ ptr ρ 1, ... ] }
```

### Operational Semantics

Form: `(σ, R, ψ, e) → (σ, R, ψ, e)`

```
(σ, R, e) → (σ', R', e')
-------------------------------- E-LiftOxide0Step
(σ, R, ψ, e) → (σ', R', ψ, e')

fresh ϑ
-------------------------------------------------------------- E-VecNew
(σ, R, ψ, Vec::<τ>::new()) ↦ (σ, R, ψ ∪ { ϑ ↦ [] }, vec ϑ 0)

R(ρ_1) = ƒ_1 ⊗ { ε ↦ vec ϑ start end }
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n }
n ≤ end - start
ψ(ϑ)[n] = ptr ρ_ϑ 1
ƒ_1 / 2 ↓ ƒ_n
fresh ρ
----------------------------------------------------- E-VecIndex
(σ, R, ψ, (ptr ρ_1 ƒ_1)[ptr ρ_2 ƒ_2]) →
  (σ, R ∪ { ρ_1 ↦ ƒ_n ⊗ { ε ↦ vec ϑ start end },
            ρ ↦ ƒ_n ⊗ { ε ↦ ρ_ϑ } }, ψ, ptr ρ ƒ_n)

R(ρ_1) = 1 ⊗ { ε ↦ vec ϑ 0 n }
ψ(ϑ) = [ ptr ρ 1, ... ]
---------------------------------------------------- E-VecPush
(σ, R, ψ, (ptr ρ_1 1).push(ptr ρ_2 1)) →
  (σ, R ∪ { ρ_1 ↦ 1 ⊗ { ε ↦ vec ϑ 0 n+1 } },
      ψ ∪ { ϑ ↦ [ ptr ρ 1, ..., ptr ρ_2 1 ] }, ())

R(ρ_1) = 1 ⊗ { ε ↦ vec ϑ 0 n }
ψ(ϑ) = [ ptr ρ 1, ..., ptr ρ_n 1 ]
---------------------------------------------------------------------------- E-VecPop
(σ, R, ψ, (ptr ρ_1 1).pop()) → (σ,
                                R ∪ { ρ_1 ↦ 1 ⊗ { ε ↦ vec ϑ n-1 } },
                                ψ ∪ { ϑ ↦ [ ptr ρ 1, ..., ptr ρ_n-1 1 ] },
                                ptr ρ_n 1)

R(ρ) = 1 ⊗ { ε ↦ vec ϑ start end }
--------------------------------------------------------- E-VecLen
(σ, R, ψ, (ptr ρ 1).len()) → (σ, R, ψ, end - start + 1)

R(ρ_v) = ƒ_v ⊗ { ε ↦ vec ϑ 0 n }
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }
n_1 ≤ n    n_2 ≤ n
ψ(ϑ)[n_1] = ptr ρ_v1 1
ψ(ϑ)[n_2] = ptr ρ_v2 1
ψ(ϑ) with n_1 as ptr ρ_v2 1 and n_2 as ptr ρ_v1 1 ⇒ vec_content
----------------------------------------------------------------- E-VecSwap
(σ, R, ψ, (ptr ρ_v ƒ_v).swap(ptr ρ_1 ƒ_1, ptr ρ_2 ƒ_2)) ↦
  (σ, R, ψ ∪ { ϑ ↦ vec_content }, unit)
```

[˄ Back to top][toc]

[toc]: #table-of-contents
