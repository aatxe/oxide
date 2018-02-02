# Ownership Made Explicit (v2)

There's a bunch of new stuff in my head, and I want to be able to view these two systems side by
side as I make those changes, so, we begin again in a new file.

## Syntax

```
identifiers x (optionally •)
struct names S

fractions ζ ::= 1 | 0 | ζ / 2
paths π ::= ε | x | x.π
regions ρ ⊆ { π ↦ v }
environments σ ⊆ { x ↦ (ρ.π, cap ρ ζ, x_s) }

mutability μ ::= imm | mut
kinds κ ::= ★

type variables ς ::= α -- by convention, of kind ★

base types bt ::= bool | u32
primitives prim ::= true | false | n

types τ ::= ς
          | bt
          | τ_1 → τ_2
          | Unit
          | τ_1 ⊗ ... ⊗ τ_n
          | ∀ε:κ. τ
          | ref ρ μ τ
          | cap ρ ζ
          | S

expressions e ::= prim
                | ptr ρ.π
                | x
                | let x: τ = e_1 in e_2
                | let mut x: τ = e_1 in e_2
                | ()
                | let () = e_1 in e_2
                | (e_1, ..., e_n)
                | let (x_1, ..., x_n) = e_1 in e_2
                | Λς: κ. e
                | e [τ]
                | S { x_1: e_1, ..., x_n: e_n }
                | S(e_1, ..., e_N)
                | e.n
                | e.x
                
type environments Γ ::= • | Γ, x : τ ⊗ cap ρ ζ
kind environments Δ ::= • | Δ, ς : κ
data environments Σ ::= •
                      | Σ, struct S<α_1, ..., α_n> { x_1: τ_1, ..., x_n: τ_n }
                      | Σ, struct S<α_1, ..., α_n>(τ_1, ..., τ_n)
```

Shorthand: `∀α. τ ≝ ∀α:★. τ` and `Λα. e ≝ Λα:★. e`

## Static Semantics

Judgment: `Σ; Δ; Γ ⊢ e : τ ⇒ Γ'`  
Meaning: In a data environment Σ, kind environment Δ, and type environment Γ, expression e has
type τ and produces a new type environment Γ'.

```
--------------------------------------------------------------------------------------- T-IdImm
Σ; Δ; Γ, x : τ ⊗ cap ρ ζ ⊢ x : ref ρ imm τ ⊗ cap ρ (ζ / 2) ⇒ Γ, x : τ ⊗ cap ρ (ζ / 2)

---------------------------------------------------------------------------- T-IdMut
Σ; Δ; Γ, x : τ ⊗ cap ρ 1 ⊢ x : ref ρ mut τ ⊗ cap ρ 1 ⇒ Γ, x : τ ⊗ cap ρ 0

Σ; Δ; Γ ⊢ e_1 : ref ρ μ τ_1 ⊗ cap ρ ζ ⇒ Γ_1
ζ ≠ 0
Σ; Δ; Γ_1, x : τ_1 ⊗ cap ρ ζ ⊢ e_2 : τ_2 ⇒ Γ_2 
------------------------------------------------ T-LetImm
Σ; Δ; Γ ⊢ let x: τ_1 = e_1 in e_2 : τ_2 ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : ref ρ mut τ_1 ⊗ cap ρ 1 ⇒ Γ_1
Σ; Δ; Γ_1, x : τ_1 ⊗ cap ρ 1 ⊢ e_2 : τ_2 ⇒ Γ_2 
--------------------------------------------------- T-LetMut
Σ; Δ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Γ_2

fresh ρ
---------------------------------------------- T-AllocUnit
Σ; Δ; Γ ⊢ () : ref ρ mut Unit ⊗ cap ρ 1 ⇒ Γ

Σ; Δ; Γ ⊢ e_1 : ref ρ μ Unit ⊗ cap ρ ζ ⇒ Γ_1
Σ; Δ; Γ_1 ⊢ e_2 : τ_2 ⇒ Γ_2
---------------------------------------------- T-LetAllocUnit
Σ; Δ; Γ ⊢ let () = e_1 in e_2 : τ_2 ⇒ Γ_2

------------------------ T-Unit
Σ; Δ; Γ ⊢ () : Unit ⇒ Γ

Σ; Δ; Γ ⊢ e_1 : Unit ⇒ Γ_1
Σ; Δ; Γ_1 ⊢ e_2 : τ_2 ⇒ Γ_2
------------------------------------------ T-LetUnit
Σ; Δ; Γ ⊢ let () = e_1 in e_2 : τ_2 ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : τ_1 ⇒ Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : τ_n ⇒ Γ_n
fresh ρ
------------------------------------------------------------------------- T-AllocTup
Σ; Δ; Γ ⊢ (e_1, ..., e_n) : ref ρ mut (τ_1 ⊗ ... ⊗ τ_n) ⊗ cap ρ 1 ⇒ Γ_n

Σ; Δ; Γ ⊢ e_1 : ref ρ mut (τ_1 ⊗ ... ⊗ τ_n) ⊗ cap ρ 1 ⇒ Γ_1
split(cap ρ 1, n) ⇝ cap ρ ζ_1 ... cap ρ ζ_n
Σ; Δ; Γ_1, x_1 : τ_1 ⊗ cap ρ ζ_1, ..., x_n : τ_n ⊗ cap ρ ζ_n ⊢ e_2 : τ_2 ⇒ Γ_2
-------------------------------------------------------------------------------- T-LetAllocTup
Σ; Δ; Γ ⊢ let (x_1, ... x_n) = e_1 in e_2 : τ_2 ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : τ_1 ⇒ Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : τ_n ⇒ Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
---------------------------------------------------------------------- T-AllocRecordStruct
Σ; Δ; Γ ⊢ S { x_1: e_1, ... x_n: e_n } : ref ρ mut S ⊗ cap ρ 1 ⇒ Γ_n


Σ; Δ; Γ ⊢ e : ref ρ μ S ⊗ cap ρ ζ ⇒ Γ'
Σ; S ⊢ x : τ
----------------------------------------- T-ProjRecordStruct
Σ; Δ; Γ ⊢ e.x : ref ρ μ τ ⊗ cap ρ ζ ⇒ Γ'
```

**FIXME**: all the let expressions need to actually restore capabilities.

## Operational Semantics

Relation: `(σ, Ρ, e) → (σ, Ρ, e)`

# An Alternative Idea

I came up with an alternative idea while building this out. I noticed that we seem to be somehow
moving the notion of linearity "upward". That is, the typing rules themselves use cap only once,
and are the only way of interacting with it (compared to context splitting). This got me back to a
question I've wondered many times before: How linear is Rust? I have come up with a number of
different answers, and this time is no different. So, this new idea is as follows:

We have type environments `Γ ::= • | Γ, ζ of x : τ` where each binding can be read as "a fraction
ζ of x of type τ." We can split an environment using `Γ_1 ⊡ Γ_2 ⇝ Γ` and when doing so, there are
a few possibilities for each binding. A binding `ζ of x : τ` can either be copied exactly into
each context (if type `τ` implements `Copy`), can be fractionally split between each context
(corresponding to an immutable borrow), or can be used completely in only one of the contexts
(corresponding to either a mutable borrow or a move).

Outstanding questions about this alternative: Does this address the problem here that restoring
capabilities seems mechanically complex?
