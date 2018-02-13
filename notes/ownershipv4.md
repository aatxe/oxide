# Ownership Made Explicit (v4)

Once more, with feeling! (Yes, this is a Buffy reference)

## Syntax

```
identifiers x, y
• is a special empty identifier
struct names S

naturals n ∈ ℕ
concrete fractions ƒ ::= n | ƒ / ƒ | ƒ + ƒ
immediate path Π ::= x | n
paths π ::= ε | Π | Π.π ;; π is (Π(.Π)*)?
regions ρ ⊆ { π ↦ v }
environments σ ⊆ { x ↦ (ρ.π, cap ρ ζ, x_s) }

mutability μ ::= imm | mut
kinds κ ::= ★ | RGN | FRAC | ID

type variables ς ::= α -- by convention, of kind ★
                   | ϱ -- by convention, of kind RGN
                   | ζ -- by convention, of kind FRAC
                   | χ -- by convention, of kind ID

base types bt ::= bool | u32
primitives prim ::= true | false | n

region types r ::= ϱ -- region variables
                 | ρ -- concrete regions

identifier type ι ::= χ -- identifer variables
                    | x -- concrete identifiers

fraction types f ::= ζ -- fraction variables
                   | ƒ -- concrete fractions

types τ ::= ς
          ;; weirdly-kinded types
          | r | ι | f
          ;; ★-kind types
          | bt
          | stk τ r f ι -- fraction f of τ-value in region r aliased from ι
          | stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n → τ_ret -- ordinary closure
          | stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n ↝ τ_ret -- move closure
          | unit
          | τ_1 ⊗ ... ⊗ τ_n
          | ∀ς: κ. τ
          | S

expressions e ::= prim
                | x
                | stack e
                | borrow μ x.π -- Rust syntax: &μ x / &μ x.π
                | drop x
                | let μ x: τ = e_1 in e_2
                | |x_1: stk τ_1 r_1 f_1 ι_1, ..., x_n: stk τ_n r_n f_n ι_n| { e }
                | move |x_1: stk τ_1 r_1 f_1 ι_1, ..., x_n: stk τ_n r_n f_n ι_n| { e }
                | e_1 e_2
                | ()
                | let () = e_1 in e_2
                | (e_1, ..., e_n)
                | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2
                | S { x_1: e_1, ..., x_n: e_n }
                | S(e_1, ..., e_N)
                | Λς: κ. e
                | e [τ]
                | e.Π

type environments Γ ::= • | Γ, x ↦ stk τ r f ι 
kind environments Δ ::= • | Δ, ς : κ
data environments Σ ::= •
                      | Σ, struct S<α_1, ..., α_n> { x_1: τ_1, ..., x_n: τ_n }
                      | Σ, struct S<α_1, ..., α_n>(τ_1, ..., τ_n)
```

Shorthand: `∀α. τ ≝ ∀α:★. τ` and `Λα. e ≝ Λα:★. e`

## Static Semantics

Judgment: `Σ; Δ; Γ ⊢ e : τ ⇒ Γ'`  
Meaning: In a data environment Σ, kind environment Δ, and type environment Γ, expression e has
type τ and produces the updated environment Γ'.

```
------------------------------------------------------- T-Id
Σ; Δ; Γ, x ↦ stk τ r f ι ⊢ x : τ ⇒ Γ, x ↦ stk τ r f ι

fresh r
Σ; Δ; Γ ⊢ e : τ
------------------------------------ T-Stack
Σ; Δ; Γ ⊢ stack e : stk τ r 1 • ⇒ Γ

Γ(x) = stk τ r f ι
f ≠ 0
f / 2 ↓ f_n
Σ; τ ⊢ π : τ_π
------------------------------------------------------------------- T-BorrowImm
Σ; Δ; Γ ⊢ borrow imm x.π : stk τ_π r f_n x ⇒ Γ, x ↦ stk τ r f_n ι

Γ(x) = stk τ r 1 ι
Σ; τ ⊢ π : τ_π
------------------------------------------------------------- T-BorrowMut
Σ; Δ; Γ ⊢ borrow mut x : stk τ_π r 1 x ⇒ Γ, x ↦ stk τ r 0 ι

Γ(x_s) = stk τ_s r f_s ι
f + f_s ↓ f_n
------------------------------------------------------------------- T-DropRet
Σ; Δ; Γ, x ↦ stk τ r f x_s ⊢ drop x : τ ⇒ Γ, x_s ↦ stk τ_s r f_n ι

------------------------------------------ T-Drop
Σ; Δ; Γ, x ↦ stk τ r 1 • ⊢ drop x : τ ⇒ Γ

Σ; Δ; Γ ⊢ e_1 : stk τ_1 r_1 f_1 ι_1 ⇒ Γ_1
f_1 ≠ 0
Σ; Δ; Γ_1, x ↦ stk τ_1 r_1 f_1 ι_1 ⊢ e_2 : τ_2 ⇒ Γ_2
Γ_2(x) = stk τ_2 r_2 f_2 x_s
Γ_2(x_s) = stk τ_s r_2 f_s ι_s
f_2 + f_s ↓ f_n
----------------------------------------------------------------------------- T-LetImm
Σ; Δ; Γ ⊢ let imm x: τ_1 = e_1 in e_2 : τ_2 ⇒ Γ_2, x_s ↦ stk τ_s r_2 f_n ι_s

Σ; Δ; Γ ⊢ e_1 : stk τ_1 r_1 1 ι_1 ⇒ Γ_1
Σ; Δ; Γ_1, x ↦ stk τ_1 r_1 1 ι_1 ⊢ e_2 : τ_2 ⇒ Γ_2
Γ_2(x) = stk τ_2 r_2 0 x_s
Γ_2(x_s) = stk τ_s r_2 1 ι_s
---------------------------------------------------------------------------- T-LetMut
Σ; Δ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Γ_2, x_s ↦ stk τ_s r_2 1 ι_s

Σ; Δ; Γ, x_1 ↦ stk τ_1 r_1 f_1 ι_1,
         ...
         x_n ↦ stk τ_n r_n f_n ι_n
         ⊢ e : τ_ret ⇒ Γ'
-------------------------------------------------------------------------- T-Closure
Σ; Δ; Γ ⊢ |x_1: stk τ_1 r_1 f_1 ι_1, ..., x_n: stk τ_n r_n f_n ι_n| { e }
        : stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n → τ_ret
        ⇒ Γ'

Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Γ_1, x_1 ↦ stk τ_1 r_1 f_1 ι_1,
           ...
           x_n ↦ stk τ_n r_n f_n ι_n
           ⊢ e : τ_ret ⇒ Γ_ignored
------------------------------------------------------------------------------- T-MoveClosure
Σ; Δ; Γ ⊢ move |x_1: stk τ_1 r_1 f_1 ι_1, ..., x_n: stk τ_n r_n f_n ι_n| { e }
        : stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n ⇝ τ_ret
        ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n → τ_ret ⇒ Γ_1
Σ; Δ; Γ_1 ⊢ e_2 : stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n ⇒ Γ_2
------------------------------------------------------------------------------- T-App
Σ; Δ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n ⇝ τ_ret ⇒ Γ_1
Σ; Δ; Γ_1 ⊢ e_2 : stk τ_1 r_1 f_1 ι_1 ⊗ ... ⊗ stk τ_n r_n f_n ι_n ⇒ Γ_2
------------------------------------------------------------------------------- T-MoveApp
Σ; Δ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Γ_2

-------------------------- T-True
Σ; Δ; Γ ⊢ true : bool ⇒ Γ

--------------------------- T-False
Σ; Δ; Γ ⊢ false : bool ⇒ Γ

------------------------ T-u32
Σ; Δ; Γ ⊢ n : u32 ⇒ Γ

------------------------ T-Unit
Σ; Δ; Γ ⊢ () : unit ⇒ Γ

Σ; Δ; Γ ⊢ e_1 : unit ⇒ Γ_1
Σ; Δ; Γ_1 ⊢ e_2 : τ_2 ⇒ Γ_2
------------------------------------------ T-LetUnit
Σ; Δ; Γ ⊢ let () = e_1 in e_2 : τ_2 ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : τ_1 ⇒ Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : τ_n ⇒ Γ_n
--------------------------------------------------- T-Tup
Σ; Δ; Γ ⊢ (e_1, ..., e_n) : τ_1 ⊗ ... ⊗ τ_n ⇒ Γ_n

Σ; Δ; Γ ⊢ e_1 : stk (τ_1 ⊗ ... ⊗ τ_n) r f ι ⇒ Γ_1
f ≠ 0
f / n ↓ f_n
Σ; Δ; Γ, x_1 ↦ stk τ_1 r f_n ι,
         ...
         x_n ↦ stk τ_n r f_n ι,
         ⊢ e_2 : t_2 ⇒ Γ_2
--------------------------------------------------------------------------------- T-LetTupImm
Σ; Δ; Γ ⊢ let (imm x_1, ..., imm x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2 : τ_2 ⇒ Γ_2

mut ∈ {μ_1, ..., μ_n}
Σ; Δ; Γ ⊢ e_1 : stk (τ_1 ⊗ ... ⊗ τ_n) r 1 ι ⇒ Γ_1
fresh r_1 ... r_n
Σ; Δ; Γ, x_1 ↦ stk τ_1 r_1 1 •,
         ...
         x_n ↦ stk τ_n r_n 1 •
         ⊢ e_2 : t_2 ⇒ Γ_2
--------------------------------------------------------------------------------- T-LetTupAnyMut
Σ; Δ; Γ ⊢ let (imm x_1, ..., imm x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2 : τ_2 ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : τ_1 ⇒ Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : τ_n ⇒ Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
------------------------------------------------- T-StructRecord
Σ; Δ; Γ ⊢ S { x_1: e_1, ... x_n: e_n } : S ⇒ Γ_n

Σ; Δ; Γ ⊢ e_1 : τ_1 ⇒ Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : τ_n ⇒ Γ_n
Σ ⊢ S(τ_1, ..., τ_n)
------------------------------------- T-StructTuple
Σ; Δ; Γ ⊢ S(e_1, ..., e_n) : S ⇒ Γ_n

Σ; Δ, ς : κ; Γ ⊢ e : τ ⇒ Γ'
----------------------------- T-TAbs
Σ; Δ; Γ ⊢ Λς: κ. e : τ ⇒ Γ'

Σ; Δ; Γ ⊢ e_1 : ∀ς: κ. τ ⇒ Γ'
Δ ⊢ τ_2 : κ
-------------------------------------- T-TApp
Σ; Δ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ς] ⇒ Γ'

Σ; Δ; Γ ⊢ e : stk S r f ι ⇒ Γ'
struct S { x_1: τ_1, ..., x: τ, ..., x_n: τ_n } ∈ Σ
---------------------------------------------------- T-ProjFieldPath
Σ; Δ; Γ ⊢ e.x : stk τ r f ι ⇒ Γ'

Σ; Δ; Γ ⊢ e : stk S r f ι ⇒ Γ'
struct S(τ_1, ..., τ_t, ..., τ_n) ∈ Σ
-------------------------------------- T-ProjIndexPathStruct
Σ; Δ; Γ ⊢ e.t : stk τ_t r f ι ⇒ Γ'

Σ; Δ; Γ ⊢ e : stk (τ_1 ⊗ ... ⊗ τ_t ⊗ ... ⊗ τ_n) r f ι ⇒ Γ'
------------------------------------------------------------ T-ProjIndexPathTup
Σ; Δ; Γ ⊢ e.t : stk τ_t r f ι ⇒ Γ'
```

Judgment: `Σ ⊢ e`  
Meaning: In a structure context Σ, the struct introducing expression e is well-formed.

```
----------------------------------------------------------------------- WF-StructTuple
Σ, struct S { x_1: τ_1, ..., x_n: τ_n) ⊢ S { x_1: τ_1, ..., x_n: τ_n }

---------------------------------------------- WF-StructTuple
Σ, struct S(τ_1, ..., τ_n) ⊢ S(τ_1, ..., τ_n)

---------------- WF-StructUnit
Σ, struct S ⊢ S
```
