# Ownership Made Explicit (v3)

Third time's the charm?

## Syntax

```
identifiers x, y
struct names S

naturals n ∈ ℕ
fractions ζ ::= n | ζ / ζ | ζ + ζ
immediate path Π ::= x | n
paths π ::= ε | Π | Π.π ;; π is (Π(.Π)*)?
regions ρ ⊆ { π ↦ v }
environments σ ⊆ { x ↦ (ρ.π, cap ρ ζ, x_s) }

mutability μ ::= imm | mut
kinds κ ::= ★

type variables ς ::= α -- by convention, of kind ★

base types bt ::= bool | u32
primitives prim ::= true | false | n

types τ ::= ς
          | bt
          | τ_1 ⊗ ... ⊗ τ_n → τ_ret     ;; ordinary closure
          | τ_1 ⊗ ... ⊗ τ_n ↝ τ_ret     ;; move closure
          | unit
          | τ_1 ⊗ ... ⊗ τ_n
          | ∀ς: κ. τ
          | ref ρ μ τ
          | cap ρ ζ
          | S

expressions e ::= prim
                | ptr μ ρ.π
                | x
                | drop x
                | letnew x: τ = e_1 in e_2
                | let μ x: τ = y.π in e
                | |μ_1 x_1: τ_1, ..., μ_n x_n: τ_n| { e }
                | move |μ_1 x_1: τ_1, ..., μ_n x_n: τ_n| { e }
                | e_1 e_2
                | ()
                | let () = e_1 in e_2
                | (e_1, ..., e_n)
                | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = y.π in e
                | S { x_1: e_1, ..., x_n: e_n }
                | S(e_1, ..., e_N)
                | Λς: κ. e
                | e [τ]
                | e.Π

type environments Γ ::= • | Γ, {from x_s} x : τ ⊗ cap ρ ζ
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
----------------------------------------------------------------------------- T-Id
Σ; Δ; Γ, {from x_s} x : τ ⊗ cap ρ ζ ⊢ x : τ ⇒ Γ, {from x_s} x : τ ⊗ cap ρ ζ

{from x_s'} x_s : τ ⊗ cap ρ ζ_1 ∈ Γ
ζ_1 + ζ_2 ↓ ζ_n
----------------------------------------------------------------------------------------- T-Drop
Σ; Δ; Γ, {from x_s} x : τ ⊗ cap ρ ζ_2 ⊢ drop x : τ ⇒ Γ, {from x_s'} x_s : τ ⊗ cap ρ ζ_n

∀x. x ∉ e_1
Σ; Δ; Γ ⊢ e_1 : τ ⇒ Γ_1
fresh ρ
Σ; Δ; Γ_1, {} x : τ ⊗ cap ρ 1 ⊢ e_2 : τ ⇒ Γ_2
---------------------------------------------- T-LetNew
Σ; Δ; Γ ⊢ letnew x: τ = e_1 in e_2 : τ ⇒ Γ_2

{from x_s} y : τ_y ⊗ cap ρ ζ ∈ Γ
ζ ≠ 0
Σ; Δ; Γ ⊢ y.π : τ_x ⇒ Γ_1
Σ; Δ; Γ_1, {from x_s} y : τ_y ⊗ cap ρ (ζ / 2),
           {from y} x : τ_x ⊗ cap ρ (ζ / 2)
           ⊢ e : τ ⇒ Γ_2
----------------------------------------------- T-LetImm
Σ; Δ; Γ ⊢ let imm x: τ_x = y.π in e : τ ⇒ Γ_2

{from x_s} y : τ_y ⊗ cap ρ 1 ∈ Γ
ζ ≠ 0
Σ; Δ; Γ ⊢ y.π : τ_x ⇒ Γ_1
Σ; Δ; Γ_1, {from x_s} y : τ_y ⊗ cap ρ 0, {from y} x : τ_x ⊗ cap ρ 1 ⊢ e : τ ⇒ Γ_2
--------------------------------------------------------------------------------------- T-LetMut
Σ; Δ; Γ ⊢ let mut x: τ_x = y.π in e : τ ⇒ Γ_2

;; mut becomes 1, and imm is an arbitrary non-zero fraction
μ-to-ζ(μ_1, ..., μ_n) ⇒ ζ_1, ... ζ_n
ζ_1 ≠ 0 ... ζ_n ≠ 0
Σ; Δ; Γ, {} x_1 : τ_1 ⊗ cap ρ_1 ζ_1
         ...
         {} x_n : τ_n ⊗ cap ρ_n ζ_n
         ⊢ e : τ_ret ⇒ Γ'
---------------------------------------------------------------------------------- T-Closure
Σ; Δ; Γ ⊢ |μ_1 x_1: τ_1, ..., μ_n x_n: τ_n| { e } : τ_1 ⊗ ... ⊗ τ_n → τ_ret ⇒ Γ'

;; mut becomes 1, and imm is an arbitrary non-zero fraction
μ-to-ζ(μ_1, ..., μ_n) ⇒ ζ_1, ... ζ_n
ζ_1 ≠ 0 ... ζ_n ≠ 0
Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Γ_1, {} x_1 : τ_1 ⊗ cap ρ_1 ζ_1
            ...
            {} x_n : τ_n ⊗ cap ρ_n ζ_n
            ⊢ e : τ_ret ⇒ Γ_ignored
---------------------------------------------------------------------------------------- T-MvClosure
Σ; Δ; Γ ⊢ move |μ_1 x_1: τ_1, ..., μ_n x_n: τ_n| { e } : τ_1 ⊗ ... ⊗ τ_n ↝ τ_ret ⇒ Γ_2

Σ; Δ; Γ ⊢ e_1 : τ_1 ⊗ ... ⊗ τ_n → τ_ret ⇒ Γ_1
Σ; Δ; Γ_1 ⊢ e_2 : τ_1 ⊗ ... ⊗ τ_n ⇒ Γ_2
----------------------------------------------- T-App
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

{from x_s} y : τ_y ⊗ cap ρ ζ ∈ Γ
ζ ≠ 0
Σ; Δ; Γ ⊢ y.π : τ_x ⇒ Γ_1
ζ / (n + 1) ↓ ζ_n
Σ; Δ; Γ_1, {from x_s} y : τ_y ⊗ cap ρ ζ_n,
           {from y} x_1 : τ_1 ⊗ cap ρ ζ_n,
           ...
           {from y} x_n : τ_n ⊗ cap ρ ζ_n
           ⊢ e : τ_f ⇒ Γ_2
------------------------------------------------------------------------------- T-LetTupImm
Σ; Δ; Γ ⊢ let (imm x_1, ..., imm x_n): τ_1 ⊗ ... ⊗ τ_n = y.π in e : τ_f ⇒ Γ_2

mut ∈ {μ_1, ..., μ_n}
{from x_s} y : τ_y ⊗ cap ρ 1 ∈ Γ
Σ; Δ; Γ ⊢ y.π : τ_x ⇒ Γ_1
1 / n ↓ ζ_n
Σ; Δ; Γ_1, {from x_s} y : τ_y ⊗ cap ρ 0,
           {from y} x_1 : τ_1 ⊗ cap ρ ζ_n,
           ...
           {from y} x_n : τ_n ⊗ cap ρ ζ_n
           ⊢ e : τ_f ⇒ Γ_2
------------------------------------------------------------------------------- T-LetTupAnyMut
Σ; Δ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = y.π in e : τ_f ⇒ Γ_2

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

;; These arbitrary projections seem to violate our ownership model (maybe they should be invalid)

Σ; Δ; Γ ⊢ e : S ⇒ Γ'
struct S { x_1: τ_1, ..., x: τ, ..., x_n: τ_n } ∈ Σ
---------------------------------------------------- T-ProjFieldPath
Σ; Δ; Γ ⊢ e.x : τ ⇒ Γ'

Σ; Δ; Γ ⊢ e : S ⇒ Γ'
struct S(τ_1, ..., τ_t, ..., τ_n) ∈ Σ
-------------------------------------- T-ProjIndexPathStruct
Σ; Δ; Γ ⊢ e.t : τ_t ⇒ Γ'

Σ; Δ; Γ ⊢ e : τ_1 ⊗ ... ⊗ τ_t ⊗ ... ⊗ τ_n ⇒ Γ'
------------------------------------------------ T-ProjIndexPathTup
Σ; Δ; Γ ⊢ e.t : τ_t ⇒ Γ'
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
