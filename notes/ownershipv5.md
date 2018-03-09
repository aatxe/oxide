# Ownership Made Explicit (v5)

## Syntax

```
identifiers x, y
• is a special empty identifier
struct names S
region names ρ

naturals n ∈ ℕ
concrete fractions ƒ ::= n | ƒ / ƒ | ƒ + ƒ
immediate path Π ::= x | n
paths π ::= ε | Π.π ;; π is (Π.)*ε

mutability μ ::= imm | mut
kinds κ ::= ★ | RGN | FRAC

type variables ς ::= α -- by convention, of kind ★
                   | ϱ -- by convention, of kind RGN
                   | ζ -- by convention, of kind FRAC

region types r ::= ϱ -- region variables
                 | ρ -- concrete regions

fraction types f ::= ζ -- fraction variables
                   | ƒ -- concrete fractions

primitives prim ::= true | false | n | ()
base types bt ::= bool | u32 | unit

types τ ::= ς
          | bt
          | &r f τ -- μ-reference in region r at type τ
          | &r_1 f τ_1 ⊗ ... ⊗ &r_n f τ_n → τ_ret -- ordinary closure
          | &r_1 f τ_1 ⊗ ... ⊗ &r_n f τ_n ↝ τ_ret -- move closure
          | ∀ς: κ. τ
          | τ_1 ⊗ ... ⊗ τ_n
          | S

expressions e ::= prim
                | alloc e
                | borrow μ x.π -- Rust syntax: &μ x / &μ x.π
                | drop x
                | let μ x: τ = e_1 in e_2
                | |x_1: &r_1 f_1 τ_1, ... x_n: &r_n f_n τ_n| { e }
                | move |x_1: &r_1 f_1 τ_1, ... x_n: &r_n f_n τ_n| { e }
                | e_1 e_2
                | let () = e_1 in e_2
                | (e_1, ..., e_n)
                | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2
                | S { x_1: e_1, ..., x_n: e_n }
                | S(e_1, ..., e_n)
                | Λς: κ. e
                | e [τ]

type environments Γ ::= • | Γ, x ↦ r
kind environments Δ ::= • | Δ, ς : κ

data environments Σ ::= •
                      | Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }
                      | Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n)

region environments Ρ ::= •
                        | Ρ, r ↦ τ ⊗ ƒ ⊗ { Π ↦ r, ... }
                        | Ρ, r ↦ τ ⊗ ƒ ⊗ {}
                        | Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ r }
```

## Static Semantics

Judgment: `Σ; Δ; Ρ; Γ; e : τ ⇒ Ρ'; Γ'`  
Meaning: In a data environment Σ, kind environment Δ, region environment Ρ and type environment Γ,
expression e has type τ and produces the updated environments Ρ' and Γ'.

```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
calculate-path-set(e) ⇒ path_set
-------------------------------------------------------------- T-Alloc
Σ; Δ; Ρ; Γ ⊢ alloc e : &ρ 1 τ ⇒ Ρ', ρ ↦ τ ⊗ 1 ⊗ path_set; Γ'

Ρ(Γ(x)) = τ_x ⊗ ƒ_x ⊗ path_set
ƒ_x ≠ 0
;; walk the path through Ρ, checking that f ≠ 0, and return r_π
Ρ; path_set ⊢ π : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
------------------------------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ ⊢ borrow imm x.π : &ρ ƒ_π τ_π ⇒ Ρ, r_π ↦ τ_π ⊗ ƒ_n ⊗ π_path_set,
                                              ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ r_π }; Γ
                                              
Ρ(Γ(x)) = τ_x ⊗ 1 ⊗ path_set
;; walk the path through Ρ, checking that f = 1, and return r_π
Ρ; path_set ⊢ π : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
fresh ρ
------------------------------------------------------------------------------- T-BorrowMut
Σ; Δ; Ρ; Γ ⊢ borrow mut x.π : &ρ ƒ_π τ_π ⇒ Ρ, r_π ↦ τ_π ⊗ 0 ⊗ π_path_set,
                                              ρ ↦ τ_π ⊗ ƒ_π ⊗ { ε ↦ r_π }; Γ

Ρ(r_x) = τ_x ⊗ ƒ_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ ƒ_r ⊗ path_set
ƒ_r + ƒ_x ↓ ƒ_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ ƒ_n ⊗ path_set; Γ

Ρ(r_x) = τ ⊗ 1 ⊗ {}
Ρ' = Ρ - r_x
--------------------------------------------- T-FreeImmediate
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ

Ρ(r_x) = τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }
r_1 ∉ Ρ ... r_n ∉ Ρ ;; i.e. all the referenced regions need to have been dropped already
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------ T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ

====================================================

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ, x_1 : τ_1 ↦ r_1, ..., x_n : τ_n ↦ r_n ⊢ e : τ_ret ⇒ Ρ'; Γ'
----------------------------------------------------------------------- T-Closure
Σ; Δ; Ρ; Γ ⊢ |x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }
           : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret
           ⇒ Ρ'; Γ'

Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Ρ; Γ_1, x_1 : τ_1 ↦ r_1, ..., x_n : τ_n ↦ r_n ⊢ e : τ_ret ⇒ Ρ'; Γ_ignored
--------------------------------------------------------------------------------- T-MoveClosure
Σ; Δ; Ρ; Γ ⊢ move |x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }
           : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ↝ τ_ret
           ⇒ Ρ'; Γ_2
           
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ⇒ Ρ_2; Γ_2
------------------------------------------------------------------------- T-App
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ↝ τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ⇒ Ρ_2; Γ_2
------------------------------------------------------------------------- T-MoveApp
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2

--------------------------------- T-True
Σ; Δ; Ρ; Γ ⊢ true : bool ⇒ Ρ; Γ

---------------------------------- T-False
Σ; Δ; Ρ; Γ ⊢ false : bool ⇒ Ρ; Γ

----------------------------- T-u32
Σ; Δ; Ρ; Γ ⊢ n : u32 ⇒ Ρ; Γ

------------------------------- T-Unit
Σ; Δ; Ρ; Γ ⊢ () : unit ⇒ Ρ; Γ

Σ; Δ; Ρ; Γ ⊢ e_1 : unit ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
-------------------------------------------------- T-LetUnit
Σ; Δ; Ρ; Γ ⊢ let () = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &r_n 1 τ_n ⇒ Ρ_n; Γ_n
------------------------------------------------------------------------- T-Tup
Σ; Δ; Ρ; Γ ⊢ (e_1, ..., e_n) : &r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n ⇒ Ρ_n; Γ_n

Σ; Δ; Ρ; Γ ⊢ e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n) ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ r_1, ... x_n ↦ r_n ⊢ e_2 : t_r ⇒ Ρ_2; Γ_2
r ∉ Ρ_2
----------------------------------------------------------------- T-LetTup
Σ; Δ; Ρ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1
             in e_2 : τ_r ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : &r_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
---------------------------------------------------------- T-StructRecord
Σ; Δ; Ρ; Γ ⊢ S { x_1: e_1, ... x_n: e_n } : S ⇒ Ρ_n; Γ_n

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &r_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S(τ_1, ..., τ_n)
--------------------------------------------- T-StructTup
Σ; Δ; Ρ; Γ ⊢ S(e_1, ..., e_n) : S ⇒ Ρ_n; Γ_n

Σ; Δ, ς : κ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
----------------------------------- T-TAbs
Σ; Δ; Ρ; Γ ⊢ Λς: κ. e : ∀ς : κ. τ ⇒ Ρ'; Γ'

Σ; Δ; Ρ; Γ ⊢ e_1 : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ τ_2 : κ
---------------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ς] ⇒ Ρ'; Γ'
```

### Additional Judgments

...

## Dynamic Semantics

### Syntax Extensions

```
expresions e ::= ...
               | ptr ρ ƒ 

evaluation contexts E ::= []
                        | alloc E
                        | let μ x: τ = E in e
                        | E e
                        | v E
                        | let () = E in e
                        | (ptr ρ ƒ, ... E, e ...)
                        | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = E in e
                        | S { x: ptr ρ ƒ, ... x: E, x: e ... }
                        | S(ptr ρ ƒ, ... E, e ...)
                        | E [τ]

simple values sv ::= true | false
                   | n
                   | ()
                   | ptr ρ ƒ 

values v ::= sv
           | (sv_1, ... sv_n)
           | S { x_1: sv_1, ... x_n: sv_n }
           | S(sv_1, ..., sv_n)
           | |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
           | move |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
           | Λς: κ. e

region sets R ::= ∅
                | R ∪ { ρ ↦ ƒ ⊗ { Π ↦ ρ, ... }} 
                | R ∪ { ρ ↦ ƒ ⊗ { ε ↦ sv } }
                | R ∪ { ρ ↦ ƒ ⊗ { ε ↦ ρ } }
                
stores σ ::= • | σ ∪ { x ↦ ρ }
```

### Typing Extensions

```
------------------------------------------------------------ T-Ptr
Σ; Δ; Ρ, ρ ↦ τ ⊗ f ⊗ path_set; Γ ⊢ ptr ρ ƒ : &ρ ƒ τ ⇒ Ρ; Γ
```

### Operational Semantics

Form: `(σ, R, e) → (σ, R, e)`

```
fresh ρ
------------------------------------------------------------- E-AllocSimple
(σ, R, alloc sv) → (σ, R ∪ { ρ ↦ 1 ⊗ { ε ↦ sv } }, ptr ρ 1)

fresh ρ
-------------------------------------------------------------- E-AllocTup
(σ, R, alloc (sv_1, ..., sv_n)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ sv_1, ..., n ↦ sv_n } }, ptr ρ 1)

fresh ρ
-------------------------------------------------------------- E-AllocStuctTup
(σ, R, alloc S (sv_1, ..., sv_n)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ sv_1, ..., n ↦ sv_n } }, ptr ρ 1)

fresh ρ
----------------------------------------------------------------- E-AllocStuctRecord
(σ, R, alloc S { x_1: sv_1, ..., x_n: sv_n }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { x_1 ↦ sv_1, ..., x_n ↦ sv_n } }, ptr ρ 1)

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
ƒ_π /2 ↓ ƒ_n
fresh ρ
----------------------------------------------------------------------- E-BorrowImm
(σ, R, borrow imm x.π) →
  (σ, R ∪ { ρ_π ↦ ƒ_n ⊗ path_set, ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π } }, ptr ρ ƒ_n)

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
fresh ρ
-------------------------------------------------------------------- E-BorrowMut
(σ, R, borrow mut x.π) →
  (σ, R ∪ { ρ_π ↦ 0 ⊗ path_set, ρ ↦ 1 ⊗ { ε ↦ ρ_π } }, ptr ρ ƒ_n)

σ(x) = ρ_x
R(ρ_x) = ƒ_x ⊗ { ε ↦ ρ_s }
Ρ(ρ_s) = ƒ_s ⊗ path_set
ƒ_x + ƒ_s ↓ ƒ_n
------------------------------------------------------------ E-Drop
(σ, R, drop x) ↦ (σ / x, R ∪ { ρ_s ↦ ƒ_n ⊗ path_set }, ())

σ(x) = ρ
R(ρ) = 1 ⊗ { ε ↦ sv }
------------------------------------- E-FreeImmediate
(σ, R, drop x) ↦ (σ / x, R / ρ, ())

σ(x) = ρ
R(ρ) = 1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }
ρ_1 ∉ R ... ρ_n ∉ R
------------------------------------------ E-Free
(σ, R, drop x) ↦ (σ / x, R / ρ, ())

μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ in e) → (σ ∪ { x ↦ ρ }, R, e)

-------------------------------------------------------------------------------------------- E-App
(σ, R, (|x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }) (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)

---------------------------------------------------------------- E-MoveApp
(σ, R, (move |x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e })
       (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)

------------------------------------- E-LetUnit
(σ, R, let () = () in e) → (σ, R, e)

----------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n) = (ptr ρ_1 1, ..., ptr ρ_n 1) in e)
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)

------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [τ]) → (σ, R, e[τ / ς])
```

## Proof of Soundness

### Important Lemmas

**Lemma** (Canonical Forms):
  1. if `v` is a value of type `bool`, then `v` is either `true` or `false`.
  2. if `v` is a value of type `u32`, then `v` is a numeric value on the range `[0, 2^32)`.
  3. if `v` is a value of type `unit`, then `v` is `()`.
  4. if `v` is a value of type `&ρ ƒ τ`, then `v` is `ptr ρ ƒ`.
  5. if `v` is a value of type `(τ_1, ..., τ_n)`, then `v` is of the form `(sv_1, ..., sv_n)`.
  6. if `v` is a value of type `S`, then `v` is either of the form `S(sv_1, ..., sv_n)` or
     `S { x_1: sv_1, ..., x_n: sv_n }` depending on its definition in `Σ`.
  7. if `v` is a value of type `&r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret`, then `v` is of
     the form `|x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }`.
  8. if `v` is a value of type `&r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ↝ τ_ret`, then `v` is of
     the form `move |x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }`.
  9. if `v` is a value of type `∀ς : κ. e`, then `v` is of the form `Λς: κ. e`.

### Progress

**Theorem**:
`∀Σ, Ρ, Γ, σ, R, e. (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ') ∧ (Ρ ⊢ R) ∧ (Γ ⊢ σ)
                    ⇒ (e ∈ 𝕍) ∨ (∃σ', R', e'. (σ, R, e) → (σ', R', e'))`

#### Proof.

By induction on a derivation of `e : τ`.

The `T-True`, `T-False`, `T-Unit`, `T-u32`, `T-Ptr`, `T-Closure`, `T-MvClosure`, `T-Tup`,
`T-StructRecord`, `T-StructTup`, and `T-TAbs` cases are all immediate since `e` is in all these
cases a value. The other cases follow.

Case `T-Alloc`: `e = alloc e'`. By IH, either `e' ∈ 𝕍` or we can take a step. In the former case,
we can use the type of `e'` and our Canonical Forms lemma to do find ways to step:
  1. `e' : bool` then `E-AllocSimple` applies.
  2. `e' : u32` then `E-AllocSimple` applies.
  3. `e' : unit` then `E-AllocSimple` applies.
  4. `e' : &ρ ƒ τ` then `E-AllocSimple` applies.
  5. `e' : (τ_1, ..., τ_n)` then `E-AllocTup` applies.
  6. `e' : S` then either `E-AllocStructTup` or `E-AllocStructRecord` applies, depending on the
     definition of `S` in `Σ`.
  7. TODO: decide if this should be allowed or if we should guard against it in `T-Alloc`
  8. TODO: decide if this should be allowed or if we should guard against it in `T-Alloc`
  9. TODO: decide if this should be allowed or if we should guard against it in `T-Alloc`

Case `T-BorrowImm`: `e = borrow imm x.π`. From premise, we know `Γ ⊢ σ` and `Ρ ⊢ R`. Thus, we know
if `x : τ`, `x ∈ σ`. Looking up `x`, we get `σ(x) = ptr ρ ƒ`. With this info and `P ⊢ R` from our
premise, we know that the `R(ρ)(π)` does give us a binding and thus,  we can use `E-BorrowImm` to
step forward.

Case `T-BorrowMut`: `e = borrow mut x.π`. From premise, we know `Γ ⊢ σ` and `Ρ ⊢ R`. Thus, we know
if `x : τ`, `x ∈ σ`. Looking up `x`, we get `σ(x) = ptr ρ ƒ`. With this info and `P ⊢ R` from our
premise, we know that the `R(ρ)(π)` does give us a binding and thus,  we can use `E-BorrowMut` to
step forward.

Case `T-Drop`: `e = drop x`. From premise, we know `Γ ⊢ σ` and can thus conclude `x ∈ σ`. Looking up
`x`, we get `σ(x) = ρ` and then from `Ρ ⊢ R`, we know that  `ρ ∈ R` and we can safely apply
`E-Drop`.

Case `T-FreeImmediate`: `e = drop x`. From premise, we know `Γ ⊢ σ` and thus can conclude `x ∈ σ`.
Looking up `x`, we get `σ(x) = ρ` for which we know `ρ ∈ R` from `Ρ ⊢ R`. From the premise, we also
know that `R(ρ)` must be of the form `1 ⊗ { ε ↦ sv }` and thus we can apply `E-FreeImmediate`.

Case `T-Free`: `e = drop x`. From premise, we know `Γ ⊢ σ` and thus can conclude `x ∈ σ`. Looking up
`x`, we get `σ(x) = ρ` for which we know `ρ ∈ R` from `Ρ ⊢ R`. From the premise, we also know that
`R(ρ)` must be of the form `1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }` and that none of `ρ_1` through `ρ_n`
are in `R`. Thus, we can apply `E-Free`.

Case `T-LetImm`: `e = let imm x: τ = e_1 in e_2`. By IH, either `e_1 ∈ 𝕍` or we can take a step. In
the former case, `e_1 ∈ 𝕍` and of type `&ρ ƒ τ` from case, by Canonical Forms, `e_1` is of the
form `ptr ρ ƒ`. Thus, we can use `E-Let` to step.

Case `T-LetMut`: `e = let mut x: τ = e_1 in e_2`. By IH, either `e_1 ∈ 𝕍` or we can take a step. In
the former case, `e_1 ∈ 𝕍` and of type `&ρ ƒ τ` from case, by Canonical Forms, `e_1` is of the
form `ptr ρ ƒ`. Thus, we can use `E-Let` to step.

Case `T-App`: `e = e_1 e_2`. By IH, either `e_1 ∈ 𝕍` and `e_2 ∈ 𝕍` or we can take a step. In the
former case, we know `e_1 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n → τ_ret` and
`e_2 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n`, then by Canonical Forms `e_1` is of the form
`|x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }` and `e_2` is of the form
`(ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n)`. So, we can step using `E-App`.

Case `T-MoveApp`: `e = e_1 e_2`. By IH, either `e_1 ∈ 𝕍` and `e_2 ∈ 𝕍` or we can take a step. In the
former case, we know `e_1 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n ↝ τ_ret` and
`e_2 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n`, then by Canonical Forms `e_1` is of the form
`move |x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }` and `e_2` is of the form
`(ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n)`. So, we can step using `E-MoveApp`.

Case `T-LetUnit`: `e = let () = e_1 in e_2`. By IH, either `e_1 ∈ 𝕍` or we can take a step. In the
former case, we know `e_1 : unit` and thus by Canonical Forms `e_1` is `()`. Thus, we can step using
`E-LetUnit`.

Case `T-LetTup`: `e = let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2`. By IH, either
`e_1 ∈ 𝕍` or we can step. In the former case, we know `e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n)` and
thus by Canonical Forms, `e_1` is of the form `(ptr ρ_1 1, ..., ptr ρ_n 1)`. Thus, we can step using
`E-LetTup`.

Case `T-TApp`: `e = e_1 [τ_2]`. By IH, either `e_1 ∈ 𝕍` or we can step. In the former case, we know
`e_1 : ∀ς : κ. τ_1`. By Canonical Forms, `e_1` is of the form `Λς : κ. e` Thus, we can apply
`E-TApp` to step forward.

### Preservation

**Theorem**:
`∀Σ, Ρ, Γ, σ, R, e, σ', R', e'. (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Ρ_f; Γ_f) ∧ (σ, R, e) → (σ', R', e')
                                ⇒ ∃Ρ', Γ'. Σ; •; P'; Γ' ⊢ e' : τ ⇒ Ρ_f; Γ_f`

#### Proof.

....
