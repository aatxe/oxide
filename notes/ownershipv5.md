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
paths π ::= ε | Π | Π.π ;; π is (Π(.Π)*)?

mutability μ ::= imm | mut
kinds κ ::= ★ | RGN | FRAC

type variables ς ::= α -- by convention, of kind ★
                   | ϱ -- by convention, of kind RGN

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

type environments Γ ::= • | Γ, x ↦ ρ
kind environments Δ ::= • | Δ, ς : κ

data environments Σ ::= •
                      | Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }
                      | Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n)

region environments Ρ ::= •
                        | Ρ, ρ ↦ ƒ ⊗ { Π ↦ ρ, ... }
                        | Ρ, ρ ↦ ƒ ⊗ { ε ↦ τ }
                        | Ρ, ρ ↦ ƒ ⊗ { ε ↦ ρ }
```

## Static Semantics

Judgment: `Σ; Δ; Ρ; Γ; e : τ ⇒ Ρ'; Γ'`  
Meaning: In a data environment Σ, kind environment Δ, region environment Ρ and type environment Γ,
expression e has type τ and produces the updated environments Ρ' and Γ'.

```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
;; we have to somehow compute a path_set here from e
----------------------------------------------------------- T-Alloc
Σ; Δ; Ρ; Γ ⊢ alloc e : &ρ 1 τ ⇒ Ρ', ρ ↦ 1 ⊗ path_set; Γ'

Ρ(Γ(x)) = ƒ_x ⊗ path_set
ƒ_x ≠ 0
canonize(π) = π_c
;; walk the path through Ρ, checking that f ≠ 0, and return ρ_π
Ρ; path_set ⊢ π_c : τ_π ⇒ ρ_π
Ρ(ρ_π) = ƒ_π ⊗ π_path_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
------------------------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ ⊢ borrow imm x.π : &ρ ƒ_π τ_π ⇒ Ρ, ρ_π ↦ ƒ_n ⊗ π_path_set,
                                              ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π }; Γ
                                              
Ρ(Γ(x)) = 1 ⊗ path_set
canonize(π) = π_c
;; walk the path through Ρ, checking that f = 1, and return ρ_π
Ρ; path_set ⊢ π_c : τ_π ⇒ ρ_π
Ρ(ρ_π) = ƒ_π ⊗ π_path_set
fresh ρ
------------------------------------------------------------------------- T-BorrowMut
Σ; Δ; Ρ; Γ ⊢ borrow mut x.π : &ρ ƒ_π τ_π ⇒ Ρ, ρ_π ↦ 0 ⊗ π_path_set,
                                              ρ ↦ ƒ_π ⊗ { ε ↦ ρ_π }; Γ

Ρ(ρ_x) = ƒ_x ⊗ { ε ↦ ρ }
Ρ(ρ) = ƒ_ρ ⊗ path_set
ƒ_ρ + ƒ_x ↓ ƒ_n
-------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ ρ_x ⊢ drop x : unit ⇒ Ρ, ρ_x ↦ ƒ_n ⊗ path_set; Γ

Ρ(ρ_x) = 1 ⊗ { ε ↦ τ }
Ρ' = Ρ - ρ_x
----------------------------------------------------------------------- T-FreeImmediate
Σ; Δ; Ρ; Γ, x ↦ ρ_x ⊢ drop x : unit ⇒ Ρ'; Γ

Ρ(ρ_x) = 1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }
ρ_1 ∉ Ρ ... ρ_n ∉ Ρ ;; i.e. all the referenced regions need to have been dropped already
Ρ' = Ρ - ρ_x
------------------------------------------------------------------------------------------ T-Free
Σ; Δ; Ρ; Γ, x ↦ ρ_x ⊢ drop x : unit ⇒ Ρ'; Γ

====================================================

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2

;; T-Closure, T-MoveClosure, T-App, T-MoveApp

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

Σ; Δ; Ρ; Γ ⊢ e_1 : τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : τ_n ⇒ Ρ_n; Γ_n
----------------------------------------------------------- T-Tup
Σ; Δ; Ρ; Γ ⊢ (e_1, ..., e_n) : τ_1 ⊗ ... ⊗ τ_n ⇒ Ρ_n; Γ_n

;; T-LetTupImm T-LetTupAnyMut

Σ; Δ; Ρ; Γ ⊢ e_1 : τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Γ_n-1 ⊢ e_n : τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
---------------------------------------------------------- T-StructRecord
Σ; Δ; Ρ; Γ ⊢ S { x_1: e_1, ... x_n: e_n } : S ⇒ Ρ_n; Γ_n

Σ; Δ; Ρ; Γ ⊢ e_1 : τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S(τ_1, ..., τ_n)
--------------------------------------------- T-StructTuple
Σ; Δ; Ρ; Γ ⊢ S(e_1, ..., e_n) : S ⇒ Ρ_n; Γ_n

Σ; Δ, ς : κ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
----------------------------------- T-TAbs
Σ; Δ; Ρ; Γ ⊢ Λς: κ. e : τ ⇒ Ρ'; Γ'

Σ; Δ; Ρ; Γ ⊢ e_1 : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ τ_2 : κ
---------------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ς] ⇒ Ρ'; Γ'
```

## Dynamic Semantics

### Syntax Extensions

```
expresions e ::= ...
               | ptr ρ ƒ 

simple values sv ::= true | false
                   | n
                   | ()
                   | ptr ρ ƒ 

values v ::= sv
           | (v_1, ... v_n)
           | S { x_1: v_1, ... x_n: v_n }
           | S(v_1, ..., v_n)
           |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
           | move |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }

region sets R ::= ∅
                | R ∪ { ρ ↦ ƒ ⊗ { Π ↦ ρ, ... }} 
                | R ∪ { ρ ↦ ƒ ⊗ { ε ↦ sv } }
                | R ∪ { ρ ↦ ƒ ⊗ { ε ↦ ρ } }
                
stores σ ::= • | σ, x := ρ
```

### Typing Extensions

...

### Operational Semantics

...

## Proof of Soundness

### Progress

...

### Preservation

...
