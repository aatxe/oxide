# Oxide0 - Formal Rust0

## Table of Contents

- [Syntax](#syntax)
  - [Syntax extensions for runtime](#syntax-extensions)
- [Type System](#static-semantics)
  - [Typing extensions for runtime](#typing-extensions)
- [Operational Semantics](#operational-semantics)
- [Proof of Soundness](#proof-of-soundness)
  - [Progress](#progress)
  - [Preservation](#preservation)


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
                | x.π := e
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
                        | Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ τ }
                        | Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ r }
```

## Static Semantics

Judgment: `Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'`  
Meaning: In a data environment Σ, kind environment Δ, region environment Ρ and type environment Γ,
expression e has type τ and produces the updated environments Ρ' and Γ'.

```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
------------------------------------------------------------------ T-AllocPrim
Σ; Δ; Ρ; Γ ⊢ alloc prim : &ρ 1 τ ⇒ Ρ', ρ ↦ τ ⊗ 1 ⊗ { ε ↦ τ }; Γ'

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
--------------------------------------------------------------------------- T-AllocTup
Σ; Δ; Ρ; Γ ⊢ alloc (e_1, ..., e_n) : &ρ 1 (τ_1 ⊗ ... ⊗ τ_n)
           ⇒ Ρ_n, ρ ↦ (τ_1 ⊗ ... ⊗ τ_n) ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S(τ_1, ..., τ_n)
----------------------------------------------------------- T-AllocStructTup
Σ; Δ; Ρ; Γ ⊢ alloc S(e_1, ..., e_n) : &ρ 1 S
           ⇒ Ρ_n, ρ ↦ S ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
--------------------------------------------------------------- T-AllocStructRecord
Σ; Δ; Ρ; Γ ⊢ alloc S { x_1: e_1, ..., x_n: e_n } : &ρ 1 S
           ⇒ Ρ_n, ρ ↦ S ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n

Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
-------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow imm x.π : &ρ ƒ_n τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ ƒ_n ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
                                              
Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
fresh ρ
------------------------------------------------------ T-BorrowMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow mut x.π : &ρ 1 τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ 0 ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x

Ρ(r_x) = τ_x ⊗ ƒ_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ ƒ_r ⊗ path_set
ƒ_r + ƒ_x ↓ ƒ_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ ƒ_n ⊗ path_set; Γ

Ρ(r_x) = τ ⊗ 1 ⊗ { ε ↦ τ }
Ρ' = Ρ - r_x
--------------------------------------------- T-FreeImmediate
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ

Ρ(r_x) = τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }
r_1 ∉ Ρ ... r_n ∉ Ρ ;; i.e. all the referenced regions need to have been dropped already
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------ T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ

======================================================

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

Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : τ_π ⇒ Ρ'; Γ'
------------------------------------------------ T-Assign
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.π := e : unit ⇒ Ρ'; Γ'

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
r_1 ∉ Ρ_2 ... r_n ∉ Ρ_2
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
τ_2 ∈ { f } ⇒ τ_2 ≠ 0
---------------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ς] ⇒ Ρ'; Γ'
```

### Additional Judgments

#### `Ρ ⊢ μ π in r : τ_π ⇒ r_π`
Meaning: In a region environment `Ρ` with constraints for `μ` borrows, path `π` in `r` has the type
`τ_π` in the region `r_π`.

```
μ = imm ⇒ ƒ ≠ 0   μ = mut ⇒ ƒ = 1
-------------------------------------------- P-EpsilonPath
Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ τ } ⊢ μ ε in r : τ ⇒ r

μ = imm ⇒ ƒ ≠ 0   μ = mut ⇒ ƒ = 1
Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ r_s } ⊢ μ π in r_s : τ ⇒ r_π
--------------------------------------------------- P-AliasPath
Ρ, r ↦ τ ⊗ ƒ ⊗ { ε ↦ r_s } ⊢ μ π in r : τ ⇒ r_π

μ = imm ⇒ ƒ ≠ 0   μ = mut ⇒ ƒ = 1
Ρ, r ↦ τ ⊗ ƒ ⊗ { Π_1 ↦ r_1, ..., Π ↦ r_Π, ..., Π_n ↦ r_n } ⊢ μ π in r_Π : τ_π ⇒ r_π
-------------------------------------------------------------------------------------- P-FieldPath
Ρ, r ↦ τ ⊗ ƒ ⊗ { Π_1 ↦ r_1, ..., Π ↦ r_Π, ..., Π_n ↦ r_n } ⊢ μ Π.π in r : τ_π ⇒ r_π
```

#### `Σ ⊢ Sτ`
Meaning: In a data structure context `Σ`, the long-form named data type `Sτ` is well-formed.

```
;; grammar "extensions"
Sτ ::= S(τ_1, ..., τ_n)
     | S { x_1: τ_1, ..., x_n: τ_n }

;; judgment rules

----------------------------------------------------------------------- WF-StructTuple
Σ, struct S { x_1: τ_1, ..., x_n: τ_n) ⊢ S { x_1: τ_1, ..., x_n: τ_n }

---------------------------------------------- WF-StructTuple
Σ, struct S(τ_1, ..., τ_n) ⊢ S(τ_1, ..., τ_n)
```

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
                   | |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                   | move |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                   | Λς: κ. e

values v ::= sv
           | (sv_1, ... sv_n)
           | S { x_1: sv_1, ... x_n: sv_n }
           | S(sv_1, ..., sv_n)

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
------------------------------------------------------------ E-AllocTup
(σ, R, alloc (ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)

fresh ρ
------------------------------------------------------------ E-AllocStuctTup
(σ, R, alloc S (ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)

fresh ρ
--------------------------------------------------------------- E-AllocStuctRecord
(σ, R, alloc S { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
ƒ_π / 2 ↓ ƒ_n
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
(σ, R, drop x) ↦ (σ / x, R / ρ_x ∪ { ρ_s ↦ ƒ_n ⊗ path_set }, ())

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

σ(x) = ρ
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦ 1 ⊗ { ε ↦ sv_π }
------------------------------------------------------------- E-AssignSimple
(σ, R, x.π := sv) → (σ, R ∪ { ρ_π ↦ 1 ⊗ { ε ↦ sv } }, ())

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
```
∀Σ, Ρ, Γ, σ, R, e. (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ') ∧ (Ρ ⊢ R) ∧ (Γ ⊢ σ)
                     ⇒ (e ∈ 𝕍) ∨ (∃σ', R', e'. (σ, R, e) → (σ', R', e'))
```

#### Proof.

By induction on the derivation of `e : τ`.

The `T-True`, `T-False`, `T-Unit`, `T-u32`, `T-Ptr`, `T-Closure`, `T-MvClosure`, `T-Tup`,
`T-StructRecord`, `T-StructTup`, and `T-TAbs` cases are all immediate since `e` is in all these
cases a value. The other cases follow.

##### Case `T-AllocPrim`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
------------------------------------------------------------------ T-AllocPrim
Σ; Δ; Ρ; Γ ⊢ alloc prim : &ρ 1 τ ⇒ Ρ', ρ ↦ τ ⊗ 1 ⊗ { ε ↦ τ }; Γ'
```

We want to step with:
```
fresh ρ
------------------------------------------------------------- E-AllocSimple
(σ, R, alloc sv) → (σ, R ∪ { ρ ↦ 1 ⊗ { ε ↦ sv } }, ptr ρ 1)
```

It is easy to check that all primitives are included in `sv` (and `𝕍`). Thus, we can step with
`E-AllocSimple`.

##### Case `T-AllocTup`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
--------------------------------------------------------------------------- T-AllocTup
Σ; Δ; Ρ; Γ ⊢ alloc (e_1, ..., e_n) : &ρ 1 (τ_1 ⊗ ... ⊗ τ_n)
           ⇒ Ρ_n, ρ ↦ (τ_1 ⊗ ... ⊗ τ_n) ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

We want to step with:
```
fresh ρ
------------------------------------------------------------ E-AllocTup
(σ, R, alloc (ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)
```

By IH, either `e_1 ∈ 𝕍` through `e_n ∈ 𝕍` or we can take a step for one of them. If they're all
values, we know from their types (`&ρ_1 1 τ_1` through `&ρ_n 1 τ_n`) and Canonical Forms, that `e_1`
through `e_n` are `ptr ρ_1 1` through `ptr ρ_n 1`. Thus, we can step with `E-AllocTup`.

##### Case `T-AllocStructTup`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S(τ_1, ..., τ_n)
----------------------------------------------------------- T-AllocStructTup
Σ; Δ; Ρ; Γ ⊢ alloc S(e_1, ..., e_n) : &ρ 1 S
           ⇒ Ρ_n, ρ ↦ S ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

We want to step with:
```
fresh ρ
------------------------------------------------------------ E-AllocStuctTup
(σ, R, alloc S (ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)
```

By IH, either `e_1 ∈ 𝕍` through `e_n ∈ 𝕍` or we can take a step for one of them. If they're all
values, we know from their types (`&ρ_1 1 τ_1` through `&ρ_n 1 τ_n`) and Canonical Forms, that `e_1`
through `e_n` are `ptr ρ_1 1` through `ptr ρ_n 1`. Thus, we can step with `E-AllocStructTup`.

##### Case `T-AllocStructRecord`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
--------------------------------------------------------------- T-AllocStructRecord
Σ; Δ; Ρ; Γ ⊢ alloc S { x_1: e_1, ..., x_n: e_n } : &ρ 1 S
           ⇒ Ρ_n, ρ ↦ S ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n
```

We want to step with:
```
fresh ρ
--------------------------------------------------------------- E-AllocStuctRecord
(σ, R, alloc S { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)
```

By IH, either `e_1 ∈ 𝕍` through `e_n ∈ 𝕍` or we can take a step for one of them. If they're all
values, we know from their types (`&ρ_1 1 τ_1` through `&ρ_n 1 τ_n`) and Canonical Forms, that `e_1`
through `e_n` are `ptr ρ_1 1` through `ptr ρ_n 1`. Thus, we can step with `E-AllocStructRecord`.

##### Case `T-BorrowImm`:

From premise:
```
Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
-------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow imm x.π : &ρ ƒ_n τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ ƒ_n ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
```

We want to step with:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
----------------------------------------------------------------------- E-BorrowImm
(σ, R, borrow imm x.π) →
  (σ, R ∪ { ρ_π ↦ ƒ_n ⊗ path_set, ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π } }, ptr ρ ƒ_n)
```

From premise, we also know `Γ ⊢ σ` and `Ρ ⊢ R`. The former tells us that we can look up `σ(x)` to
get `ptr ρ_x ƒ_x`. With that and `Ρ ⊢ R`, we know `ρ_x ∈ Ρ` and that `R(ρ_x)(π)` is valid. From
the typing rule's premise, we know that the fractions are non-zero along the path, and so this
condition is met for `E-BorrowImm` as well. Thus, we can indeed step with `E-BorrowImm`.

##### Case `T-BorrowMut`:

From premise:
```
Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
fresh ρ
------------------------------------------------------ T-BorrowMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow mut x.π : &ρ 1 τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ 0 ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
```

We want to step with:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
fresh ρ
-------------------------------------------------------------------- E-BorrowMut
(σ, R, borrow mut x.π) →
  (σ, R ∪ { ρ_π ↦ 0 ⊗ path_set, ρ ↦ 1 ⊗ { ε ↦ ρ_π } }, ptr ρ ƒ_n)
```

From premise, we also know `Γ ⊢ σ` and `Ρ ⊢ R`. The former tells us that we can look up `σ(x)` to
get `ptr ρ_x ƒ_x`. With that and `Ρ ⊢ R`, we know `ρ_x ∈ Ρ` and that `R(ρ_x)(π)` is valid. From
the typing rule's premise, we know that the fractions are 1 along the path, and so this
condition is met for `E-BorrowMut` as well. Thus, we can indeed step with `E-BorrowMut`.

##### Case `T-Drop`:

From premise:
```
Ρ(r_x) = τ_x ⊗ ƒ_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ ƒ_r ⊗ path_set
ƒ_r + ƒ_x ↓ ƒ_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ ƒ_n ⊗ path_set; Γ
```

We want to step with:
```
σ(x) = ρ_x
R(ρ_x) = ƒ_x ⊗ { ε ↦ ρ_s }
Ρ(ρ_s) = ƒ_s ⊗ path_set
ƒ_x + ƒ_s ↓ ƒ_n
------------------------------------------------------------ E-Drop
(σ, R, drop x) ↦ (σ / x, R / ρ_x ∪ { ρ_s ↦ ƒ_n ⊗ path_set }, ())
```

From premise, we know `Γ ⊢ σ` and can thus conclude `x ∈ σ`. Looking up `x`, we get `σ(x) = ρ` and
then from `Ρ ⊢ R`, we know that  `ρ ∈ R` and we can safely apply `E-Drop`.

##### Case `T-FreeImmediate`:

From premise:
```
Ρ(r_x) = τ ⊗ 1 ⊗ { ε ↦ τ}
Ρ' = Ρ - r_x
--------------------------------------------- T-FreeImmediate
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ
```

We want to step with:
```
σ(x) = ρ
R(ρ) = 1 ⊗ { ε ↦ sv }
------------------------------------- E-FreeImmediate
(σ, R, drop x) ↦ (σ / x, R / ρ, ())
```

From premise, we know `Γ ⊢ σ` and thus can conclude `x ∈ σ`. Looking up `x`, we get `σ(x) = ρ` for
which we know `ρ ∈ R` from `Ρ ⊢ R`. From the premise, we also know that `R(ρ)` must be of the form
`1 ⊗ { ε ↦ sv }` and thus we can apply `E-FreeImmediate`.

##### Case `T-Free`:

From premise:
```
Ρ(r_x) = τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }
r_1 ∉ Ρ ... r_n ∉ Ρ ;; i.e. all the referenced regions need to have been dropped already
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------ T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ
```

We want to step with:
```
σ(x) = ρ
R(ρ) = 1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }
ρ_1 ∉ R ... ρ_n ∉ R
------------------------------------------ E-Free
(σ, R, drop x) ↦ (σ / x, R / ρ, ())
```

From premise, we know `Γ ⊢ σ` and thus can conclude `x ∈ σ`. Looking up `x`, we get `σ(x) = ρ` for
which we know `ρ ∈ R` from `Ρ ⊢ R`. From the premise, we also know that `R(ρ)` must be of the form
`1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }` and that none of `ρ_1` through `ρ_n` are in `R`. Thus, we can
apply `E-Free`.

##### Case `T-LetImm`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

We want to step with:
```
μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ in e) → (σ ∪ { x ↦ ρ }, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, `e_1 ∈ 𝕍` and of type `&ρ ƒ τ`
from case, by Canonical Forms, `e_1` is of the form `ptr ρ ƒ`. Thus, we can use `E-Let` to step.

##### Case `T-LetMut`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

We want to step with:
```
μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ in e) → (σ ∪ { x ↦ ρ }, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, `e_1 ∈ 𝕍` and of type `&ρ ƒ τ`
from case, by Canonical Forms, `e_1` is of the form `ptr ρ ƒ`. Thus, we can use `E-Let` to step.

##### Case `T-Assign`:

From premise:
```
Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : τ_π ⇒ Ρ'; Γ'
------------------------------------------------ T-Assign
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.π := e : unit ⇒ Ρ'; Γ'
```

We want to step with:
```
σ(x) = ρ
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦ 1 ⊗ { ε ↦ sv_π }
------------------------------------------------------------- E-AssignSimple
(σ, R, x.π := sv) → (σ, R ∪ { ρ_π ↦ 1 ⊗ { ε ↦ sv } }, ())
```

By IH, either `e ∈ 𝕍` or we can take a step. In the former case, if `τ_π` is a simple type (i.e.
not a struct or tuple), then by Canonical Forms, we know that `e` is a simple value `sv`. Then, we
can step using `E-AssignSimple`.

##### Case `T-App`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ⇒ Ρ_2; Γ_2
------------------------------------------------------------------------- T-App
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2
```

We want to step with:
```
-------------------------------------------------------------------------------------------- E-App
(σ, R, (|x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }) (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

By IH, either `e_1 ∈ 𝕍` and `e_2 ∈ 𝕍` or we can take a step. In the former case, we know
`e_1 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n → τ_ret` and
`e_2 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n`, then by Canonical Forms `e_1` is of the form
`|x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }` and `e_2` is of the form
`(ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n)`. So, we can step using `E-App`.

##### Case `T-MoveApp`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ↝ τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ⇒ Ρ_2; Γ_2
------------------------------------------------------------------------- T-MoveApp
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2
```

We want to step with:
```
---------------------------------------------------------------- E-MoveApp
(σ, R, (move |x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e })
       (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

By IH, either `e_1 ∈ 𝕍` and `e_2 ∈ 𝕍` or we can take a step. In the former case, we know
`e_1 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n ↝ τ_ret` and `e_2 : &ρ_1 ƒ_1 τ_1 ⊗ ... ⊗ &ρ_n ƒ_n τ_n`,
then by Canonical Forms `e_1` is of the form
`move |x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }` and `e_2` is of the form
`(ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n)`. So, we can step using `E-MoveApp`.

##### Case `T-LetUnit`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : unit ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
-------------------------------------------------- T-LetUnit
Σ; Δ; Ρ; Γ ⊢ let () = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

We want to step with:
```
------------------------------------- E-LetUnit
(σ, R, let () = () in e) → (σ, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, we know `e_1 : unit` and thus by
Canonical Forms `e_1` is `()`. Thus, we can step using `E-LetUnit`.

##### Case `T-LetTup`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n) ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ r_1, ... x_n ↦ r_n ⊢ e_2 : t_r ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2 ... r_n ∉ Ρ_2
----------------------------------------------------------------- T-LetTup
Σ; Δ; Ρ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1
             in e_2 : τ_r ⇒ Ρ_2; Γ_2
```

We want to step with:
```
----------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n) = (ptr ρ_1 1, ..., ptr ρ_n 1) in e)
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can step. In the former case, we know
`e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n)` and thus by Canonical Forms, `e_1` is of the form
`(ptr ρ_1 1, ..., ptr ρ_n 1)`. Thus, we can step using `E-LetTup`.

##### Case `T-TApp`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ τ_2 : κ
τ_2 ∈ { f } ⇒ τ_2 ≠ 0
---------------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ς] ⇒ Ρ'; Γ'
```

We want to step with:
```
------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [τ]) → (σ, R, e[τ / ς])
```

By IH, either `e_1 ∈ 𝕍` or we can step. In the former case, we know `e_1 : ∀ς : κ. τ_1`. By
Canonical Forms, `e_1` is of the form `Λς : κ. e` Thus, we can apply `E-TApp` to step forward.

### Preservation

**Theorem**:
```
∀Σ, Ρ, Γ, σ, R, e, σ', R', e'. (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Ρ_f; Γ_f) ∧ (σ, R, e) → (σ', R', e')
                                 ⇒ ∃Ρ', Γ'. Σ; •; P'; Γ' ⊢ e' : τ ⇒ Ρ_f; Γ_f
```

#### Proof.

By induction on the stepping from `(σ, R, e) → (σ', R', e')`.

##### Case `E-AllocSimple`:

From premise:
```
fresh ρ
------------------------------------------------------------- E-AllocSimple
(σ, R, alloc sv) → (σ, R ∪ { ρ ↦ 1 ⊗ { ε ↦ sv } }, ptr ρ 1)
```

From premise and knowledge that `e` is  form `alloc e'`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
------------------------------------------------------------------ T-AllocPrim
Σ; Δ; Ρ; Γ ⊢ alloc prim : &ρ 1 τ ⇒ Ρ', ρ ↦ τ ⊗ 1 ⊗ { ε ↦ τ }; Γ'
```

`Γ'`: `E-AllocSimple` did not change `σ` and so we pick `Γ` as `Γ'`.

`Ρ'`: `E-AllocSimple` changed `R` by adding a binding for a fresh `ρ`. So, we can pick `Ρ'` to be
`Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding `ρ ↦ τ ⊗ 1 ⊗ { ε ↦ τ }`. This
corresponds to the same change we see being made in `T-AllocPrim`.

`e'` is well-typed: From `E-AllocSimple`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and `Ρ'` that
we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some fraction `ƒ`)
to derive `e' : &ρ 1 τ`.

##### Case `E-AllocTup`:

From premise:
```
fresh ρ
------------------------------------------------------------ E-AllocTup
(σ, R, alloc (ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `alloc (e_1, ..., e_n)`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
--------------------------------------------------------------------------- T-AllocTup
Σ; Δ; Ρ; Γ ⊢ alloc (e_1, ..., e_n) : &ρ 1 (τ_1 ⊗ ... ⊗ τ_n)
           ⇒ Ρ_n, ρ ↦ (τ_1 ⊗ ... ⊗ τ_n) ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

`Γ'`: `E-AllocTup` did not change `σ` and so we pick `Γ` as `Γ'`.

`Ρ'`: `E-AllocTup` changed `R` by adding a binding for a fresh `ρ`. So, we can pick `Ρ'` to be
`Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n }`. This corresponds to the same change we see being made in
`T-AllocTup`.

`e'` is well-typed: From `E-AllocTup`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and `Ρ'` that
we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some fraction `ƒ`)
to derive `e' : &ρ 1 τ`.

##### Case `E-AllocStructTup`:

From premise:
```
fresh ρ
------------------------------------------------------------ E-AllocStructTup
(σ, R, alloc S (ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `alloc S(e_1, ..., e_n)`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S(τ_1, ..., τ_n)
----------------------------------------------------------- T-AllocStructTup
Σ; Δ; Ρ; Γ ⊢ alloc S(e_1, ..., e_n) : &ρ 1 S
           ⇒ Ρ_n, ρ ↦ S ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

`Γ'`: `E-AllocStructTup` did not change `σ` and so we pick `Γ` as `Γ'`.

`Ρ'`: `E-AllocStructTup` changed `R` by adding a binding for a fresh `ρ`. So, we can pick `Ρ'` to be
`Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n }`. This corresponds to the same change we see being made in
`T-AllocStructTup`.

`e'` is well-typed: From `E-AllocStructTup`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and `Ρ'`
that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some fraction
`ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-AllocStructRecord`:

From premise:
```
fresh ρ
--------------------------------------------------------------- E-AllocStuctRecord
(σ, R, alloc S { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `alloc S { x_1: e_1, ..., x_n: e_n }`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
--------------------------------------------------------------- T-AllocStructRecord
Σ; Δ; Ρ; Γ ⊢ alloc S { x_1: e_1, ..., x_n: e_n } : &ρ 1 S
           ⇒ Ρ_n, ρ ↦ S ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n
```

`Γ'`: `E-AllocStructRecord` did not change `σ` and so we pick `Γ` as `Γ'`.

`Ρ'`: `E-AllocStructRecord` changed `R` by adding a binding for a fresh `ρ`. So, we can pick `Ρ'` to
be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }`. This corresponds to the same change we see being made
in `T-AllocStructRecord`.

`e'` is well-typed: From `E-AllocStructRecord`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-BorrowImm`:

From premise:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
----------------------------------------------------------------------- E-BorrowImm
(σ, R, borrow imm x.π) →
  (σ, R ∪ { ρ_π ↦ ƒ_n ⊗ path_set, ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π } }, ptr ρ ƒ_n)
```

From premise and knowledge that `e` is of the form `borrow imm x.π`:
```
Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
ƒ_π / 2 ↓ ƒ_n
fresh ρ
-------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow imm x.π : &ρ ƒ_n τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ ƒ_n ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
```

`Γ'`: `E-BorrowImm` did not change `σ` and so we pick `Γ` as `Γ'`.

`Ρ'`: `E-BorrowImm` changed `R` by adding a binding for a fresh `ρ`. So, we can pick `Ρ'` to
be `Ρ` (recall from the premise `Ρ ⊢ R`) with the changed binding for `ρ_π` modifying the fraction
from `ƒ_π` to `ƒ_n` and the extra binding `ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ ρ_π }`. This corresponds to the
same change we see being made in `T-BorrowImm`.

`e'` is well-typed: From `E-BorrowImm`, we know `e' = ptr ρ ƒ_n`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ ƒ_n τ_π`.

##### Case `E-BorrowMut`:

From premise:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
fresh ρ
-------------------------------------------------------------------- E-BorrowMut
(σ, R, borrow mut x.π) →
  (σ, R ∪ { ρ_π ↦ 0 ⊗ path_set, ρ ↦ 1 ⊗ { ε ↦ ρ_π } }, ptr ρ ƒ_n)
```

From premise and knowledge that `e` is of the form `borrow mut x.π`:
```
Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
fresh ρ
------------------------------------------------------ T-BorrowMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow mut x.π : &ρ 1 τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ 0 ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
```

`Γ'`: `E-BorrowMut` did not change `σ` and so we pick `Γ` as `Γ'`.

`Ρ'`: `E-BorrowMut` changed `R` by adding a binding for a fresh `ρ`. So, we can pick `Ρ'` to
be `Ρ` (recall from the premise `Ρ ⊢ R`) with the changed binding for `ρ_π` modifying the fraction
from `ƒ_π` to `1` and the extra binding `ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ ρ_π }`. This corresponds to the same
change we see being made in `T-BorrowMut`.

`e'` is well-typed: From `E-BorrowMut`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-Drop`:

From premise:
```
σ(x) = ρ_x
R(ρ_x) = ƒ_x ⊗ { ε ↦ ρ_s }
Ρ(ρ_s) = ƒ_s ⊗ path_set
ƒ_x + ƒ_s ↓ ƒ_n
------------------------------------------------------------ E-Drop
(σ, R, drop x) ↦ (σ / x, R / ρ_x ∪ { ρ_s ↦ ƒ_n ⊗ path_set }, ())
```

From premise and knowledge that `e` is of the form `drop x`:
```
Ρ(r_x) = τ_x ⊗ ƒ_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ ƒ_r ⊗ path_set
ƒ_r + ƒ_x ↓ ƒ_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ ƒ_n ⊗ path_set; Γ
```

`Γ'`: `E-Drop` changed `σ` by removing `x` and so we can mirror the change by picking `Γ'` to be
`Γ / x`.

`Ρ'`: `E-Drop` changes `R` by removing `ρ_x` and updating the binding for `ρ_s` with the new
fraction `ƒ_n`. So, we'll pick `Ρ'` that mirrors this by taking `Ρ`, removing `ρ_x` and adding
`ρ_s ↦ τ_s ⊗ ƒ_n ⊗ path_set`.

`e'` is well-typed: From `E-Drop`, we know `e' = ()` and this is trivially well-typed by `T-Unit`.

##### Case `E-FreeImmediate`:

From premise:
```
σ(x) = ρ
R(ρ) = 1 ⊗ { ε ↦ sv }
------------------------------------- E-FreeImmediate
(σ, R, drop x) ↦ (σ / x, R / ρ, ())
```

From premise and knowledge that `e` is of the form `drop x`:
```
Ρ(r_x) = τ ⊗ 1 ⊗ { ε ↦ τ }
Ρ' = Ρ - r_x
--------------------------------------------- T-FreeImmediate
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ
```

`Γ'`: `E-FreeImmediate` changed `σ` by removing `x` and so we can mirror the change by picking `Γ'`
to be `Γ / x`.

`Ρ'`: `E-FreeImmediate` changed `R` by removing `ρ` and so we can mirror the change by picking `Ρ'`
to be `Ρ / x`.

`e'` is well-typed: From `E-FreeImmediate`, we know `e' = ()` and this is trivially well-typed by
`T-Unit`.

##### Case `E-Free`:

From premise:
```
σ(x) = ρ
R(ρ) = 1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }
ρ_1 ∉ R ... ρ_n ∉ R
------------------------------------------ E-Free
(σ, R, drop x) ↦ (σ / x, R / ρ, ())
```

From premise and knowledge that `e` is of the form `drop x`:
```
Ρ(r_x) = τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }
r_1 ∉ Ρ ... r_n ∉ Ρ ;; i.e. all the referenced regions need to have been dropped already
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------ T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ
```

`Γ'`: `E-Free` changed `σ` by removing `x` and so we can mirror the change by picking `Γ'` to be
`Γ / x`.

`Ρ'`: `E-Free` changed `R` by removing `ρ` and so we can mirror the change by picking `Ρ'` to be
`Ρ / x`.

`e'` is well-typed: From `E-Free`, we know `e' = ()` and this is trivially well-typed by `T-Unit`.

##### Case `E-Let`:

From premise:
```
μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ in e) → (σ ∪ { x ↦ ρ }, R, e)
```

From premise and knowledge that `e` is of the form `let μ x: τ = ptr ρ ƒ`, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2
```
or:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ Ρ_2
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

`Γ'`: `E-Let` adds a new binding to `σ` for `x` to `ρ`, and so we can pick `Γ'` to have the
analagous change of adding `x ↦ ρ` to `Γ`.

`Ρ'`: `E-Let` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`.

`e'` is well-typed: We know from the premises of `T-LetImm` and `T-LetMut` that `e_2` is well typed
in our `Γ'`. Since `E-Let` steps to `e_2`, we then know that it's well-typed.

##### Case 'E-AssignSimple':

From premise:
```
σ(x) = ρ
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦ 1 ⊗ { ε ↦ sv_π }
------------------------------------------------------------- E-AssignSimple
(σ, R, x.π := sv) → (σ, R ∪ { ρ_π ↦ 1 ⊗ { ε ↦ sv } }, ())
```

From premise and knowledge that `e` is of the form `x.π := e_1` then:
```
Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : τ_π ⇒ Ρ'; Γ'
------------------------------------------------ T-Assign
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.π := e : unit ⇒ Ρ'; Γ'
```

`Γ'`: `E-AssignSimple` leaves `σ` unchanged, and so we can pick `Γ` as `Γ'`.

`Ρ'`: In `E-AssignSimple`, we update the binding for `ρ_π` in `R` to point to the new value. Since
the type of this value does not change, we can pick `Ρ` as `Ρ'`.

`e'` is well-typed: Since the resulting expression is `()`, the result is well-typed by `T-Unit`.

##### Case `E-App`:

From premise:
```
-------------------------------------------------------------------------------------------- E-App
(σ, R, (|x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }) (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

From premise and knowledge that `e` is of the form `e_1 e_2` then:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ⇒ Ρ_2; Γ_2
------------------------------------------------------------------------- T-App
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2
```

`Γ'`: In `E-App`, we add new bindings to `σ` for `x_1` through `x_n`. We can mirror this for `Γ` by
picking `Γ'` to be `Γ, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n`.

`Ρ'`: `E-App` leaves `R` unchanged, and so we can pick `Ρ` as `Ρ'`.

`e'` is well-typed: Since we know `e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret`, we know that
`e`, the body of the function and the result of stepping by `E-App`, is well typed in our `Γ'`.

##### Case `E-App`:

From premise:
```
---------------------------------------------------------------- E-MoveApp
(σ, R, (move |x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e })
       (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

From premise and knowledge that `e` is of the form `e_1 e_2` then:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ↝ τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ⇒ Ρ_2; Γ_2
------------------------------------------------------------------------- T-MoveApp
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2
```

`Γ'`: In `E-MoveApp`, we add new bindings to `σ` for `x_1` through `x_n`. We can mirror this for `Γ`
by picking `Γ'` to be `Γ, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n`.

`Ρ'`: `E-MoveApp` leaves `R` unchanged, and so we can pick `Ρ` as `Ρ'`.

`e'` is well-typed: Since we know `e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret`, we know that
`e`, the body of the function and the result of stepping by `E-MoveApp`, is well typed in our `Γ'`.

##### Case `E-LetUnit`:

From premise:
```
------------------------------------- E-LetUnit
(σ, R, let () = () in e) → (σ, R, e)
```

From premise and knowledge that `e` is of the form ``, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : unit ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
-------------------------------------------------- T-LetUnit
Σ; Δ; Ρ; Γ ⊢ let () = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

`Γ'`: `E-LetUnit` leaves `σ` unchanged and so we can pick `Γ'` to be `Γ`.

`Ρ'`: `E-LetUnit` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`.

`e'` is well-typed: We know from the `T-LetUnit` that `e_2`, our result, is well-typed.

##### Case `E-LetTup`:

From premise:
```
----------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n) = (ptr ρ_1 1, ..., ptr ρ_n 1) in e)
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

From premise and knowledge that `e` is of the form ``, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n) ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ r_1, ... x_n ↦ r_n ⊢ e_2 : t_r ⇒ Ρ_2; Γ_2
r ∉ Ρ_2
----------------------------------------------------------------- T-LetTup
Σ; Δ; Ρ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1
             in e_2 : τ_r ⇒ Ρ_2; Γ_2
```

`Γ'`: `E-LetTup`, like `E-App`, adds bindings for `x_1` through `x_n` to `σ`. We can mirror this by
picking `Γ'` to be `Γ, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n`.

`Ρ'`: `E-LetTup` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`.

`e'` is well-typed: We know from `T-LetTup` that `e_2`, our result, is well-typed with the changes
we made in `Γ'` (i.e. adding bindings for `x_1` through `x_n`).

##### Case `E-TApp`:

From premise:
```
------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [τ]) → (σ, R, e[τ / ς])
```

From premise and knowledge that `e` is of the form ``, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ τ_2 : κ
τ_2 ∈ { f } ⇒ τ_2 ≠ 0
---------------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ς] ⇒ Ρ'; Γ'
```

`Γ'`: `E-TApp` leaves `σ` unchanged, and so we can pick `Γ'` to be `Γ`.

`Ρ'`: `E-TApp` leaves `R` unchanged, and so we can pick `Ρ'` to be `Ρ`.

`e'` is well-typed: Since we left `Γ'` and `Ρ'` unchanged, we still know from our premise that our
result is well-typed.
