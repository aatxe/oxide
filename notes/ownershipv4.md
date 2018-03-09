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
          | &r f^ι τ -- fraction f of τ-value in region r aliased from ι
          | &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n → τ_ret -- ordinary closure
          | &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ↝ τ_ret -- move closure
          | unit
          | τ_1 ⊗ ... ⊗ τ_n
          | ∀ς: κ. τ
          | S

expressions e ::= prim
                | x
                | alloc e
                | borrow μ x.π -- Rust syntax: &μ x / &μ x.π
                | drop x
                | let μ x: τ = e_1 in e_2
                | |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }
                | move |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }
                | e_1 e_2
                | ()
                | let () = e_1 in e_2
                | (e_1, ..., e_n)
                | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2
                | S { x_1: e_1, ..., x_n: e_n }
                | S(e_1, ..., e_n)
                | Λς: κ. e
                | e [τ]
                | e.Π

type environments Γ ::= • | Γ, x ↦ stk τ r f ι 
kind environments Δ ::= • | Δ, ς : κ
data environments Σ ::= •
                      | Σ, struct S<α_1, ..., α_n> { x_1: τ_1, ..., x_n: τ_n }
                      | Σ, struct S<α_1, ..., α_n>(τ_1, ..., τ_n)

region environments Ρ ::= • | Ρ, ρ : τ
```

Shorthand: `∀α. τ ≝ ∀α:★. τ` and `Λα. e ≝ Λα:★. e`
Shorthand: `&r f τ ≝ &r f^• τ`

## Static Semantics

### Type Checking

Judgment: `Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'`  
Meaning: In a data environment Σ, kind environment Δ, region environment Ρ and type environment Γ,
expression e has type τ and produces the updated environments Ρ' and Γ'.

```
------------------------------------------------------------- T-Id
Σ; Δ; Ρ; Γ, x ↦ stk τ r f ι ⊢ x : τ ⇒ Ρ; Γ, x ↦ stk τ r f ι

fresh ρ
Σ; Δ; Γ ⊢ e : τ
---------------------------------------------- T-Alloc
Σ; Δ; Ρ; Γ ⊢ alloc e : &ρ 1 τ • ⇒ Ρ, ρ : τ; Γ

Γ(x) = stk τ r f ι
f ≠ 0
f / 2 ↓ f_n
Σ; τ ⊢ π : τ_π
------------------------------------------------------------------- T-BorrowImm
Σ; Δ; Γ ⊢ borrow imm x.π : &r f_n^x τ_π ⇒ Γ, x ↦ stk τ r f_n ι

Γ(x) = stk τ r 1 ι
Σ; τ ⊢ π : τ_π
--------------------------------------------------------------- T-BorrowMut
Σ; Δ; Ρ; Γ ⊢ borrow mut x : &r 1^x τ_π ⇒ Ρ; Γ, x ↦ stk τ r 0 ι

Γ(x_s) = stk τ_s r f_s ι
f + f_s ↓ f_n
----------------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ stk τ r f x_s ⊢ drop x : unit ⇒ Ρ; Γ, x_s ↦ stk τ_s r f_n ι

---------------------------------------------------------- T-Free
Σ; Δ; Ρ, ρ : τ; Γ, x ↦ stk τ ρ 1 • ⊢ drop x : unit ⇒ Ρ; Γ

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1^ι_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x ↦ stk τ_1 r_1 f_1 ι_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
Γ_2(x) = stk τ_2 r_2 f_2 x_s
Γ_2(x_s) = stk τ_s r_2 f_s ι_s
f_2 + f_s ↓ f_n
-------------------------------------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2, x_s ↦ stk τ_s r_2 f_n ι_s

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1^ι_1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x ↦ stk τ_1 r_1 1 ι_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
Γ_2(x) = stk τ_2 r_2 0 x_s
Γ_2(x_s) = stk τ_s r_2 1 ι_s
------------------------------------------------------------------------------------ T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1 in e_2 : τ_2 ⇒ Ρ_2; Γ_2, x_s ↦ stk τ_s r_2 1 ι_s

Σ; Δ; Ρ; Γ, x_1 ↦ stk τ_1 r_1 f_1 ι_1,
            ...
            x_n ↦ stk τ_n r_n f_n ι_n
            ⊢ e : τ_ret ⇒ Ρ'; Γ'
-------------------------------------------------------------------- T-Closure
Σ; Δ; Ρ; Γ ⊢ |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }
           : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n → τ_ret
           ⇒ Ρ'; Γ'

Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Ρ; Γ_1, x_1 ↦ stk τ_1 r_1 f_1 ι_1,
              ...
              x_n ↦ stk τ_n r_n f_n ι_n
              ⊢ e : τ_ret ⇒ Ρ'; Γ_ignored
------------------------------------------------------------------------- T-MoveClosure
Σ; Δ; Ρ; Γ ⊢ move |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }
           : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ↝ τ_ret
           ⇒ Ρ'; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n → τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ⇒ Ρ_2; Γ_2
--------------------------------------------------------------------------------- T-App
Σ; Δ; Ρ; Γ ⊢ e_1 e_2 : τ_ret ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ⇝ τ_ret ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ⇒ Ρ_2; Γ_2
--------------------------------------------------------------------------------- T-MoveApp
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

Σ; Δ; Ρ; Γ ⊢ e_1 : τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : τ_n ⇒ Ρ_n; Γ_n
----------------------------------------------------------- T-Tup
Σ; Δ; Ρ; Γ ⊢ (e_1, ..., e_n) : τ_1 ⊗ ... ⊗ τ_n ⇒ Ρ_n; Γ_n

Σ; Δ; Ρ; Γ ⊢ e_1 : &r f^ι (τ_1 ⊗ ... ⊗ τ_n) ⇒ Ρ_1; Γ_1
f ≠ 0
f / n ↓ f_n
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ stk τ_1 r f_n ι,
                ...
                x_n ↦ stk τ_n r f_n ι,
                ⊢ e_2 : t_2 ⇒ Ρ_2; Γ_2
Γ_2(x_1) = stk τ_1_i r_1 f_1_i x_1_s     Γ_2(x_1_s) = stk τ_1_s r_1 f_1_s ι_1_s 
...                                      ...
Γ_2(x_n) = stk τ_n_i r_n f_n_i x_n_s     Γ_2(x_n_s) = stk τ_n_s r_n f_n_s ι_n_s
f_1_i + f_1_s ↓ f_1_t ... f_n_i + f_n_s ↓ f_n_t
---------------------------------------------------------------------------------------- T-LetTupImm
Σ; Δ; Ρ; Γ ⊢ let (imm x_1, ..., imm x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2 : τ_2
           ⇒ Ρ_2; Γ_2, x_1_s ↦ stk τ_1_s r_1 f_1_t ι_n_s, ..., x_n_s ↦ stk τ_n_s r_n f_n_t ι_n_s

mut ∈ {μ_1, ..., μ_n}
Σ; Δ; Ρ; Γ ⊢ e_1 : &r 1^ι (τ_1 ⊗ ... ⊗ τ_n) ⇒ Ρ_1; Γ_1
fresh r_1 ... r_n
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ stk τ_1 r_1 1 •,
                ...
                x_n ↦ stk τ_n r_n 1 •
                ⊢ e_2 : t_2 ⇒ Ρ_2; Γ_2
Γ_2(x_1) = stk τ_1_i r_1 1 x_1_s     Γ_2(x_1_s) = stk τ_1_s r_1 0 ι_1_s 
...                                  ...
Γ_2(x_n) = stk τ_n_i r_n 1 x_n_s     Γ_2(x_n_s) = stk τ_n_s r_n 0 ι_n_s
------------------------------------------------------------------------------------- T-LetTupAnyMut
Σ; Δ; Ρ; Γ ⊢ let (imm x_1, ..., imm x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2 : τ_2
           ⇒ Ρ_2; Γ_2, x_1_s ↦ stk τ_1_s r_1 1 ι_n_s, ..., x_n_s ↦ stk τ_n_s r_n 1 ι_n_s

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

Σ; Δ; Ρ; Γ ⊢ e : &r f^ι S ⇒ Ρ'; Γ'
struct S { x_1: τ_1, ..., x: τ, ..., x_n: τ_n } ∈ Σ
---------------------------------------------------- T-ProjFieldPath
Σ; Δ; Ρ; Γ ⊢ e.x : &r f^ι τ_t ⇒ Ρ'; Γ'

Σ; Δ; Ρ; Γ ⊢ e : &r f^ι S ⇒ Ρ'; Γ'
struct S(τ_1, ..., τ_t, ..., τ_n) ∈ Σ
-------------------------------------- T-ProjIndexPathStruct
Σ; Δ; Ρ; Γ ⊢ e.t : &r f^ι τ_t  ⇒ Ρ'; Γ'

Σ; Δ; Ρ; Γ ⊢ e : &r f^ι (τ_1 ⊗ ... ⊗ τ_t ⊗ ... ⊗ τ_n) ⇒ Ρ'; Γ'
----------------------------------------------------------------- T-ProjIndexPathTup
Σ; Δ; Ρ; Γ ⊢ e.t : &r f^ι τ_t ⇒ Ρ'; Γ'
```

### Additional Judgments

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

## Dynamic Semantics

### Syntax Extensions

```
expresions e ::= ...
               | ptr ρ.π ƒ x

simple values sv ::= true | false
                   | n
                   | ptr ρ.π ƒ x
                   | ()

values v ::= sv
           | (v_1, ... v_n)
           | S { x_1: v_1, ... x_n: v_n }
           | S(v_1, ..., v_n)
           | |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }
           | move |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }

evaluation contexts E ::= []
                        | alloc E
                        | let μ x: τ = E in e
                        | E e
                        | v E
                        | let () = E in e
                        | (v ..., E, e ...)
                        | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = E in e
                        | S { x: v ..., x: E, x: e ... }
                        | S(v ..., E, e ...)
                        | E [τ]
                        | E.Π

regions ρ are maps from paths π to simple values sv.
region sets R map region names to regions.
stores σ are maps from identifiers x to pointers ptr ρ.π ƒ x
```

### Typing Extensions

```
--------------------------------------------------- T-Ptr
Σ; Δ; Ρ, ρ : τ; Γ ⊢ ptr ρ.π ƒ x : &ρ ƒ^x τ ⇒ Ρ; Γ
```

### Operational Semantics

Form: `(σ, R, e) → (σ, R, e)`

```
σ(x) = ptr ρ.π ƒ x_s
ƒ ≠ 0
canonize(π) = π_c
R(ρ)(π_c) = sv
----------------------- E-Id
(σ, R, x) → (σ, R, sv)

fresh ρ
------------------------------------------------------------ E-AllocSimple
(σ, R, alloc sv) → (σ, R ∪ { ρ ↦ { ε ↦ sv } }, ptr ρ.ε 1 •)

;; TODO: alloc for tuples and structs
;; general idea: recursively convert subvalues to sets of path-sv pairs and union them all together

σ(x) = ptr ρ.π_x ƒ x_s
ƒ ≠ 0
canonize(π_x.π) = π_c
π_c ∈ R(ρ)
ƒ / 2 ↓ ƒ_n
--------------------------------------------------------------------------- E-BorrowImm
(σ, R, borrow imm x.π) → (σ ∪ { x ↦ ptr ρ.π_x ƒ_n x_s, R, ptr ρ.π_c ƒ_n x)

σ(x) = ptr ρ.π_x 1 x_s
canonize(π_x.π) = π_c
π_c ∈ R(ρ)
----------------------------------------------------------------------- E-BorrowMut
(σ, R, borrow mut x.π) → (σ ∪ { x ↦ ptr ρ.π_x 0 x_s, R, ptr ρ.π_c 1 x)

σ(x) = ptr ρ.π ƒ x_s
σ(x_s) = ptr ρ.π_s ƒ_s x_ss
ƒ + ƒ_s ↓ ƒ_n
--------------------------------------------------------------- E-Drop
(σ, R, drop x) ↦ (σ ∪ { x_s ↦ ptr ρ.π_s ƒ_n x_ss } / x, R, ())

σ(x) = ptr ρ.π 1 •
------------------------------------ E-Free
(σ, R, drop x) ↦ (σ / x, R / ρ, ())

μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ.π ƒ x_s in e) → (σ ∪ { x ↦ ptr ρ.π ƒ x_s }, R, e)

-------------------------------------------------------------------------------------- E-App
(σ, R, (|x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }) (v_1, ..., v_n)) →
(σ ∪ { x_1 ↦ v_1, ..., x_n ↦ v_n }, R, e)

------------------------------------------------------------------------------------------ E-MoveApp
(σ, R, (move |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }) (v_1, ..., v_n)) →
(σ ∪ { x_1 ↦ v_1, ..., x_n ↦ v_n }, R, e)

------------------------------------- E-LetUnit
(σ, R, let () = () in e) → (σ, R, e)

mut ∈ { μ_1, ..., μ_n } ⇒ ƒ_1 = 1 ∧ ... ∧ ƒ_n = 1
ƒ_1 ≠ 0 ∧ ... ∧ ƒ_n ≠ 0
------------------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = (v_1, ..., v_n) in e) →
(σ ∪ { x_1 ↦ v_1, ..., x_n ↦ v_n }, R, e)

------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [τ]) → (σ, R, e[τ / ς])

---------------------------------------------------- E-ProjImmPath
(σ, R, (ptr ρ.π ƒ x_s).Π) → (σ, R, ptr ρ.π.Π ƒ x_s)
```

## Proof of Soundness

### Progress

**Lemma** (Canonical Forms):
  1. if `v` is a value of type `bool`, then `v` is either `true` or `false`.
  2. if `v` is a value of type `u32`, then `v` is a numeric value on the range `[0, 2^32)`.
  3. if `v` is a value of type `unit`, then `v` is `()`.
  4. if `v` is a value of type `&ρ ƒ^x τ`, then `v` is of the form `ptr ρ.π ƒ x`.
  5. if `v` is a value of type `&r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n → τ_ret`, then `v` is of
     the form `|x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }`.
  6. if `v` is a value of type `&r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ↝ τ_ret`, then `v` is of
     the form `move |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }`.

**Theorem**:
`∀Ρ, Γ. ∃Σ, σ, R. (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Γ) ∧ (Ρ ⊢ R) ∧ (Γ ⊢ σ)
                   ⇒ (e ∈ v) ∨ (∃σ', R', e'. (σ, R, e) → (σ', R', e'))`

I think we need to somehow bound `Σ` here or something.

#### Proof.

By induction on a derivation of `e : τ`.

The `T-True`, `T-False`, `T-Unit`, `T-u32`, `T-Ptr`, `T-Closure`, and `T-MvClosure` cases are all
immediate since `e` is in all these cases a value. The other cases follow.

Case `T-Id`: `e = x`. From premise, we know `Γ ⊢ σ` and thus, if `x : τ`, `x ∈ σ`. Thus, we can
take a step via `E-Id`.

Case `T-Alloc`: `e = alloc e'`. By IH, either `e ∈ v` or we can take a step. In the former case,
since `e ∈ v`, we can apply `E-Alloc` to step. In the latter case, we can step `e'` to step e to
`alloc e''`. ;; TODO: fix `E-Alloc`

Case `T-BorrowImm`: `e = borrow imm x.π`. From premise, we know `Γ ⊢ σ` and `Ρ ⊢ R`. Thus, we know
if `x : τ`, `x ∈ σ`. Looking up `x`, we get `σ(x) = ptr ρ.π_x ƒ x_s`. With this info and `P ⊢ R`
from our premise, we know that the `canonize(π_x.π) ∈ R(ρ)` and so we can use `E-BorrowImm` to step
forward.

Case `T-BorrowMut`: `e = borrow mut x.π`. From premise, we know `Γ ⊢ σ` and `Ρ ⊢ R`. Thus, we know
if `x : τ`, `x ∈ σ`. Looking up `x`, we get `σ(x) = ptr ρ.π_x 1 x_s`. With this info and `P ⊢ R`
from our premise, we know that the `canonize(π_x.π) ∈ R(ρ)` and so we can use `E-BorrowMut` to step
forward.

Case `T-Drop`: `e = drop x`. From premise, we know `Γ ⊢ σ` and can thus conclude `x ∈ σ`. Looking up
`x`, we get `σ(x) = ptr ρ.π ƒ x_s` and we can apply `E-Drop` to take a step.

Case `T-Free`: `e = drop x`. From premise, we know `Γ ⊢ σ` and can thus conclude `x ∈ σ`. Looking up
`x`, we get `σ(x) = ptr ρ.π 1 •` (subject to constraints of `T-Free`) and can apply `E-Free` to take
a step.

Case `T-LetImm`: `e = let imm x: τ = e_1 in e_2`. By IH, either `e_1 ∈ v` or we can take a step. In
the former case, `e_1 ∈ v` and of type `&ρ ƒ^x τ` from case, by Canonical Forms, `e_1` is of the
form `ptr ρ.π ƒ x`. Thus, we can use `E-Let` to step.

Case `T-LetMut`: `e = let mut x: τ = e_1 in e_2`. By IH, either `e_1 ∈ v` or we can take a step. In
the former case, `e_1 ∈ v` and of type `&ρ ƒ^x τ` from case, by Canonical Forms, `e_1` is of the
form `ptr ρ.π ƒ x`. Thus, we can use `E-Let` to step.

Case `T-App`: `e = e_1 e_2`. By IH, either `e_1 ∈ v` and `e_2 ∈ v` or we can take a step. In the
former case, we know `e_1 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n → τ_ret` and
`e_2 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n`, then by Canonical Forms `e_1` is of the form
`|x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }` and `e_2` is of the form 
`(ptr r_1.π_1 f_1 ι_1, ..., ptr r_n.π_n f_n ι_n)`. So, we can step using `E-App`.

Case `T-MoveApp`: `e = e_1 e_2`. By IH, either `e_1 ∈ v` and `e_2 ∈ v` or we can take a step. In the
former case, we know `e_1 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n ↝ τ_ret` and
`e_2 : &r_1 f_1^ι_1 τ_1 ⊗ ... ⊗ &r_n f_n^ι_n τ_n`, then by Canonical Forms `e_1` is of the form
`move |x_1: &r_1 f_1^ι_1 τ_1, ..., x_n: &r_n f_n^ι_n τ_n| { e }` and `e_2` is of the form 
`(ptr r_1.π_1 f_1 ι_1, ..., ptr r_n.π_n f_n ι_n)`. So, we can step using `E-MoveApp`.

Case `T-LetUnit`: `e = let () = e_1 in e_2`. By IH, either `e_1 ∈ v` or we can take a step. In the
former case, we know `e_1 : unit` and thus by Canonical Forms `e_1` is `()`. Thus, we can step using
`E-LetUnit`.

Case `T-LetTupImm`: `e = let (imm x_1, ..., imm x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2`. By IH, either
`e_1 ∈ v` or we can take a step. In the former case, we know `e_1 : τ_1 ⊗ ... ⊗ τ_n` and thus by
Canonical forms, `e_1` is of the form `(v_1, ..., v_n)`. Thus, we can step using `E-LetTup`.

Case `T-LetMutAnyMut`: `e = let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1 in e_2`. By IH,
either `e_1 ∈ v` or we can take a step. In the former case, we know `e_1 : τ_1 ⊗ ... ⊗ τ_n` and thus
by Canonical forms, `e_1` is of the form `(v_1, ..., v_n)`. Thus, we can step using `E-LetTup`.
