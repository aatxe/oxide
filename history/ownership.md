# Ownership Made Explicit

The goal here is to gradually build a core calculus for Rust that makes ownership explicit
syntactically through the use of fractional permissions (fractional linear capabilities). As far as
I can tell, there are two sensible ways of doing this.

Firstly, we can follow the tradition of Boyland and introduce a sort of substructural permissions
context that gets updated accordingly as the program executes (or while stepping through statements 
during type-checking). This results in typing rules that look like ordinary rules for typing
imperative programs (with each rule yielding an updated context).

The alternative is to follow more directly Linear Regions, L3, etc. and add a capability type that
is produced by stack and heap allocations and is tracked linearly in the context while variables of
other types are tracked unrestricted. This is a sort of specialization of λ^rgnUL in two ways: The
first is that we wish to strip out the U/L qualifiers and instead pre-determine that some types are
handled linearly and others are handled normally. The second is that we are in effect fixing the
size of all regions to one value. In the interest of expressing Rust as a flavor of ML, we follow
this approach here.

## Syntax

```
x ::= identifiers
S ::= struct names

α ::= traditional (kind ★) type variables
ζ ::= fractional (kind FRAC) type variables
ρ ::= memory location (kind RGN) type variables
ε ::= α | ζ | ρ

;; memory locations
ℓ ::= ρ
    | concrete memory locations (only appear at runtime)

;; Primitives
prims ::= new e
        | read e_1 e_2
        | write e_1 e_2 e_3
        | split e
        | join e_1 e_2

;; Expressions
e ::= prims
    | x
    | λx:τ. e 
    | e_1 e_2
    | ()
    | let () = e_1 in e_2
    | (e_1, ..., e_n)
    | let (x_1, ..., x_n) = e_1 in e_2
    | Λε:κ. e
    | e [τ]
    | pack(τ:κ, e)
    | let pack(ε:κ, x) = e_1 in e_2
    | S { x_1: e_1, ..., x_n: e_n }
    | S(e_1, ..., e_N)
    | S
    | e.n
    | e.x

;; Types
τ ::= ε
    | τ_1 → τ_2
    | Unit
    | 1
    | τ / 2
    | τ_1 × ... × τ_n
    | ∀ε:κ. τ
    | ref ℓ τ
    | cap ℓ τ
    | S
    
;; Kinds
κ ::= ★
    | RGN
    | FRAC

Γ ::= • | Γ,x:τ
Δ ::= • | Δ,ε:κ
Σ ::= •
    | Σ,struct S<α_1, ..., α_n> { x_1: τ_1, ..., x_n: τ_n }
    | Σ,struct S<α_1, ..., α_n>(τ_1, ..., τ_n)
    | Σ,struct S
```

## Static Semantics

Judgment: `Σ; Δ; Γ ⊢ e : τ`  
Meaning: In a structure context Σ, type context Δ, and value context Γ, expression e has type τ.

```
-------------------- T-Id
Σ; Δ; Γ,x:τ ⊢ x : τ

Σ; Δ; Γ,x:τ_x ⊢ e : τ
------------------------------ T-Abs
Σ; Δ; Γ ⊢ λx:τ_x. e : τ_x → τ

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Γ_1 ⊢ e_1 : τ_x → τ
Σ; Δ; Γ_2 ⊢ e_2 : τ_x
-------------------------- T-App
Σ; Δ; Γ ⊢ e_1 e_2 : τ

-------------------- T-Unit
Σ; Δ; Γ ⊢ () : Unit

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Γ_1 ⊢ e_1 : Unit
Σ; Δ; Γ_2 ⊢ e_2 : τ
---------------------------------- T-LetUnit
Σ; Δ; Γ ⊢ let () = e_1 in e_2 : τ

Δ ⊢ Γ_1 ⊡ ... ⊡ Γ_n ⇝ Γ
Σ; Δ; Γ_1 ⊢ e_1 : τ_1
...
Σ; Δ; Γ_n ⊢ e_n : τ_n
---------------------------------------------- T-Prod
Σ; Δ; Γ ⊢ (e_1, ..., e_n) : (τ_1 × ... × τ_n)

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Γ_1 ⊢ e_1 : (τ_1 × ... × τ_n)
Σ; Δ; Γ_2, x_1:τ_1, ..., x_n:τ_n ⊢ e_2 : τ
----------------------------------------------- T-LetProd
Σ; Δ; Γ ⊢ let (x_1, ..., x_n) = e_1 in e_2 : τ

Σ; Δ,ε:κ; Γ ⊢ e : τ
---------------------------- T-TAbs
Σ; Δ; Γ ⊢ Λε:κ. e : ∀ε:κ. τ

Σ; Δ; Γ ⊢ e_1 : ∀ε:κ. τ
Δ ⊢ τ_2 : κ
--------------------------------- T-TApp
Σ; Δ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ε]

Δ ⊢ τ_1 : κ
Σ; Δ; Γ ⊢ e_2 : τ[τ_1 / ε]
------------------------------------- T-Pack
Σ; Δ; Γ ⊢ pack(τ_1:κ, e_2) : ∃ε:κ. τ

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Σ; Δ; Γ_1 ⊢ e_1 : ∃ε:κ. τ
Σ; Δ,ε:κ; Τ_2,x:τ ⊢ e_2 : τ'
Δ ⊢ τ' : ★
-------------------------------------------- T-LetPack
Σ; Δ; Γ ⊢ let pack(ε:κ, x) = e_1 in e_2 : τ'

Σ; Δ; Γ ⊢ e : τ
Δ ⊢ τ : ★
---------------------------------------------- T-New
Σ; Δ; Γ ⊢ new e : ∃ρ:RGN. (ref ρ τ × cap ρ 1)

Σ; Δ; Γ ⊢ e_1 : cap ℓ τ_ƒ
Δ ⊢ ℓ : RGN
Δ ⊢ τ_ƒ: FRAC
Σ; Δ; Γ ⊢ e_2 : ref ℓ τ
--------------------------------------- T-Read
Σ; Δ; Γ ⊢ read e_1 e_2 : cap ℓ τ_ƒ × τ

Σ; Δ; Γ ⊢ e_1 : cap ℓ 1
Δ ⊢ ℓ : RGN
Σ; Δ; Γ ⊢ e_2 : ref ℓ τ
Σ; Δ; Γ ⊢ e_3 : τ
--------------------------------------------- T-Write
Σ; Δ; Γ ⊢ write e_1 e_2 e_3 : cap ℓ 1 × Unit

Σ; Δ; Γ ⊢ e : cap ℓ τ_ƒ
Δ ⊢ ℓ : RGN
Δ ⊢ τ_ƒ: FRAC
-------------------------------------------------------- T-Split
Σ; Δ; Γ ⊢ split e : (cap ℓ (τ_ƒ / 2) × cap ℓ (τ_ƒ / 2))

Σ; Δ; Γ ⊢ e_1 : cap ℓ (τ_ƒ / 2)
Δ ⊢ ℓ : RGN
Δ ⊢ τ_ƒ: FRAC
Σ; Δ; Γ ⊢ e_2 : cap ℓ (τ_ƒ / 2)
----------------------------------- T-Join
Σ; Δ; Γ ⊢ join e_1 e_2 : cap ℓ τ_ƒ

Σ; Δ; Γ ⊢ e_1 : τ_1
...
Σ; Δ; Γ ⊢ e_n : τ_n
Σ ⊢ S { x_1: τ_1, ..., x_n: τ_n }
------------------------------------------- T-StructRecord
Σ; Δ; Γ ⊢ S { x_1: e_1, ... x_n: e_n } : S

Σ; Δ; Γ ⊢ e : S
Σ; S ⊢ x : τ
------------------ T-ProjStructRecord
Σ; Δ; Γ ⊢ e.x : τ

Σ; Δ; Γ ⊢ e_1 : τ_1
...
Σ; Δ; Γ ⊢ e_n : τ_n
Σ ⊢ S(τ_1, ..., τ_n)
------------------------------- T-StructTuple
Σ; Δ; Γ ⊢ S(τ_1, ..., τ_n) : S

n ∈ ℕ
Σ; Δ; Γ ⊢ e : S
Σ; S ⊢ n : τ
------------------ T-ProjStructTuple
Σ; Δ; Γ ⊢ e.n : τ

Σ ⊢ S
---------------- T-StructUnit
Σ; Δ; Γ ⊢ S : S
```

Judgment: `Δ ⊢ τ : κ`  
Meaning: In a type context Δ, type τ has the kind κ.

```
---------------- K-Id
Δ, ε: κ ⊢ ε : κ

------------- K-Unit
Δ ⊢ Unit : ★

------------- K-WholeFrac
Δ ⊢ 1 : FRAC

Δ ⊢ τ : FRAC
----------------- K-HalfFrac
Δ ⊢ τ / 2 : FRAC

Δ ⊢ τ_1 : ★
Δ ⊢ τ_2 : ★
------------------ K-Fun
Δ ⊢ τ_1 → τ_2 : ★

Δ ⊢ τ_1 : ★
...
Δ ⊢ τ_n : ★
------------------------ K-Prod
Δ ⊢ τ_1 × ... × τ_n : ★

Δ,ε:κ ⊢ τ : ★
---------------- K-Univ
Δ ⊢ ∀ε:κ. τ : ★

Δ ⊢ ℓ : RGN
Δ ⊢ τ : FRAC
---------------- K-Ref
Δ ⊢ ref ℓ τ : ★

Δ ⊢ ℓ : RGN
Δ ⊢ τ : FRAC
---------------- K-Cap
Δ ⊢ cap ℓ τ : ★

;; n.b. we may wish to include Σ here and require S ∈ dom(Σ)
---------- K-Struct
Δ ⊢ S : ★
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

Judgment: `Σ; S ⊢ (n|x) : τ`  
Meaning: In a structure S within structure context Σ, the n-th projection or x field is of type τ.

```
------------------------------------------------------------------- T-StructXthProj
Σ, struct S { x_1: τ_1, ..., x_i: τ_i, ... x_n: τ_n }; S ⊢ x_i : τ

i ∈ ℕ
----------------------------------------------- T-StructIthProj
Σ, struct S(τ_1, ..., τ_i, ... τ_n); S ⊢ i : τ
```
