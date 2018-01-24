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

α ::= traditional (kind ★) type variables
ζ ::= fractional (kind FRAC) type variables
ρ ::= memory location (kind RGN) type variables
ε ::= α | ζ | ρ

;; memory locations
ℓ ::= ρ
    | concrete memory locations (only appear at runtime)

;; Primitives
prims ::= new | read | write | split | join

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
    
;; Types
τ ::= α
    | τ_1 → τ_2
    | 1
    | τ / 2
    | τ_1 × ... × τ_n
    | ∀ε:κ. τ
    | ref ℓ τ
    | cap ℓ τ
    
;; Kinds
κ ::= ★
    | RGN
    | FRAC

Γ ::= • | Γ,x:τ
Δ ::= • | Δ,ε:κ
```

## Static Semantics

```
----------------- T-Id
Δ; Γ,x:τ ⊢ x : τ

Δ; Γ,x:τ_x ⊢ e : τ
--------------------------- T-Abs
Δ; Γ ⊢ λx:τ_x. e : τ_x → τ

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Δ; Γ_1 ⊢ e_1 : τ_x → τ
Δ; Γ_2 ⊢ e_2 : τ_x
----------------------- T-App
Δ; Γ ⊢ e_1 e_2 : τ

----------------- T-Unit
Δ; Γ ⊢ () : 1

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Δ; Γ_1 ⊢ e_1 : 1
Δ; Γ_2 ⊢ e_2 : τ
------------------------------- T-LetUnit
Δ; Γ ⊢ let () = e_1 in e_2 : τ

Δ ⊢ Γ_1 ⊡ ... ⊡ Γ_n ⇝ Γ
Δ; Γ_1 ⊢ e_1 : τ_1
...
Δ; Γ_n ⊢ e_n : τ_n
------------------------------------------- T-Prod
Δ; Γ ⊢ (e_1, ..., e_n) : (τ_1 × ... × τ_n)

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Δ; Γ_1 ⊢ e_1 : (τ_1 × ... × τ_n)
Δ; Γ_2, x_1:τ_1, ..., x_n:τ_n ⊢ e_2 : τ
-------------------------------------------- T-LetProd
Δ; Γ ⊢ let (x_1, ..., x_n) = e_1 in e_2 : τ

Δ,ε:κ; Γ ⊢ e : τ
------------------------- T-TAbs
Δ; Γ ⊢ Λε:κ. e : ∀ε:κ. τ

Δ; Γ ⊢ e_1 : ∀ε:κ. τ
Δ ⊢ τ_2 : κ
------------------------------ T-TApp
Δ; Γ ⊢ e_1 [τ_2] : τ[τ_2 / ε]

Δ ⊢ τ_1 : κ
Δ; Γ ⊢ e_2 : τ[τ_1 / ε]
---------------------------------- T-Pack
Δ; Γ ⊢ pack(τ_1:κ, e_2) : ∃ε:κ. τ

Δ ⊢ Γ_1 ⊡ Γ_2 ⇝ Γ
Δ; Γ_1 ⊢ e_1 : ∃ε:κ. τ
Δ,ε:κ; Τ_2,x:τ ⊢ e_2 : τ'
Δ ⊢ τ' : ★
----------------------------------------- T-LetPack
Δ; Γ ⊢ let pack(ε:κ, x) = e_1 in e_2 : τ'

--------------------------------------------------- T-New
Δ; Γ ⊢ new : ∀α:★. α → ∃ρ:LOC. (ref ρ α × cap ρ 1)

------------------------------------------------------------------------- T-Read
Δ; Γ ⊢ read : ∀α:★. ∀ρ:LOC. ∀ζ:FRAC. (cap ρ ζ × ref ρ α) → (cap ρ ζ × α)

--------------------------------------------------------------- T-Write
Δ; Γ ⊢ write : ∀α:★. ∀ρ:LOC. (cap ρ 1 × ref ρ α × α) → cap ρ 1

-------------------------------------------------------------------------- T-Split
Δ; Γ ⊢ split : ∀ρ:LOC. ∀ζ:FRAC. cap ρ ζ → (cap ρ (ζ / 2) × cap ρ (ζ / 2))

------------------------------------------------------------------------- T-Join
Δ; Γ ⊢ join : ∀ρ:LOC. ∀ζ:FRAC. (cap ρ (ζ / 2) × cap ρ (ζ / 2)) → cap ρ ζ
```
