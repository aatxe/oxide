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
kinds κ ::= ★ | RGN

type variables ς ::= α -- by convention, of kind ★
                   | ϱ -- by convention, of kind RGN

region types r ::= ϱ -- region variables
                 | ρ -- concrete regions

primitives prim ::= true | false | n | ()
base types bt ::= bool | u32 | unit

types τ ::= ς
          | bt
          | &r μ τ -- μ-reference in region r at type τ
          | &r_1 μ_1 τ_1 ⊗ ... ⊗ &r_n μ_n τ_n → τ_ret -- ordinary closure
          | &r_1 μ_1 τ_1 ⊗ ... ⊗ &r_n μ_n τ_n ↝ τ_ret -- move closure
          | ∀ς: κ. τ
          | τ_1 ⊗ ... ⊗ τ_n
          | S

expressions e ::= prim
                | alloc e
                | borrow μ x.π -- Rust syntax: &μ x / &μ x.π
                | drop x
                | let μ x: τ = e_1 in e_2
                | |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                | move |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
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
                        | Ρ, ρ ↦ ƒ ⊗ { π ↦ ρ }
                        | Ρ, ρ ↦ ƒ ⊗ ε ↦ τ
                        | Ρ, ρ ↦ ƒ ⊗ ε ↦ ρ
```

## Static Semantics

...

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
                | R ∪ { ρ ↦ ƒ ⊗ { Π ↦ ρ }} 
                | R ∪ { ρ ↦ ƒ ⊗ ε ↦ sv }
                | R ∪ { ρ ↦ ƒ ⊗ ε ↦ ρ }
                
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
