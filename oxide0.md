# Oxide0 - Formal Rust0

## Table of Contents

- [Summary](#summary)
  - [Bindings and borrowing](#bindings-and-borrowing)
- [Syntax](#syntax)
  - [Syntax extensions for runtime](#syntax-extensions)
  - [Syntactic Sugar](#syntactic-sugar)
- [Type System](#static-semantics)
  - [Main inference rules](#inference-rules)
  - [Invariants](#invariants)
  - [Typing extensions for runtime](#typing-extensions)
  - [Minor judgments](#additional-judgments)
- [Operational Semantics](#dynamic-semantics)
- [Proof of Soundness](#proof-of-soundness)
  - [Progress](#progress)
  - [Preservation](#preservation)
- [Extensions to make oxide0 less minimal](#a-less-minimal-oxide0)

## Summary

In `oxide`, we allocate every value on a region in the stack, associating it with a fractional
capability guarding its use. The fractional aspect of this capability allows us to model mutable vs
immutable borrows by tracking the existence of aliases. That is, if a capability is `1`, we know
that there are no aliases and a mutable borrow is safe. Aggregate structures (like tuples and
structs) reference other smaller regions (each of which has its own capability). Perhaps notably, we
simplify the move-vs-borrow distinction by treating all moves as mutable borrows — a natural
consequence of our fractional capabilities.

To keep the style of programming close to real Rust, capabilities are always packaged inside of our
reference type (`&r f τ`). Consequently, every type is always used under references. I think of this
as making their existence somewhere on the stack explicit in some sense. The major differences
syntactically from Rust are the placement of `alloc` expressions around values (which represent
allocation on the **stack**), and the use of the word `borrow` instead of `&` in the expression form
of borrowing.

You can find examples of Rust0 code and its corresponding `oxide0` form [here](examples/level0.md).

### Bindings and borrowing

As noted above, all values are used under references. This can be seen by looking at the typing
rules for bindings: each binding expects to find a reference to a value at the right type. This is
what enables/requires us to use `alloc` and `borrow` expressions, as these operations are the only
ones that yield a reference at some type `τ`.

[˄ Back to top][toc]

## Syntax

```
identifiers x, y
• is a special empty identifier
struct names S
enum variants E
region names ρ

naturals n ∈ ℕ
concrete fractions ƒ ::= n | ƒ / ƒ | ƒ + ƒ
immediate path Π ::= x | n | [n]
paths π ::= ε | Π.π ;; π is (Π.)*ε

enum variants ev ::= E(τ_1, ..., τ_n)
                   | E { x_1: τ_1, ..., x_n: τ_n }

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

all-kind types χ ::= ς
                   | τ
                   | ρ
                   | ƒ
                   | rgn of x.π
                   | cap of x.π

★-kind types τ ::= α
                 | bt
                 | &r f τ                                  -- μ-reference in region r at type τ
                 | &r_1 f τ_1 ⊗ ... ⊗ &r_n f τ_n → τ_ret  -- ordinary closure
                 | &r_1 f τ_1 ⊗ ... ⊗ &r_n f τ_n ↝ τ_ret  -- move closure
                 | ∀ς: κ. τ
                 | [τ; n]  -- fixed-sized arrays
                 | [τ]     -- slices
                 | τ_1 ⊗ ... ⊗ τ_n
                 | S<χ_1, ..., χ_n>

expressions e ::= prim
                | alloc e
                | copy x
                | borrow μ x.π         -- Rust syntax: &μ x / &μ x.π
                | slice μ x.π e_1 e_2  -- Rust syntax: &x.π[e_1..e_2]
                | drop x
                | let μ x: τ = e_1; e_2
                | x.π := e
                | |x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }
                | move |x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }
                | e_1 e_2
                | e_1; e_2
                | if e_1 { e_2 } else { e_3 }
                | for μ x in e_1 { e_2 }
                | (e_1, ..., e_n)
                | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1; e_2
                | [e_1, ..., e_n]
                | S::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
                | S::<χ_1, ..., χ_n>(e_1, ..., e_n)
                | S::ev::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
                | S::ev::<χ_1, ..., χ_n>(e_1, ..., e_n)
                | Λς: κ. e
                | e [χ]

type environments Γ ::= • | Γ, x ↦ r
kind environments Δ ::= • | Δ, ς : κ

data environments Σ ::= •
                      | Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }
                      | Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n)
                      | Σ, enum S<ς_1 : κ_1, ..., ς_n : κ_n> { ev_1, ..., ev_n }

region environments Ρ ::= •
                        | Ρ, r ↦ τ ⊗ f ⊗ { Π ↦ r, ... }
                        | Ρ, r ↦ τ ⊗ f ⊗ { <tag> ↦ ev, Π ↦ r, ... }
                        | Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ τ }
                        | Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ r }
```

[˄ Back to top][toc]

## Syntactic Sugar

For each of the following examples of syntactic sugar, the left-hand side is the desugared form, and
the right-hand side is the sugar. The sugar exists largely to make code easier to read, but also to
bridge the gap between oxide core syntax and Rust.

```
x.ε             ↔  x
x.(Π.)*Π.ε      ↔  x.(Π.)*Π
e_1 (e_2, ...)  ↔  e_1(e_2, ...)
Λα: ★. e        ↔  Λα. e
Λϱ: RGN. e      ↔  Λϱ. e
Λζ: FRAC. e     ↔  Λζ. e
{ e }           ↔  e;
S<>             ↔  S

S::<> { x_1: e_1, ..., x_n: e_n }        ↔  S { x_1: e_1, ..., x_n: e_n }
S::<>(e_1, ..., e_n)                     ↔  S(e_1, ..., e_n)
if e { ... } else { if e' { ... } ... }  ↔  if { ... } else if e' { ... } ...
if e { ... } else { () }                 ↔  if e { ... }
```

[˄ Back to top][toc]

## Static Semantics

Judgment: `Σ; Δ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'`  
Meaning: In a data environment `Σ`, kind environment `Δ`, region environment `Ρ` and type
environment `Γ`, expression `e` has type `τ` and produces the updated environments `Ρ'` and `Γ'`.

### Invariants

```
Σ; Δ ⊢ Ρ
Σ; Δ; Ρ ⊢ Γ
Σ; Δ; Ρ ⊢ τ : ★
⊢ Σ
```

### Inference Rules

```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ prim : τ ⇒ Ρ; Γ
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
Σ; Δ; Ρ_n; Γ_n ⊢ S::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
--------------------------------------------------------------------------- T-AllocStructTup
Σ; Δ; Ρ; Γ ⊢ alloc S::<χ_1, ..., χ_n>(e_1, ..., e_n)
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S<χ_1, ..., χ_n> ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }
-------------------------------------------------------------------------------- T-AllocStructRecord
Σ; Δ; Ρ; Γ ⊢ alloc S::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S::<χ_1, ..., χ_n> ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ; Δ; Ρ_n; Γ_n ⊢ S::E::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
------------------------------------------------------------------------------------- T-AllocEnumTup
Σ; Δ; Ρ; Γ ⊢ alloc S::E::<χ_1, ..., χ_n>(e_1, ..., e_n)
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S<χ_1, ..., χ_n> ⊗ 1 ⊗ { <tag> ↦ E, 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S::E::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }
---------------------------------------------------------------------------------- T-AllocEnumRecord
Σ; Δ; Ρ; Γ ⊢ alloc S::E::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S::<χ_1, ..., χ_n> ⊗ 1 ⊗ { <tag> ↦ E, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n

fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ ⇒ Ρ_n; Γ_n
--------------------------------------------------------------------------- T-AllocArray
Σ; Δ; Ρ; Γ ⊢ alloc [e_1, ..., e_n] : &ρ 1 [τ; n]
           ⇒ Ρ_n, ρ ↦ [τ; n] ⊗ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n }; Γ_n

Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ f_π ⊗ π_path_set
f_π ≠ 0
τ_π ~ bt
fresh ρ
------------------------------------------------------ T-Copy
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ copy x.π : &ρ 1 τ_π
                    ⇒ Ρ, ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ τ_π };
                      Γ, x ↦ r_x

Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ f_π ⊗ π_path_set
Ρ ⊢ imm r_π
f_π / 2 ↓ f_n
fresh ρ
-------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow imm x.π : &ρ f_n τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ f_n ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ f_n ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
                                              
Ρ ⊢ mut π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Ρ ⊢ mut r_π
fresh ρ
------------------------------------------------------ T-BorrowMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow mut x.π : &ρ 1 τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ 0 ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x

Ρ ⊢ imm π in r_x : [τ_e; n] ⇒ r_π
Ρ(r_π) = [τ_e; n] ⊗ f_π ⊗ π_path_set
f_π / 2 ↓ f_n
fresh ρ
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Γ_2
-------------------------------------------------------------- T-SliceImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ slice imm x.π e_1 e_2 : &ρ [τ]
                    ⇒ Ρ_2, r_π ↦ [τ_e; n] ⊗ f_n ⊗ π_path_set,
                           ρ ↦ [τ_e] ⊗ f_n ⊗ { ε ↦ r_π };
                      Γ_2, x ↦ r_x

Ρ ⊢ mut π in r_x : [τ_e; n] ⇒ r_π
Ρ(r_π) = [τ_e; n] ⊗ 1 ⊗ π_path_set
fresh ρ
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Γ_2
------------------------------------------------------------- T-SliceMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ slice mut x.π e_1 e_2 : &ρ [τ]
                    ⇒ Ρ_2, r_π ↦ [τ_e; n] ⊗ 0 ⊗ π_path_set,
                           ρ ↦ [τ_e] ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ_2, x ↦ r_x

Ρ(r_x) = τ_x ⊗ f_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ f_r ⊗ path_set
f_r + f_x ↓ f_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ f_n ⊗ path_set; Γ

Ρ(r_x) = τ ⊗ 1 ⊗ { ε ↦ τ }
Ρ' = Ρ - r_x
--------------------------------------------- T-FreeImmediate
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ

Ρ(r_x) = τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }
r_1 ∉ dom(Ρ) ... r_n ∉ dom(Ρ) ;; i.e. all the referenced regions have already been dropped
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------- T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ

===================================================================================================

--------------------------------- T-True
Σ; Δ; Ρ; Γ ⊢ true : bool ⇒ Ρ; Γ

--------------------------------- T-False
Σ; Δ; Ρ; Γ ⊢ false : bool ⇒ Ρ; Γ

n ∈ [0, 2^32)
------------------------------ T-u32
Σ; Δ; Ρ; Γ ⊢ n : u32 ⇒ Ρ; Γ

------------------------------- T-Unit
Σ; Δ; Ρ; Γ ⊢ () : unit ⇒ Ρ; Γ

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2

Ρ ⊢ mut (Π.)*ε in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Ρ ⊢ mut r_π
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : &r_n 1 τ_π ⇒ Ρ'; Γ'
π_path_set ∪ { Π ↦ r_n } = new_path_set
--------------------------------------------------------- T-Assign
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.(Π.)*Π.ε := e
                    : unit
                    ⇒ Ρ', r_π ↦ τ_n ⊗ 1 ⊗ new_path_set;
                      Γ'

Ρ ⊢ mut r_x
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : &r_n 1 τ_π ⇒ Ρ'; Γ'
--------------------------------------------------------- T-AssignEpsilon
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.ε := e : unit ⇒ Ρ'; Γ', x ↦ r_n

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
---------------------------------------- T-Seq
Σ; Δ; Ρ; Γ ⊢ e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 bool ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ ⇒ Ρ_2; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_3 : τ ⇒ Ρ_3; Γ_1
;; FIXME: we need to somehow unify Ρ_2 and Ρ_3
;; in particular, τ is not necessarily identical in e_2
;; and e_2, but we should be able to join ρ's in each
-------------------------------------------------------- T-If
Σ; Δ; Ρ; Γ ⊢ if e_1 { e_2 } else { e_3 } : τ ⇒ Ρ'; Γ_1

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ imm r_1    f_1 ≠ 0
Ρ(r_1) = τ_1 ⊗ f_1 ⊗ path_set_1
fresh ρ
f_1 / 2 ↓ f_n
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ f_n ⊗ path_set_1, ρ ↦ τ ⊗ f_n ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
--------------------------------------------------------------------- T-ForImm
Σ; Δ; Ρ; Γ ⊢ for imm x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ mut r_1
Ρ(r_1) = τ_1 ⊗ 1 ⊗ path_set_1
fresh ρ
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ 0 ⊗ path_set_1, ρ ↦ τ ⊗ 1 ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
----------------------------------------------------------------- T-ForMut
Σ; Δ; Ρ; Γ ⊢ for mut x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1

Σ; Δ; Ρ; Γ ⊢ e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n) ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ r_1, ... x_n ↦ r_n ⊢ e_2 : t_r ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2) ... r_n ∉ dom(Ρ_2)
----------------------------------------------------------------------- T-LetTup
Σ; Δ; Ρ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1; e_2
           : τ_r ⇒ Ρ_2; Γ_2

Σ; Δ, ς : κ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ'
-------------------------------------------- T-TAbs
Σ; Δ; Ρ; Γ ⊢ Λς: κ. e : ∀ς : κ. τ ⇒ Ρ'; Γ'

Σ; Δ; Ρ; Γ ⊢ e : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ χ : κ
χ ~ f ⇒ χ ≠ 0
---------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e [χ] : τ[χ / ς] ⇒ Ρ'; Γ'
```

[˄ Back to top][toc]

### Additional Judgments

#### `Ρ ⊢ μ π in r : τ_π ⇒ r_π`
Meaning: In a region environment `Ρ` with constraints for `μ` borrows, path `π` in `r` has the type
`τ_π` in the region `r_π`.

```
μ = imm ⇒ f ≠ 0   μ = mut ⇒ f = 1
-------------------------------------------- P-EpsilonPath
Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ τ } ⊢ μ ε in r : τ ⇒ r

μ = imm ⇒ f ≠ 0   μ = mut ⇒ f = 1
Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ r_s } ⊢ μ π in r_s : τ ⇒ r_π
--------------------------------------------------- P-AliasPath
Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ r_s } ⊢ μ π in r : τ ⇒ r_π

μ = imm ⇒ f ≠ 0   μ = mut ⇒ f = 1
Ρ, r ↦ τ ⊗ f ⊗ { Π_1 ↦ r_1, ..., Π ↦ r_Π, ..., Π_n ↦ r_n } ⊢ μ π in r_Π : τ_π ⇒ r_π
-------------------------------------------------------------------------------------- P-FieldPath
Ρ, r ↦ τ ⊗ f ⊗ { Π_1 ↦ r_1, ..., Π ↦ r_Π, ..., Π_n ↦ r_n } ⊢ μ Π.π in r : τ_π ⇒ r_π
```

#### `Ρ ⊢ μ r`
Meaning: In a region enviroment `Ρ`, region `r` is well-formed for a `μ` borrow. That is, for an
immutable borrow, all of the subpaths of `r` are non-zero, and for a mutable borrow, all of the
subpaths of `r` are `1`.

```
f ≠ 0
----------------------------------- WF-ImmEpsilonRegion
Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ τ } ⊢ imm r

----------------------------------- WF-MutEpsilonRegion
Ρ, r ↦ τ ⊗ 1 ⊗ { ε ↦ τ } ⊢ mut r

f ≠ 0
Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ r_s } ⊢ imm r_s
--------------------------------------- WF-ImmAliasRegion
Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ r_s } ⊢ imm r

Ρ, r ↦ τ ⊗ 1 ⊗ { ε ↦ r_s } ⊢ mut r_s
-------------------------------------- WF-MutAliasRegion
Ρ, r ↦ τ ⊗ 1 ⊗ { ε ↦ r_s } ⊢ mut r

f ≠ 0
Ρ, r ↦ τ ⊗ f ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n } ⊢ imm r_1
...
Ρ, r ↦ τ ⊗ f ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n } ⊢ imm r_n
--------------------------------------------------------- WF-ImmAliasRegion
Ρ, r ↦ τ ⊗ f ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n } ⊢ imm r

Ρ, r ↦ τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n } ⊢ mut r_1
...
Ρ, r ↦ τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n } ⊢ mut r_n
--------------------------------------------------------- WF-MutAliasRegion
Ρ, r ↦ τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n } ⊢ mut r
```

#### `Σ; Δ; Ρ; Γ ⊢ Sτ`
Meaning: In a data structure context `Σ`, kind environment `Δ`, region environment `Ρ`, and type
environment `Γ`, the long-form named data type `Sτ` is well-formed.

```
;; grammar "extensions"
Sτ ::= S::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
     | S::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }

;; judgment rules

⊢ Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }; Δ; Ρ; Γ
  ⊢ χ_1 : κ_1
...
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }; Δ; Ρ; Γ
  ⊢ χ_n : κ_n
---------------------------------------------------------------------------- WF-StructTuple
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }; Δ; Ρ; Γ
  ⊢ S::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }

⊢ Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n)
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n); Δ; Ρ; Γ
  ⊢ χ_1 : κ_1
...
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n); Δ; Ρ; Γ
  ⊢ χ_n : κ_n
---------------------------------------------------------------- WF-StructTuple
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n); Δ; Ρ; Γ
  ⊢ S::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
```

#### `Σ; Δ ⊢ Ρ`
Meaning: In a data structure context `Σ` and kind environment `Δ`, the region environment `Ρ` is
well-formed.

```
--------- WF-EmptyRegionEnv
Σ; Δ ⊢ •

Σ; Δ ⊢ Ρ
Σ; Δ; Ρ; • ⊢ τ : ★
Σ; Δ; Ρ; • ⊢ f : FRAC
Σ ⊢ Π_1 in τ             ...             Σ ⊢ Π_n in τ
Σ; Δ; Ρ; • ⊢ r_1 : RGN   ...   Σ; Δ; Ρ; • ⊢ r_n : RGN
------------------------------------------------------- WF-NestedRegion
Σ; Δ ⊢ Ρ, r ↦ τ ⊗ f ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }

Σ; Δ ⊢ Ρ
Σ; Δ; Ρ; • ⊢ τ : ★
Σ; Δ; Ρ; • ⊢ f : FRAC
--------------------------------- WF-ImmediateRegion
Σ; Δ ⊢ Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ τ }

Σ; Δ ⊢ Ρ
Σ; Δ; Ρ; • ⊢ τ : ★
Σ; Δ; Ρ; • ⊢ f : FRAC
Σ; Δ; Ρ; • ⊢ ρ : RGN
--------------------------------- WF-AliasRegion
Σ; Δ ⊢ Ρ, r ↦ τ ⊗ f ⊗ { ε ↦ ρ }
```

#### `Σ; Δ; Ρ ⊢ Γ`
Meaning: In a data structure context `Σ`, kind environment `Δ`, and region environment `Ρ`, the type
environment `Γ` is well-formed.

```
------------ WF-EmptyTypeEnv
Σ; Δ; Ρ ⊢ •

Σ; Δ; Ρ ⊢ Γ
Σ; Δ; Ρ; Γ ⊢ r : RGN
---------------------- WF-IdentifierBound
Σ; Δ; Ρ ⊢ Γ, x ↦ r
```

#### `Σ; Δ; Ρ; Γ ⊢ χ : κ`
Meaning: In a data structure context `Σ`, kind environment `Δ`, region environment `Ρ`, and type
environment `Γ`, the generalized type `χ` has the kind `κ`.

```
--------------------------- K-TVar
Σ; Δ, ς : κ; Ρ; Γ ⊢ ς : κ

ρ ∈ dom(Ρ)
---------------------- K-ConcreteRegion
Σ; Δ; Ρ; Γ ⊢ ρ : RGN

---------------------- K-ConcreteFraction
Σ; Δ; Ρ; Γ ⊢ ƒ : FRAC

Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
---------------------------------------- K-RgnOf
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ rgn of x.π : RGN

Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
----------------------------------------- K-CapOf
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ cap of x.π : FRAC

--------------------- K-BaseType
Σ; Δ; Ρ; Γ ⊢ bt : ★

Σ; Δ; Ρ; Γ ⊢ r : RGN
Σ; Δ; Ρ; Γ ⊢ f : FRAC
-------------------------- K-Ref
Σ; Δ; Ρ; Γ ⊢ &r f τ : ★

Σ; Δ; Ρ; Γ ⊢ r_1 : RGN    Σ; Δ; Ρ ⊢ f_1 : FRAC
...
Σ; Δ; Ρ; Γ ⊢ r_n : RGN    Σ; Δ; Ρ ⊢ f_n : FRAC
Σ; Δ; Ρ; Γ ⊢ τ_ret : ★
---------------------------------------------------------- K-Closure
Σ; Δ; Ρ; Γ ⊢ &r_1 f τ_1 ⊗ ... ⊗ &r_n f τ_n → τ_ret : ★

Σ; Δ; Ρ; Γ ⊢ r_1 : RGN    Σ; Δ; Ρ; Γ ⊢ f_1 : FRAC
...
Σ; Δ; Ρ; Γ ⊢ r_n : RGN    Σ; Δ; Ρ; Γ ⊢ f_n : FRAC
Σ; Δ; Ρ; Γ ⊢ τ_ret : ★
---------------------------------------------------------- K-MoveClosure
Σ; Δ; Ρ; Γ ⊢ &r_1 f τ_1 ⊗ ... ⊗ &r_n f τ_n ↝ τ_ret : ★

Σ; Δ, ς : κ; Ρ; Γ ⊢ τ : ★
----------------------------- K-Universal
Σ; Δ; Ρ; Γ ⊢ ∀ς : κ. τ : ★

Σ; Δ; Ρ; Γ ⊢ τ_1 : ★
...
Σ; Δ; Ρ; Γ ⊢ τ_n : ★
----------------------------------- K-Tuple
Σ; Δ; Ρ; Γ ⊢ τ_1 ⊗ ... ⊗ τ_n : ★

Σ; Δ; Ρ; Γ ⊢ χ_1 : κ_1
...
Σ; Δ; Ρ; Γ ⊢ χ_n : κ_n
S<ς_1 : κ_1, ..., ς_n : κ_n> ∈ dom(Σ)
-------------------------------------- K-Struct
Σ; Δ; Ρ; Γ ⊢ S<χ_1, ..., χ_n> : ★
```

#### `⊢ Σ`
Meaning: The data structure context `Σ` is well-formed. That is, all of the names are unique, and
all of the component types are well-formed with respect to type variables bound in the definition.

```
---- WF-EmptyStructContext
⊢ •

⊢ Σ    S ∉ dom(Σ)
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n };
  •, ς_1 : κ_1, ..., ς_n : κ_n; •; •
⊢ τ_1 : ★
...
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n };
  •, ς_1 : κ_1, ..., ς_n : κ_n; •; •
⊢ τ_n : ★
--------------------------------------------------------------------- WF-DefnStructRecord
⊢ Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n> { x_1: τ_1, ..., x_n: τ_n }

⊢ Σ    S ∉ dom(Σ)
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n);
  •, ς_1 : κ_1, ..., ς_n : κ_n; •; •
⊢ τ_1 : ★
...
Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n);
  •, ς_1 : κ_1, ..., ς_n : κ_n; •; •
⊢ τ_n : ★
------------------------------------------------------- WF-DefnStructTuple
⊢ Σ, struct S<ς_1 : κ_1, ..., ς_n : κ_n>(τ_1, ..., τ_n)

Σ, enum S<ς_1 : κ_1, ..., ς_n : κ_n> { ev_1, ..., ev_n };
  •, ς_1 : κ_1, ..., ς_n : κ_n
⊢ ev_1
...
Σ, enum S<ς_1 : κ_1, ..., ς_n : κ_n> { ev_1, ..., ev_n };
  •, ς_1 : κ_1, ..., ς_n : κ_n
⊢ ev_n
dom(ev_1) ≠ ... ≠ dom(ev_n) ;; i.e. all variant names are unique
----------------------------------------------------------------- WP-DefnEnum
⊢ Σ, enum S<ς_1 : κ_1, ..., ς_n : κ_n> { ev_1, ..., ev_n }
```

#### `Σ; Δ ⊢ ev`
Meaning: In the data structure context `Σ` and the kind environment `Δ`, the enum variant `ev` is
well-formed.

```
Σ; Δ; •; • ⊢ τ_1 : ★
...
Σ; Δ; •; • ⊢ τ_n : ★
----------------------- WF-TupleVariant
Σ; Δ ⊢ E(τ_1, ... τ_n)

Σ; Δ; •; • ⊢ τ_1 : ★
...
Σ; Δ; •; • ⊢ τ_n : ★
------------------------------------ WF-RecordVariant
Σ; Δ ⊢ E { x_1: τ_1, ... x_n: τ_n }
```

[˄ Back to top][toc]

## Dynamic Semantics

### Syntax Extensions

```
expresions e ::= ...
               | ptr ρ ƒ
               | fatptr ρ ƒ n_1 n_2 -- the value form of a slice, a pointer with a start and end

evaluation contexts E ::= []
                        | alloc E
                        | slice μ x.π E e
                        | slice μ x.π v E
                        | let μ x: τ = E; e
                        | E e
                        | v E
                        | E; e
                        | if E { e } else { e }
                        | for μ x in E { e_2 }
                        | (ptr ρ ƒ, ... E, e ...)
                        | let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = E; e
                        | S::<χ_1, ..., χ_n> { x: ptr ρ ƒ, ... x: E, x: e ... }
                        | S::<χ_1, ..., χ_n>(ptr ρ ƒ, ... E, e ...)
                        | S::E::<χ_1, ..., χ_n> { x: ptr ρ ƒ, ... x: E, x: e ... }
                        | S::E::<χ_1, ..., χ_n>(ptr ρ ƒ, ... E, e ...)
                        | E [χ]

simple values sv ::= true | false
                   | n
                   | ()
                   | ptr ρ ƒ
                   | fatptr ρ ƒ n_1 n_2
                   | |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                   | move |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                   | Λς: κ. e

values v ::= sv
           | [sv_1, ..., sv_n]
           | (sv_1, ..., sv_n)
           | S { x_1: sv_1, ..., x_n: sv_n }
           | S(sv_1, ..., sv_n)
           | S::E { x_1: sv_1, ..., x_n: sv_n }
           | S::E(sv_1, ..., sv_n)

region sets R ::= ∅
                | R ∪ { ρ ↦ ƒ ⊗ { Π ↦ ρ, ... } } 
                | R ∪ { ρ ↦ ƒ ⊗ { <tag> ↦ E, Π ↦ ρ, ... } }
                | R ∪ { ρ ↦ ƒ ⊗ { ε ↦ sv } }
                | R ∪ { ρ ↦ ƒ ⊗ { ε ↦ ρ } }
                
stores σ ::= • | σ ∪ { x ↦ ρ }
```

### Typing Extensions

```
------------------------------------------------------------ T-Ptr
Σ; Δ; Ρ, ρ ↦ τ ⊗ f ⊗ path_set; Γ ⊢ ptr ρ ƒ : &ρ ƒ τ ⇒ Ρ; Γ

----------------------------------------------------------------------------- T-FatPtr
Σ; Δ; Ρ, ρ ↦ [τ] ⊗ f ⊗ path_set; Γ ⊢ fatptr ρ ƒ n_1 n_2 : &ρ ƒ [τ] ⇒ Ρ; Γ
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
--------------------------------------------------------------- E-AllocStuctTup
(σ, R, alloc S::<χ_1, ..., χ_n>(ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)

fresh ρ
--------------------------------------------------------------------------- E-AllocStuctRecord
(σ, R, alloc S::<χ_1, ..., χ_n> { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)

fresh ρ
----------------------------------------------------------------------- E-AllocEnumTup
(σ, R, alloc S::E::<χ_1, ..., χ_n>(ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { <tag> ↦ E, 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)

fresh ρ
------------------------------------------------------------------------------ E-AllocEnumRecord
(σ, R, alloc S::E::<χ_1, ..., χ_n> { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { <tag> ↦ E, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)

fresh ρ
------------------------------------------------------------------ E-AllocArray
(σ, R, alloc [ptr ρ_1 1, ..., ptr ρ_n 1]) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n } }, ptr ρ 1)

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ { ε ↦ sv }
sv ~ prim
fresh ρ
------------------------------------------------------------ E-Copy
(σ, R, copy x.π) → (σ, R ∪ { ρ ↦ 1 ⊗ { ε ↦ sv }}, ptr ρ 1)

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
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }    ƒ_1 ≠ 0
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }    ƒ_2 ≠ 0
[n_1] ∈ dom(path_set) [n_2] ∈ dom(path_set)
ƒ_π / 2 ↓ ƒ_n
fresh ρ
----------------------------------------------------------------------------------- E-SliceImm
(σ, R, slice imm x.π (ptr ρ_1 ƒ_1) (ptr ρ_2 ƒ_2)) →
  (σ, R ∪ { ρ_π ↦ ƒ_n ⊗ path_set, ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π } }, fatptr ρ ƒ_n n_1 n_2)

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦  ⊗ ρath_set
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }    ƒ_1 ≠ 0
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }    ƒ_2 ≠ 0
[n_1] ∈ dom(path_set) [n_2] ∈ dom(path_set)
fresh ρ
------------------------------------------------------------------------------- E-SliceMut
(σ, R, slice mut x.π (ptr ρ_1 ƒ_1) (ptr ρ_2 ƒ_2)) →
  (σ, R ∪ { ρ_π ↦ 0 ⊗ path_set, ρ ↦ 1 ⊗ { ε ↦ ρ_π } }, fatptr ρ ƒ_n n_1 n_2)

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
ρ_1 ∉ dom(R) ... ρ_n ∉ dom(R)
------------------------------------------ E-Free
(σ, R, drop x) ↦ (σ / x, R / ρ, ())

μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ; e) → (σ ∪ { x ↦ ρ }, R, e)

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)((Π.)*ε) = ρ_π ↦ 1 ⊗ path_set
path_set ∪ { Π ↦ ρ } = new_path_set
;; TODO(maybe): recursively remove ρ_π from R
--------------------------------------------------------------------------- E-Assign
(σ, R, x.(Π.)*Π.ε := ptr ρ 1) → (σ, R ∪ { ρ_π ↦ 1 ⊗ new_path_set }, ())

σ(x) = ρ_x
R(ρ_x) = 1 ⊗ path_set
;; TODO(maybe): recursively remove ρ_x from R
------------------------------------------------- E-AssignEpsilon
(σ, R, x.ε := ptr ρ 1) → (σ ∪ { x ↦ ρ }, R, ())

-------------------------------------------------------------------------------------------- E-App
(σ, R, (|x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e }) (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)

---------------------------------------------------------------- E-MoveApp
(σ, R, (move |x_1: &ρ_1 ƒ_1 τ_1, ..., x_n: &ρ_n ƒ_n τ_n| { e })
       (ptr ρ_1 ƒ_1, ..., ptr ρ_n ƒ_n))
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)

-------------------------- E-Seq
(σ, R, (); e) → (σ, R, e)

ƒ ≠ 0
R(ρ) = ƒ ⊗ { ε ↦ true }
------------------------------------------------------ E-IfTrue
(σ, R, if ptr ρ ƒ { e_1 } else { e_2 }) → (σ, R, e_1)

ƒ ≠ 0
R(ρ) = ƒ ⊗ { ε ↦ false }
------------------------------------------------------ E-IfFalse
(σ, R, if ptr ρ ƒ { e_1 } else { e_2 }) → (σ, R, e_2)

R(ρ_1) = ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
ƒ_1 ≠ 0
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
------------------------------------------------------------------------------- E-ForArray
(σ, R, for μ x in (ptr ρ_1 ƒ_1) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_0 ƒ_ε_0; e_2); ...
         (let μ x = ptr ρ_ε_n-1 ƒ_ε_n-1; e_2); ())

;; using an ε path here resolves the slice to its backing array
R(ρ_1)(ε) = ρ_ε ↦ ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
ƒ_1 ≠ 0
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
---------------------------------------------------------------- E-ForSlice
(σ, R, for μ x in (fatptr ρ_1 ƒ_1 n_1 n_2) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_n_1 ƒ_ε_n_1; e_2); ...
         (let μ x = ptr ρ_ε_n_2 ƒ_ε_n_2; e_2); ())

--------------------------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = (ptr ρ_1 1, ..., ptr ρ_n 1); e)
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)

χ ≠ rgn of x.π ∧ χ ≠ cap of x.π
------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [χ]) → (σ, R, e[χ / ς])

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
------------------------------------------------------ E-TAppRgnOf
(σ, R, (Λς: κ. e) [rgn of x.π]) → (σ, R, e[ρ_π / ς])

σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
------------------------------------------------------ E-TAppCapOf
(σ, R, (Λς: κ. e) [cap of x.π]) → (σ, R, e[ƒ_π / ς])
```

[˄ Back to top][toc]

## Proof of Soundness

### Important Lemmas

**Lemma** (Canonical Forms):
   1. if `v` is a value of type `bool`, then `v` is either `true` or `false`.
   2. if `v` is a value of type `u32`, then `v` is a numeric value on the range `[0, 2^32)`.
   3. if `v` is a value of type `unit`, then `v` is `()`.
   4. if `v` is a value of type `&ρ ƒ τ`, then `v` is `ptr ρ ƒ`.
   5. if `v` is a value of type `&ρ ƒ [τ]`, then `v` is of the form `fatptr ρ ƒ n_1 n_2`.
   6. if `v` is a value of type `[τ; n]`, then `v` is of the form `[sv_1, ..., sv_n]`.
   7. if `v` is a value of type `(τ_1, ..., τ_n)`, then `v` is of the form `(sv_1, ..., sv_n)`.
   8. if `v` is a value of type `S`, then `v` is either of the form `S(sv_1, ..., sv_n)`,
      `S { x_1: sv_1, ..., x_n: sv_n }`, `S::E(sv_1, ..., sv_n)`, or
      `S::E { x_1: sv_1, ..., x_n: sv_n }` depending on its definition in `Σ`.
   9. if `v` is a value of type `&r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret`, then `v` is of
      the form `|x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }`.
  10. if `v` is a value of type `&r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n ↝ τ_ret`, then `v` is of
      the form `move |x_1: &r_1 f_1 τ_1, ..., x_n: &r_n f_n τ_n| { e }`.
  11. if `v` is a value of type `∀ς : κ. e`, then `v` is of the form `Λς: κ. e`.

**Lemma** (Type Substitution):

```
If Σ; Δ, ς : κ; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ' and Σ; Δ; Ρ; Γ ⊢ χ then,
   Σ; Δ; Ρ[χ / ς]; Γ[χ / ς] ⊢ e[χ / ς] : τ[χ / ς] ⇒ Ρ'[χ / ς]; Γ'[χ / ς]
```

[˄ Back to top][toc]

### Progress

#### Theorem.

```
∀Σ, Ρ, Γ, σ, R, e. (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Ρ'; Γ') ∧ (Ρ ⊢ R) ∧ (Γ ⊢ σ)
                     ⇒ (e ∈ 𝕍) ∨ (∃σ', R', e'. (σ, R, e) → (σ', R', e'))
```

#### Proof.

By induction on the derivation of `e : τ`.

The `T-True`, `T-False`, `T-Unit`, `T-u32`, `T-Ptr`, `T-FatPtr`, `T-Closure`, `T-MvClosure`, and
`T-TAbs` cases are all immediate since `e` is in all these cases a value. The other cases follow.

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

Relevant extra info:
```
primitives prim ::= true | false | n | ()

simple values sv ::= true | false
                   | n
                   | ()
                   | ptr ρ ƒ
                   | |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                   | move |x_1: &r_1 μ_1 τ_1, ... x_n: &r_n μ_n τ_n| { e }
                   | Λς: κ. e
```

It is easy to check (by looking at the grammar) that all primitives are included in `sv` (and `𝕍`).
Thus, we can step with `E-AllocSimple`.

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
Σ; Δ; Ρ_n; Γ_n ⊢ S::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
--------------------------------------------------------------------------- T-AllocStructTup
Σ; Δ; Ρ; Γ ⊢ alloc S::<χ_1, ..., χ_n>(e_1, ..., e_n)
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S<χ_1, ..., χ_n> ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
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
Σ ⊢ S::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }
-------------------------------------------------------------------------------- T-AllocStructRecord
Σ; Δ; Ρ; Γ ⊢ alloc S::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S::<χ_1, ..., χ_n> ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
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

##### Case `T-AllocEnumTup`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ; Δ; Ρ_n; Γ_n ⊢ S::E::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
------------------------------------------------------------------------------------- T-AllocEnumTup
Σ; Δ; Ρ; Γ ⊢ alloc S::E::<χ_1, ..., χ_n>(e_1, ..., e_n)
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S<χ_1, ..., χ_n> ⊗ 1 ⊗ { <tag> ↦ E, 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

We want to step with:
```
fresh ρ
----------------------------------------------------------------------- E-AllocEnumTup
(σ, R, alloc S::E::<χ_1, ..., χ_n>(ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { <tag> ↦ E, 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)
```

By IH, either `e_1 ∈ 𝕍` through `e_n ∈ 𝕍` or we can take a step for one of them. If they're all
values, we know from their types (`&ρ_1 1 τ_1` through `&ρ_n 1 τ_n`) and Canonical Forms, that `e_1`
through `e_n` are `ptr ρ_1 1` through `ptr ρ_n 1`. Thus, we can step with `E-AllocEnumTup`.

##### Case `T-AllocEnumRecord`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S::E::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }
---------------------------------------------------------------------------------- T-AllocEnumRecord
Σ; Δ; Ρ; Γ ⊢ alloc S::E::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S::<χ_1, ..., χ_n> ⊗ 1 ⊗ { <tag> ↦ E, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n
```

We want to step with:
```
fresh ρ
------------------------------------------------------------------------------ E-AllocEnumRecord
(σ, R, alloc S::E::<χ_1, ..., χ_n> { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { <tag> ↦ E, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)
```

By IH, either `e_1 ∈ 𝕍` through `e_n ∈ 𝕍` or we can take a step for one of them. If they're all
values, we know from their types (`&ρ_1 1 τ_1` through `&ρ_n 1 τ_n`) and Canonical Forms, that `e_1`
through `e_n` are `ptr ρ_1 1` through `ptr ρ_n 1`. Thus, we can step with `E-AllocEnumRecord`.

##### Case `T-AllocArray`:

From premise:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ ⇒ Ρ_n; Γ_n
--------------------------------------------------------------------------- T-AllocArray
Σ; Δ; Ρ; Γ ⊢ alloc [e_1, ..., e_n] : &ρ 1 [τ; n]
           ⇒ Ρ_n, ρ ↦ [τ; n] ⊗ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n }; Γ_n
```

We want to step with:
```
fresh ρ
------------------------------------------------------------------ E-AllocArray
(σ, R, alloc [ptr ρ_1 1, ..., ptr ρ_n 1]) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n } }, ptr ρ 1)
```

By IH, either `e_1 ∈ 𝕍` through `e_n ∈ 𝕍` or we can take a step for one of them. If they're all
values, weknow from their types (`&ρ_1 1 τ` through `&ρ_n 1 τ`) and Canonical Forms, that `e_1`
through `e_n` are `ptr ρ_1 1` through `ptr ρ_n 1`. Thus, we can step with `E-AllocArray`.

##### Case `T-Copy`:

From premise:
```
Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ f_π ⊗ π_path_set
f_π ≠ 0
τ_π ~ bt
fresh ρ
------------------------------------------------------ T-Copy
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ copy x.π : &ρ 1 τ_π
                    ⇒ Ρ, ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ τ_π };
                      Γ, x ↦ r_x
```

We want to step with:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ { ε ↦ sv }
sv ~ prim
fresh ρ
------------------------------------------------------------ E-Copy
(σ, R, copy x.π) → (σ, R ∪ { ρ ↦ 1 ⊗ { ε ↦ sv }}, ptr ρ 1)
```

From premise, we also know `Γ ⊢ σ` and `Ρ ⊢ R`. The former tells us that we can look up `σ(x)` to
get `ptr ρ_x ƒ_x`. With that and `Ρ ⊢ R`, we know `ρ_x ∈ Ρ` and that `R(ρ_x)(π)` is valid. From
the typing rule's premise, we know that the fractions are non-zero along the path, and so this
condition is met for `E-Copy` as well. We can also see from the grammar and Canonical Forms that if
the type `τ_π` is a base type `bt`, then a simple value `sv` at that type must be a `prim`. Thus, we
can indeed step with `E-Copy`.

##### Case `T-BorrowImm`:

From premise:
```
Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ ƒ_π ⊗ π_path_set
Ρ ⊢ imm r_π
f_π / 2 ↓ f_n
fresh ρ
-------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow imm x.π : &ρ f_n τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ f_n ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ f_n ⊗ { ε ↦ r_π };
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
Ρ(r_π) = τ_π ⊗ f_π ⊗ π_path_set
Ρ ⊢ mut r_π
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

##### Case `T-SliceImm`:

From premise:
```
Ρ ⊢ imm π in r_x : [τ_e; n] ⇒ r_π
Ρ(r_π) = [τ_e; n] ⊗ f_π ⊗ π_path_set
f_π / 2 ↓ f_n
fresh ρ
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Γ_2
-------------------------------------------------------------- T-SliceImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ slice imm x.π e_1 e_2 : &ρ [τ]
                    ⇒ Ρ_2, r_π ↦ [τ_e; n] ⊗ f_n ⊗ π_path_set,
                           ρ ↦ [τ_e] ⊗ f_n ⊗ { ε ↦ r_π };
                      Γ_2, x ↦ r_x
```

We want to step with:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }    ƒ_1 ≠ 0
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }    ƒ_2 ≠ 0
[n_1] ∈ dom(path_set) [n_2] ∈ dom(path_set)
ƒ_π / 2 ↓ ƒ_n
fresh ρ
----------------------------------------------------------------------------------- E-SliceImm
(σ, R, slice imm x.π (ptr ρ_1 ƒ_1) (ptr ρ_2 ƒ_2)) →
  (σ, R ∪ { ρ_π ↦ ƒ_n ⊗ path_set, ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π } }, fatptr ρ ƒ_n n_1 n_2)
```

From premise, we also know `Γ ⊢ σ` and `Ρ ⊢ R`. The former tells us that we can look up `σ(x)` to
get `ρ_x`, `ρ_1`, and `ρ_2`. With that and `Ρ ⊢ R`, we know that `R(ρ_x)(π)` is valid. From the
typing rule's premise, we know that the fractions are non-zero along the path. We also know from the
types that `r_1` and `r_2` are at the type `u32`, and thus we can determine using Canonical Forms
that the simple value for those regions is of the form `n`. Thus, as long as these numbers are in
bounds for the array, we can step using `E-SliceImm`.

TODO: deal with the out of bounds case.

##### Case `T-SliceMut`:

From premise:
```
Ρ ⊢ mut π in r_x : [τ_e; n] ⇒ r_π
Ρ(r_π) = [τ_e; n] ⊗ 1 ⊗ π_path_set
fresh ρ
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Γ_2
------------------------------------------------------------- T-SliceMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ slice mut x.π e_1 e_2 : &ρ [τ]
                    ⇒ Ρ_2, r_π ↦ [τ_e; n] ⊗ 0 ⊗ π_path_set,
                           ρ ↦ [τ_e] ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ_2, x ↦ r_x
```

We want to step with:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦  ⊗ ρath_set
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }    ƒ_1 ≠ 0
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }    ƒ_2 ≠ 0
[n_1] ∈ dom(path_set) [n_2] ∈ dom(path_set)
fresh ρ
------------------------------------------------------------------------------- E-SliceMut
(σ, R, slice mut x.π (ptr ρ_1 ƒ_1) (ptr ρ_2 ƒ_2)) →
  (σ, R ∪ { ρ_π ↦ 0 ⊗ path_set, ρ ↦ 1 ⊗ { ε ↦ ρ_π } }, fatptr ρ ƒ_n n_1 n_2)
```

From premise, we also know `Γ ⊢ σ` and `Ρ ⊢ R`. The former tells us that we can look up `σ(x)` to
get `ρ_x`, `ρ_1`, and `ρ_2`. With that and `Ρ ⊢ R`, we know that `R(ρ_x)(π)` is valid. From the
typing rule's premise, we know that the fractions are non-zero along the path. We also know from the
types that `r_1` and `r_2` are at the type `u32`, and thus we can determine using Canonical Forms
that the simple value for those regions is of the form `n`. Thus, as long as these numbers are in
bounds for the array, we can step using `E-SliceMut`.

TODO: deal with the out of bounds case.

##### Case `T-Drop`:

From premise:
```
Ρ(r_x) = τ_x ⊗ f_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ f_r ⊗ path_set
f_r + f_x ↓ f_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ f_n ⊗ path_set; Γ
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
r_1 ∉ dom(Ρ) ... r_n ∉ dom(Ρ) ;; i.e. all the referenced regions have already been dropped
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------- T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ
```

We want to step with:
```
σ(x) = ρ
R(ρ) = 1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }
ρ_1 ∉ dom(R) ... ρ_n ∉ dom(R)
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
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

We want to step with:
```
μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ; e) → (σ ∪ { x ↦ ρ }, R, e)
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
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

We want to step with:
```
μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ; e) → (σ ∪ { x ↦ ρ }, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, `e_1 ∈ 𝕍` and of type `&ρ ƒ τ`
from case, by Canonical Forms, `e_1` is of the form `ptr ρ ƒ`. Thus, we can use `E-Let` to step.

##### Case `T-Assign`:

From premise:
```
Ρ ⊢ mut (Π.)*ε in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Ρ ⊢ mut r_π
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : &r_n 1 τ_π ⇒ Ρ'; Γ'
π_path_set ∪ { Π ↦ r_n } = new_path_set
------------------------------------------------------ T-Assign
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.(Π.)*Π.ε := e
                    : unit
                    ⇒ Ρ', r_π ↦ τ_n ⊗ 1 ⊗ new_path_set; Γ'
```

We want to step with:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)((Π.)*ε) = ρ_π ↦ 1 ⊗ path_set
path_set ∪ { Π ↦ ρ } = new_path_set
;; TODO(maybe): recursively remove ρ_π from R
--------------------------------------------------------------------------- E-Assign
(σ, R, x.(Π.)*Π.ε := ptr ρ 1) → (σ, R ∪ { ρ_π ↦ 1 ⊗ new_path_set }, ())
```

By IH, either `e ∈ 𝕍` or we can take a step. In the former case, `e ∈ 𝕍` and of type `&r_n 1 τ`.
Then, by Canonical Forms, `e` is of the form `ptr ρ 1`. Then, from
`Ρ ⊢ mut (Π.)*ε in r_x : τ_π ⇒ r_π`, we know that `R(ρ_x)((Π.)*ε)` succeeds. Thus, we can step
using `E-Assign`.

##### Case `T-AssignEpsilon`:

From premise:
```
Ρ ⊢ mut r_x
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : &r_n 1 τ_π ⇒ Ρ'; Γ'
--------------------------------------------------------- T-AssignEpsilon
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.ε := e : unit ⇒ Ρ'; Γ', x ↦ r_n
```

We want to step with:
```
σ(x) = ρ_x
R(ρ_x) = 1 ⊗ path_set
;; TODO(maybe): recursively remove ρ_x from R
------------------------------------------------- E-AssignEpsilon
(σ, R, x.ε := ptr ρ 1) → (σ ∪ { x ↦ ρ }, R, ())
```

By IH, either `e ∈ 𝕍` or we can take a step. In the former case, `e ∈ 𝕍` and of type `&r_n 1 τ`.
Then, by Canonical Forms, `e` is of the form `ptr ρ 1`. We know from `Ρ ⊢ mut r_x` that `ρ_x` has a
capability of `1`. Thus, we can step using `E-AssignEpsilon`.

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

##### Case `T-Seq`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : unit ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
---------------------------------------- T-Seq
Σ; Δ; Ρ; Γ ⊢ e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

We want to step with:
```
-------------------------- E-Seq
(σ, R, (); e) → (σ, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, we know `e_1 : unit` and thus by
Canonical Forms `e_1` is `()`. Thus, we can step using `E-Seq`.

##### Case `T-If`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 bool ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ ⇒ Ρ_2; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_3 : τ ⇒ Ρ_3; Γ_1
;; FIXME: we need to somehow unify Ρ_2 and Ρ_3
;; in particular, τ is not necessarily identical in e_2
;; and e_2, but we should be able to join ρ's in each
-------------------------------------------------------- T-If
Σ; Δ; Ρ; Γ ⊢ if e_1 { e_2 } else { e_3 } : τ ⇒ Ρ'; Γ_1
```

We want to step with either of:
```
ƒ ≠ 0
R(ρ) = ƒ ⊗ { ε ↦ true }
------------------------------------------------------ E-IfTrue
(σ, R, if ptr ρ ƒ { e_1 } else { e_2 }) → (σ, R, e_1)

ƒ ≠ 0
R(ρ) = ƒ ⊗ { ε ↦ false }
------------------------------------------------------ E-IfFalse
(σ, R, if ptr ρ ƒ { e_1 } else { e_2 }) → (σ, R, e_2)
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, we know that
`e_1 : &r_1 f_1 bool` which tells us that the value stored in its region is a `bool`. Thus,
we know by Canonical Forms that this simple value is either `true` or `false`. Then, we can step
using `E-IfTrue` or `E-IfFalse` respectively.

##### Case `T-ForImm`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ imm r_1    f_1 ≠ 0
Ρ(r_1) = τ_1 ⊗ f_1 ⊗ path_set_1
fresh ρ
f_1 / 2 ↓ f_n
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ f_n ⊗ path_set_1, ρ ↦ τ ⊗ f_n ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
--------------------------------------------------------------------- T-ForImm
Σ; Δ; Ρ; Γ ⊢ for imm x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1
```

We want to step with either of:
```
R(ρ_1) = ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
ƒ_1 ≠ 0
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
------------------------------------------------------------------------------- E-ForArray
(σ, R, for μ x in (ptr ρ_1 ƒ_1) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_0 ƒ_ε_0; e_2); ...
         (let μ x = ptr ρ_ε_n-1 ƒ_ε_n-1; e_2); ())

;; using an ε path here resolves the slice to its backing array
R(ρ_1)(ε) = ρ_ε ↦ ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
ƒ_1 ≠ 0
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
---------------------------------------------------------------- E-ForSlice
(σ, R, for μ x in (fatptr ρ_1 ƒ_1 n_1 n_2) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_n_1 ƒ_ε_n_1; e_2); ...
         (let μ x = ptr ρ_ε_n_2 ƒ_ε_n_2; e_2); ())
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, we know that `e_1 : &r_1 f_1 τ_1`
where `τ_1` is either of the form `[τ; n]` or `[τ]` (that is, it's either an array or a slice). From
the typing rule premise `Ρ ⊢ imm r_1`, we know that all of the subregions for arrays have non-zero
fractions and thus can be immutably bound to `x` in the let results. Thus, we can step with either
`E-ForArray` or `E-ForSlice`, depending on which of the types we have for `τ_1`.

##### Case `T-ForMut`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ mut r_1
Ρ(r_1) = τ_1 ⊗ 1 ⊗ path_set_1
fresh ρ
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ 0 ⊗ path_set_1, ρ ↦ τ ⊗ 1 ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
----------------------------------------------------------------- T-ForMut
Σ; Δ; Ρ; Γ ⊢ for mut x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1
```

We want to step with either of:
```
;; using an ε path means resolving any aliasing, e.g. for references to arrays
R(ρ_1)(ε) = ρ_ε ↦ ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
------------------------------------------------------------------------------- E-ForArray
(σ, R, for μ x in (ptr ρ_1 ƒ_1) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_0 ƒ_ε_0; e_2); ...
         (let μ x = ptr ρ_ε_n-1 ƒ_ε_n-1; e_2); ())

;; using an ε path means resolving any aliasing 
R(ρ_1)(ε) = ρ_ε ↦ ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
---------------------------------------------------------------- E-ForSlice
(σ, R, for μ x in (fatptr ρ_1 ƒ_1 n_1 n_2) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_n_1 ƒ_ε_n_1; e_2); ...
         (let μ x = ptr ρ_ε_n_2 ƒ_ε_n_2; e_2); ())
```

By IH, either `e_1 ∈ 𝕍` or we can take a step. In the former case, we know that `e_1 : &r_1 f_1 τ_1`
where `τ_1` is either of the form `[τ; n]` or `[τ]` (that is, it's either an array or a slice). From
the typing rule premise `Ρ ⊢ mut r_1`, we know that all of the subregions for arrays have fractions
of 1 and thus can be immutably bound to `x` in the let results. Thus, we can step with either
`E-ForArray` or `E-ForSlice`, depending on which of the types we have for `τ_1`.

##### Case `T-LetTup`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n) ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ r_1, ... x_n ↦ r_n ⊢ e_2 : t_r ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2) ... r_n ∉ dom(Ρ_2)
----------------------------------------------------------------------- T-LetTup
Σ; Δ; Ρ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1; e_2
           : τ_r ⇒ Ρ_2; Γ_2
```

We want to step with:
```
--------------------------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = (ptr ρ_1 1, ..., ptr ρ_n 1); e)
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

By IH, either `e_1 ∈ 𝕍` or we can step. In the former case, we know
`e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n)` and thus by Canonical Forms, `e_1` is of the form
`(ptr ρ_1 1, ..., ptr ρ_n 1)`. Thus, we can step using `E-LetTup`.

##### Case `T-TApp`:

From premise:
```
Σ; Δ; Ρ; Γ ⊢ e : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ χ : κ
χ ~ f ⇒ χ ≠ 0
---------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e [χ] : τ[χ / ς] ⇒ Ρ'; Γ'
```

We want to step with:
```
------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [χ]) → (σ, R, e[χ / ς])
```

By IH, either `e ∈ 𝕍` or we can step. In the former case, we know `e : ∀ς : κ. τ`. By Canonical
Forms, `e` is of the form `Λς : κ. e` Thus, we can apply `E-TApp` to step forward.

[˄ Back to top][toc]

### Preservation

#### Theorem.

```
∀Σ, Ρ, Γ, σ, R, e, σ', R', e'.
  (Σ; •; Ρ; Γ ⊢ e : τ ⇒ Ρ_f; Γ_f) ∧ (Ρ ⊢ R) ∧ (Γ ⊢ σ) ∧ (σ, R, e) → (σ', R', e')
    ⇒ ∃Ρ', Γ'. (Γ' ⊢ σ') ∧ (Ρ' ⊢ R') ∧ (Σ; •; P'; Γ' ⊢ e' : τ ⇒ Ρ_f; Γ_f)
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

`Γ'` and `Γ' ⊢ σ'`: `E-AllocSimple` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocSimple` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding `ρ ↦ τ ⊗ 1 ⊗ { ε ↦ τ }`.
This corresponds to the same change we see being made in `T-AllocPrim`. Since we picked the change
to mirror the one in `R`, `Ρ' ⊢ R'` still holds.

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

`Γ'` and `Γ' ⊢ σ'`: `E-AllocTup` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and `Γ'`
are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocTup` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n }`. This corresponds to the same change we see being made in
`T-AllocTup`. Since we picked this change to mirror the one in `R`, `Ρ' ⊢ R'` still holds.

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
Σ; Δ; Ρ_n; Γ_n ⊢ S::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
--------------------------------------------------------------------------- T-AllocStructTup
Σ; Δ; Ρ; Γ ⊢ alloc S::<χ_1, ..., χ_n>(e_1, ..., e_n)
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S<χ_1, ..., χ_n> ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

`Γ'` and `Γ' ⊢ σ'`: `E-AllocStructTup` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocStructTup` changed `R` by adding a binding for a fresh `ρ`. So, we can
pick `Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n }`. This corresponds to the same change we see being made in
`T-AllocStructTup`. Since we picked this change to mirror the one in `R`, `Ρ' ⊢ R'` still holds.

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
Σ ⊢ S::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }
-------------------------------------------------------------------------------- T-AllocStructRecord
Σ; Δ; Ρ; Γ ⊢ alloc S::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S::<χ_1, ..., χ_n> ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n
```

`Γ'` and `Γ' ⊢ σ'`: `E-AllocStructRecord` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocStructRecord` changed `R` by adding a binding for a fresh `ρ`. So, we
can pick `Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }`. This corresponds to the same change we see being made
in `T-AllocStructRecord`. Since we picked this change to mirror the one in `R`, `Ρ' ⊢ R'` still
holds.

`e'` is well-typed: From `E-AllocStructRecord`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-AllocEnumTup`:

From premise:
```
fresh ρ
----------------------------------------------------------------------- E-AllocEnumTup
(σ, R, alloc S::E::<χ_1, ..., χ_n>(ptr ρ_1 1, ..., ptr ρ_n 1)) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { <tag> ↦ E, 1 ↦ ρ_1, ..., n ↦ ρ_n } }, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `alloc S::E(e_1, ..., e_n)`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ; Δ; Ρ_n; Γ_n ⊢ S::E::<χ_1, ..., χ_n>(τ_1, ..., τ_n)
------------------------------------------------------------------------------------- T-AllocEnumTup
Σ; Δ; Ρ; Γ ⊢ alloc S::E::<χ_1, ..., χ_n>(e_1, ..., e_n)
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S<χ_1, ..., χ_n> ⊗ 1 ⊗ { <tag> ↦ E, 1 ↦ ρ_1, ..., n ↦ ρ_n };
             Γ_n
```

`Γ'` and `Γ' ⊢ σ'`: `E-AllocEnumTup` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocEnumTup` changed `R` by adding a binding for a fresh `ρ`. So, we can
pick `Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { 1 ↦ ρ_1, ..., n ↦ ρ_n }`. This corresponds to the same change we see being made in
`T-AllocEnumTup`. Since we picked this change to mirror the one in `R`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: From `E-AllocEnumTup`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and `Ρ'`
that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some fraction
`ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-AllocEnumRecord`:

From premise:
```
fresh ρ
------------------------------------------------------------------------------ E-AllocEnumRecord
(σ, R, alloc S::E::<χ_1, ..., χ_n> { x_1: ptr ρ_1 1, ..., x_n: ptr ρ_n 1 }) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { <tag> ↦ E, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n } }, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `alloc S::E { x_1: e_1, ..., x_n: e_n }`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ_1 ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ_n ⇒ Ρ_n; Γ_n
Σ ⊢ S::E::<χ_1, ..., χ_n> { x_1: τ_1, ..., x_n: τ_n }
---------------------------------------------------------------------------------- T-AllocEnumRecord
Σ; Δ; Ρ; Γ ⊢ alloc S::E::<χ_1, ..., χ_n> { x_1: e_1, ..., x_n: e_n }
           : &ρ 1 S<χ_1, ..., χ_n>
           ⇒ Ρ_n, ρ ↦ S::<χ_1, ..., χ_n> ⊗ 1 ⊗ { <tag> ↦ E, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n };
             Γ_n
```

`Γ'` and `Γ' ⊢ σ'`: `E-AllocEnumRecord` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocEnumRecord` changed `R` by adding a binding for a fresh `ρ`. So, we
can pick `Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }`. This corresponds to the same change we see being made
in `T-AllocEnumRecord`. Since we picked this change to mirror the one in `R`, `Ρ' ⊢ R'` still
holds.

`e'` is well-typed: From `E-AllocEnumRecord`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-AllocArray`:

From premise:
```
fresh ρ
------------------------------------------------------------------ E-AllocArray
(σ, R, alloc [ptr ρ_1 1, ..., ptr ρ_n 1]) →
  (σ, R ∪ { ρ ↦ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n } }, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `alloc [ptr ρ_1 1, ..., ptr ρ_n 1]`:
```
fresh ρ
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_n 1 τ ⇒ Ρ_1; Γ_1
...
Σ; Δ; Ρ_n-1; Γ_n-1 ⊢ e_n : &ρ_n 1 τ ⇒ Ρ_n; Γ_n
--------------------------------------------------------------------------- T-AllocArray
Σ; Δ; Ρ; Γ ⊢ alloc [e_1, ..., e_n] : &ρ 1 [τ; n]
           ⇒ Ρ_n, ρ ↦ [τ; n] ⊗ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n }; Γ_n
```

`Γ'` and `Γ' ⊢ σ'`: `E-AllocArray` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-AllocArray` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the extra binding
`ρ ↦ τ ⊗ 1 ⊗ { [0] ↦ ρ_1, ..., [n-1] ↦ ρ_n }`. This corresponds to the same change we see being
made in `T-AllocArray`. Since we picked this change to mirror the one in `R`, `Ρ' ⊢ R'` still
holds.

`e'` is well-typed: From `E-AllocArray`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and `Ρ'` that
we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some fraction `ƒ`)
to derive `e' : &ρ 1 τ`.

##### Case `E-Copy`:

From premise:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ { ε ↦ sv }
sv ~ prim
fresh ρ
------------------------------------------------------------ E-Copy
(σ, R, copy x.π) → (σ, R ∪ { ρ ↦ 1 ⊗ { ε ↦ sv }}, ptr ρ 1)
```

From premise and knowledge that `e` is of the form `copy x.π`:
```
Ρ ⊢ imm π in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ f_π ⊗ π_path_set
f_π ≠ 0
τ_π ~ bt
fresh ρ
------------------------------------------------------ T-Copy
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ copy x.π : &ρ 1 τ_π
                    ⇒ Ρ, ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ τ_π };
                      Γ, x ↦ r_x
```

`Γ'` and `Γ' ⊢ σ'`: `E-Copy` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-Copy` changed `R` by adding a binding for a fresh `ρ`. This corresponds
to the same change we see being made in `T-Copy`. Since we picked this change to mirror the one
in `R`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: From `E-Copy`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ 1 τ_π`.

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
Ρ(r_π) = τ_π ⊗ f_π ⊗ π_path_set
f_π / 2 ↓ f_n
fresh ρ
-------------------------------------------------------- T-BorrowImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow imm x.π : &ρ f_n τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ f_n ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ f_n ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
```

`Γ'` and `Γ' ⊢ σ'`: `E-BorrowImm` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-BorrowImm` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the changed binding for `ρ_π` modifying the
fraction from `ƒ_π` to `ƒ_n` and the extra binding `ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ ρ_π }`. This corresponds
to the same change we see being made in `T-BorrowImm`. Since we picked this change to mirror the one
in `R`, `Ρ' ⊢ R'` still holds.

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
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
fresh ρ
------------------------------------------------------ T-BorrowMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ borrow mut x.π : &ρ 1 τ_π
                    ⇒ Ρ, r_π ↦ τ_π ⊗ 0 ⊗ π_path_set,
                         ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ, x ↦ r_x
```

`Γ'` and `Γ' ⊢ σ'`: `E-BorrowMut` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-BorrowMut` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the changed binding for `ρ_π` modifying the
fraction from `ƒ_π` to `1` and the extra binding `ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ ρ_π }`. This corresponds to
the same change we see being made in `T-BorrowMut`. Since we picked this change to mirror the one in
`R`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: From `E-BorrowMut`, we know `e' = ptr ρ 1`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-Ptr` (whose only requirement is that `ρ` is bound to some
fraction `ƒ`) to derive `e' : &ρ 1 τ`.

##### Case `E-SliceImm`:

From premise:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ ≠ 0
R(ρ_x)(π) = ρ_π ↦ ƒ_π ⊗ ρath_set
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }    ƒ_1 ≠ 0
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }    ƒ_2 ≠ 0
[n_1] ∈ dom(path_set) [n_2] ∈ dom(path_set)
ƒ_π / 2 ↓ ƒ_n
fresh ρ
----------------------------------------------------------------------------------- E-SliceImm
(σ, R, slice imm x.π (ptr ρ_1 ƒ_1) (ptr ρ_2 ƒ_2)) →
  (σ, R ∪ { ρ_π ↦ ƒ_n ⊗ path_set, ρ ↦ ƒ_n ⊗ { ε ↦ ρ_π } }, fatptr ρ ƒ_n n_1 n_2)
```

From premise and knowledge that `e` is of the form `slice imm x.π e_1 e_2`:
```
Ρ ⊢ imm π in r_x : [τ_e; n] ⇒ r_π
Ρ(r_π) = [τ_e; n] ⊗ f_π ⊗ π_path_set
f_π / 2 ↓ f_n
fresh ρ
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Γ_2
-------------------------------------------------------------- T-SliceImm
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ slice imm x.π e_1 e_2 : &ρ [τ]
                    ⇒ Ρ_2, r_π ↦ [τ_e; n] ⊗ f_n ⊗ π_path_set,
                           ρ ↦ [τ_e] ⊗ f_n ⊗ { ε ↦ r_π };
                      Γ_2, x ↦ r_x
```

`Γ'` and `Γ' ⊢ σ'`: `E-SliceImm` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and `Γ'`
are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-SliceImm` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the changed binding for `ρ_π` modifying the
fraction from `ƒ_π` to `ƒ_n` and the extra binding `ρ ↦ τ_π ⊗ ƒ_n ⊗ { ε ↦ ρ_π }`. This corresponds
to the same change we see being made in `T-SliceImm`. Since we picked this change to mirror the one
in `R`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: From `E-SliceImm`, we know `e' = fatptr ρ ƒ_n n_1 n_2`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-FatPtr` (whose only requirement is that `ρ` is bound to the
same fraction `ƒ`) to derive `e' : &ρ ƒ_n [τ]`.

##### Case `E-SliceMut`:

From premise:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)(π) = ρ_π ↦  ⊗ ρath_set
R(ρ_1) = ƒ_1 ⊗ { ε ↦ n_1 }    ƒ_1 ≠ 0
R(ρ_2) = ƒ_2 ⊗ { ε ↦ n_2 }    ƒ_2 ≠ 0
[n_1] ∈ dom(path_set) [n_2] ∈ dom(path_set)
fresh ρ
------------------------------------------------------------------------------- E-SliceMut
(σ, R, slice mut x.π (ptr ρ_1 ƒ_1) (ptr ρ_2 ƒ_2)) →
  (σ, R ∪ { ρ_π ↦ 0 ⊗ path_set, ρ ↦ 1 ⊗ { ε ↦ ρ_π } }, fatptr ρ ƒ_n n_1 n_2)
```

From premise and knowledge that `e` is of the form `slice mut x.π e_1 e_2`:
```
Ρ ⊢ mut π in r_x : [τ_e; n] ⇒ r_π
Ρ(r_π) = [τ_e; n] ⊗ 1 ⊗ π_path_set
fresh ρ
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e_1 : &r_1 f_1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &r_2 f_2 u32 ⇒ Ρ_2; Γ_2
------------------------------------------------------------- T-SliceMut
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ slice mut x.π e_1 e_2 : &ρ [τ]
                    ⇒ Ρ_2, r_π ↦ [τ_e; n] ⊗ 0 ⊗ π_path_set,
                           ρ ↦ [τ_e] ⊗ 1 ⊗ { ε ↦ r_π };
                      Γ_2, x ↦ r_x
```

`Γ'` and `Γ' ⊢ σ'`: `E-SliceMut` did not change `σ` and so we pick `Γ` as `Γ'`. Since `σ'` and `Γ'`
are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-SliceMut` changed `R` by adding a binding for a fresh `ρ`. So, we can pick
`Ρ'` to be `Ρ` (recall from the premise `Ρ ⊢ R`) with the changed binding for `ρ_π` modifying the
fraction from `ƒ_π` to `0` and the extra binding `ρ ↦ τ_π ⊗ 1 ⊗ { ε ↦ ρ_π }`. This corresponds
to the same change we see being made in `T-SliceMut`. Since we picked this change to mirror the one
in `R`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: From `E-SliceMut`, we know `e' = fatptr ρ 1 n_1 n_2`. Then, using the `Γ'` and
`Ρ'` that we picked, we can apply `T-FatPtr` (whose only requirement is that `ρ` is bound to the
same fraction `ƒ`) to derive `e' : &ρ 1 [τ]`.

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
Ρ(r_x) = τ_x ⊗ f_x ⊗ { ε ↦ r }
Ρ(r) = τ_r ⊗ f_r ⊗ path_set
f_r + f_x ↓ f_n
----------------------------------------------------------------------- T-Drop
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ, r ↦ τ_r ⊗ f_n ⊗ path_set; Γ
```

`Γ'` and `Γ' ⊢ σ'`: `E-Drop` changed `σ` by removing `x` and so we can mirror the change by picking
`Γ'` to be `Γ / x`. Since we picked this change to mirror the one in `σ'`, `Γ' ⊢ σ'` still holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-Drop` changes `R` by removing `ρ_x` and updating the binding for `ρ_s` with
the new fraction `ƒ_n`. So, we'll pick `Ρ'` that mirrors this by taking `Ρ`, removing `ρ_x` and
adding `ρ_s ↦ τ_s ⊗ ƒ_n ⊗ path_set`. Since we picked this change to mirror the one in `R'`,
`Ρ' ⊢ R'` still holds.

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

`Γ'` and `Γ' ⊢ σ'`: `E-FreeImmediate` changed `σ` by removing `x` and so we can mirror the change by
picking `Γ'` to be `Γ / x`. Since we picked this change to mirror the one in `σ'`, `Γ' ⊢ σ'` still
holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-FreeImmediate` changed `R` by removing `ρ` and so we can mirror the change by
picking `Ρ'` to be `Ρ / x`. Since we picked this change to mirror the one in `R'`, `Ρ' ⊢ R'` still
holds.

`e'` is well-typed: From `E-FreeImmediate`, we know `e' = ()` and this is trivially well-typed by
`T-Unit`.

##### Case `E-Free`:

From premise:
```
σ(x) = ρ
R(ρ) = 1 ⊗ { Π_1 ↦ ρ_1, ..., Π_n ↦ ρ_n }
ρ_1 ∉ dom(R) ... ρ_n ∉ dom(R)
------------------------------------------ E-Free
(σ, R, drop x) ↦ (σ / x, R / ρ, ())
```

From premise and knowledge that `e` is of the form `drop x`:
```
Ρ(r_x) = τ ⊗ 1 ⊗ { Π_1 ↦ r_1, ..., Π_n ↦ r_n }
r_1 ∉ dom(Ρ) ... r_n ∉ dom(Ρ) ;; i.e. all the referenced regions need to have been dropped already
Ρ' = Ρ - r_x
------------------------------------------------------------------------------------------ T-Free
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ drop x : unit ⇒ Ρ'; Γ
```

`Γ'` and `Γ' ⊢ σ'`: `E-Free` changed `σ` by removing `x` and so we can mirror the change by picking
`Γ'` to be `Γ / x`. Since we picked this change to mirror the one in `σ'`, `Γ' ⊢ σ'` still holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-Free` changed `R` by removing `ρ` and so we can mirror the change by picking
`Ρ'` to be `Ρ / x`. Since we picked this change to mirror the one in `R'`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: From `E-Free`, we know `e' = ()` and this is trivially well-typed by `T-Unit`.

##### Case `E-Let`:

From premise:
```
μ = mut ⇒ ƒ = 1
ƒ ≠ 0
---------------------------------------------------------- E-Let
(σ, R, let μ x: τ = ptr ρ ƒ; e) → (σ ∪ { x ↦ ρ }, R, e)
```

From premise and knowledge that `e` is of the form `let μ x: τ = ptr ρ ƒ`, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```
or:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

`Γ'` and `Γ' ⊢ σ'`: `E-Let` adds a new binding to `σ` for `x` to `ρ`, and so we can pick `Γ'` to
have the analagous change of adding `x ↦ ρ` to `Γ`. Since we picked this change to mirror the one in
`σ'`, `Γ' ⊢ σ'` still holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-Let` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'` and
`Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.


`e'` is well-typed: We know from the premises of `T-LetImm` and `T-LetMut` that `e_2` is well typed
in our `Γ'`. Since `E-Let` steps to `e_2`, we then know that it's well-typed.

##### Case `E-Assign`:

From premise:
```
σ(x) = ρ_x
;; looking up the whole path through regions checks ƒ = 1
R(ρ_x)((Π.)*ε) = ρ_π ↦ 1 ⊗ path_set
path_set ∪ { Π ↦ ρ } = new_path_set
;; TODO(maybe): recursively remove ρ_π from R
--------------------------------------------------------------------------- E-Assign
(σ, R, x.(Π.)*Π.ε := ptr ρ 1) → (σ, R ∪ { ρ_π ↦ 1 ⊗ new_path_set }, ())
```

From premise and knowledge that `e` is of the form `x.(Π.)*Π.ε := ptr ρ 1` then:
```
Ρ ⊢ mut (Π.)*ε in r_x : τ_π ⇒ r_π
Ρ(r_π) = τ_π ⊗ 1 ⊗ π_path_set
Ρ ⊢ mut r_π
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : &r_n 1 τ_π ⇒ Ρ'; Γ'
π_path_set ∪ { Π ↦ r_n } = new_path_set
------------------------------------------------------ T-Assign
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.(Π.)*Π.ε := e
                    : unit
                    ⇒ Ρ', r_π ↦ τ_n ⊗ 1 ⊗ new_path_set; Γ'
```

`Γ'` and `Γ' ⊢ σ'`: `E-Assign` leaves `σ` unchanged, and so we can pick `Γ'` to be `Γ`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: In `E-Assign`, we look up the immediate parent of the node in the path
(`(Π.)*ε`) and update its binding for `Π` to point to the new region `ρ`. We can mirror this change
by picking `Ρ'` to be `Ρ` with `ρ_π ↦ τ_n ⊗ 1 ⊗ new_path_set` (where `new_path_set` is as appears in
`T-Assign` premise). Since we picked this change to mirror the one in `R'`, `Ρ' ⊢ R'` still holds.

`e'` is well-typed: The resulting expression of `E-Assign` is `()` which is well-typed by `T-Unit`.

##### Case `E-AssignEpsilon`:

From premise:
```
σ(x) = ρ_x
R(ρ_x) = 1 ⊗ path_set
;; TODO(maybe): recursively remove ρ_x from R
------------------------------------------------- E-AssignEpsilon
(σ, R, x.ε := ptr ρ 1) → (σ ∪ { x ↦ ρ }, R, ())
```

From premise and knowledge that `e` is of the form `x.ε := ptr ρ 1` then:
```
Ρ ⊢ mut r_x
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ e : &r_n 1 τ_π ⇒ Ρ'; Γ'
--------------------------------------------------------- T-AssignEpsilon
Σ; Δ; Ρ; Γ, x ↦ r_x ⊢ x.ε := e : unit ⇒ Ρ'; Γ', x ↦ r_n
```

`Γ'` and `Γ' ⊢ σ'`: In `E-AssignEpsilon`, we rebind `x` to the new region `ρ` from the pointer. We
can mirror this by choosing `Γ'` to be `Γ` with `x ↦ ρ`. Since we picked this change to mirror the
one in `σ'`, `Γ' ⊢ σ'` stll holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-AssignEpsilon` leaves `R` unchanged, and so we can pick `Ρ'` to be `Ρ`. Since
`R'` and `Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: The resulting expression of `E-AssignEpsilon` is `()` which is well-typed by
`T-Unit`.

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

`Γ'` and `Γ' ⊢ σ'`: In `E-App`, we add new bindings to `σ` for `x_1` through `x_n`. We can mirror
this for `Γ` by picking `Γ'` to be `Γ, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n`. Since we picked this change to
mirror the one in `σ'`, `Γ' ⊢ σ'` still holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-App` leaves `R` unchanged, and so we can pick `Ρ` as `Ρ'`. Since `R'` and
`Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

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

`Γ'` and `Γ' ⊢ σ'`: In `E-MoveApp`, we add new bindings to `σ` for `x_1` through `x_n`. We can
mirror this for `Γ` by picking `Γ'` to be `Γ, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n`. Since we picked this
change to mirror the one in `σ'`, `Γ' ⊢ σ'` still holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-MoveApp` leaves `R` unchanged, and so we can pick `Ρ` as `Ρ'`. Since `R'` and
`Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: Since we know `e_1 : &r_1 f_1 τ_1 ⊗ ... ⊗ &r_n f_n τ_n → τ_ret`, we know that
`e`, the body of the function and the result of stepping by `E-MoveApp`, is well typed in our `Γ'`.

##### Case `E-Seq`:

From premise:
```
-------------------------- E-Seq
(σ, R, (); e) → (σ, R, e)
```

From premise and knowledge that `e` is of the form `e_1; e_2`, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : unit ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
---------------------------------------- T-Seq
Σ; Δ; Ρ; Γ ⊢ e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

`Γ'` and `Γ' ⊢ σ'`: `E-Seq` leaves `σ` unchanged and so we can pick `Γ'` to be `Γ`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-Seq` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'` and
`Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: We know from the `T-Seq` that `e_2`, our result, is well-typed.

##### Case `E-IfTrue`:

From premise:
```
ƒ ≠ 0
R(ρ) = ƒ ⊗ { ε ↦ true }
------------------------------------------------------ E-IfTrue
(σ, R, if ptr ρ ƒ { e_1 } else { e_2 }) → (σ, R, e_1)
```

From premise and knowledge that `e` is of the form `if e_1 { e_2 } else { e_3 }`:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 bool ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ ⇒ Ρ_2; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_3 : τ ⇒ Ρ_3; Γ_1
;; FIXME: we need to somehow unify Ρ_2 and Ρ_3
;; in particular, τ is not necessarily identical in e_2
;; and e_2, but we should be able to join ρ's in each
-------------------------------------------------------- T-If
Σ; Δ; Ρ; Γ ⊢ if e_1 { e_2 } else { e_3 } : τ ⇒ Ρ'; Γ_1
```

`Γ'` and `Γ' ⊢ σ'`: `E-IfTrue` leaves `σ` unchanged and so we can pick `Γ'` to be `Γ`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-IfTrue` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'`
and `Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: We know from `T-If` that our result from the first branch is well-typed.

##### Case `E-IfFalse`:

From premise:
```
ƒ ≠ 0
R(ρ) = ƒ ⊗ { ε ↦ false }
------------------------------------------------------ E-IfFalse
(σ, R, if ptr ρ ƒ { e_1 } else { e_2 }) → (σ, R, e_2)
```

From premise and knowledge that `e` is of the form `if e_1 { e_2 } else { e_3 }`:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 bool ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : τ ⇒ Ρ_2; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_3 : τ ⇒ Ρ_3; Γ_1
;; FIXME: we need to somehow unify Ρ_2 and Ρ_3
;; in particular, τ is not necessarily identical in e_2
;; and e_2, but we should be able to join ρ's in each
-------------------------------------------------------- T-If
Σ; Δ; Ρ; Γ ⊢ if e_1 { e_2 } else { e_3 } : τ ⇒ Ρ'; Γ_1
```

`Γ'` and `Γ' ⊢ σ'`: `E-IfFalse` leaves `σ` unchanged and so we can pick `Γ'` to be `Γ`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-IfFalse` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'`
and `Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: We know from `T-If` that our result from the second branch is well-typed.

##### Case `E-ForArray`:

From premise:
```
R(ρ_1) = ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
ƒ_1 ≠ 0
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
------------------------------------------------------------------------------- E-ForArray
(σ, R, for μ x in (ptr ρ_1 ƒ_1) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_0 ƒ_ε_0; e_2); ...
         (let μ x = ptr ρ_ε_n-1 ƒ_ε_n-1; e_2); ())
```

From premise and knowledge that `e` is of the form `for μ x in e_1 { e_2 }`, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ imm r_1    f_1 ≠ 0
Ρ(r_1) = τ_1 ⊗ f_1 ⊗ path_set_1
fresh ρ
f_1 / 2 ↓ f_n
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ f_n ⊗ path_set_1, ρ ↦ τ ⊗ f_n ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
--------------------------------------------------------------------- T-ForImm
Σ; Δ; Ρ; Γ ⊢ for imm x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ mut r_1
Ρ(r_1) = τ_1 ⊗ 1 ⊗ path_set_1
fresh ρ
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ 0 ⊗ path_set_1, ρ ↦ τ ⊗ 1 ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
----------------------------------------------------------------- T-ForMut
Σ; Δ; Ρ; Γ ⊢ for mut x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1
```

It's also useful here to see:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

`Γ'` and `Γ' ⊢ σ'`: `E-ForArray` leaves `σ` unchanged and so we can pick `Γ'` to be `Γ`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-ForArray` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'`
and `Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: We have to consider each case separately, though they are quite similar. In
`T-ForImm`, `Ρ ⊢ imm r_1` tells us that the subregions all have non-zero capabilities. This means
that the parameters to each of the let bindings in `e'` are well typed. Then, we also know that
`e_2` is well-typed if `x` is bound which is happening in the let binding as well. The same process
is repeated for `T-ForMut`, but we instead know that all the capabilities are one.

##### Case `E-ForSlice`:

From premise:
```
;; using an ε path here resolves the slice to its backing array
R(ρ_1)(ε) = ρ_ε ↦ ƒ_1 ⊗ { [0] ↦ ρ_ε_0, ..., [n-1] ↦ ρ_ε_n-1 }
ƒ_1 ≠ 0
R(ρ_ε_0) = ƒ_ε_0 ⊗ path_set_0
...
R(ρ_ε_n-1) = ƒ_ε_n-1 ⊗ path_set_n-1
---------------------------------------------------------------- E-ForSlice
(σ, R, for μ x in (fatptr ρ_1 ƒ_1 n_1 n_2) { e_2 }) →
  (σ, R, (let μ x = ptr ρ_ε_n_1 ƒ_ε_n_1; e_2); ...
         (let μ x = ptr ρ_ε_n_2 ƒ_ε_n_2; e_2); ())
```

From premise and knowledge that `e` is of the form `for μ x in e_1 { e_2 }`, either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ imm r_1    f_1 ≠ 0
Ρ(r_1) = τ_1 ⊗ f_1 ⊗ path_set_1
fresh ρ
f_1 / 2 ↓ f_n
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ f_n ⊗ path_set_1, ρ ↦ τ ⊗ f_n ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
--------------------------------------------------------------------- T-ForImm
Σ; Δ; Ρ; Γ ⊢ for imm x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
τ_1 ~ [τ; n] ∨ τ_1 ~ [τ]
Ρ ⊢ mut r_1
Ρ(r_1) = τ_1 ⊗ 1 ⊗ path_set_1
fresh ρ
Ρ' ≝ Ρ_1, r_1 ↦ τ_1 ⊗ 0 ⊗ path_set_1, ρ ↦ τ ⊗ 1 ⊗ { ε ↦ r_1 }
Σ; Δ; Ρ'; Γ, x ↦ ρ ⊢ e_2 : unit ⇒ Ρ'; Γ
----------------------------------------------------------------- T-ForMut
Σ; Δ; Ρ; Γ ⊢ for mut x in e_1 { e_2 } : unit ⇒ Ρ'; Γ_1
```

It's also useful here to see:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 f_1 τ_1 ⇒ Ρ_1; Γ_1
f_1 ≠ 0
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetImm
Σ; Δ; Ρ; Γ ⊢ let imm x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2

Σ; Δ; Ρ; Γ ⊢ e_1 : &r_1 1 τ_1 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x : τ_1 ↦ r_1 ⊢ e_2 : τ_2 ⇒ Ρ_2; Γ_2
r_1 ∉ dom(Ρ_2)
----------------------------------------------------------- T-LetMut
Σ; Δ; Ρ; Γ ⊢ let mut x: τ_1 = e_1; e_2 : τ_2 ⇒ Ρ_2; Γ_2
```

`Γ'` and `Γ' ⊢ σ'`: `E-ForSlice` leaves `σ` unchanged and so we can pick `Γ'` to be `Γ`. Since `σ'`
and `Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-ForSlice` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'`
and `Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: We have to consider each case separately, though they are quite similar. In
`T-ForImm`, `Ρ ⊢ imm r_1` tells us that the subregions all have non-zero capabilities. This means
that the parameters to each of the let bindings in `e'` are well typed. Then, we also know that
`e_2` is well-typed if `x` is bound which is happening in the let binding as well. The same process
is repeated for `T-ForMut`, but we instead know that all the capabilities are one.

##### Case `E-LetTup`:

From premise:
```
--------------------------------------------------------------------------------------- E-LetTup
(σ, R, let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = (ptr ρ_1 1, ..., ptr ρ_n 1); e)
  → (σ ∪ { x_1 ↦ ρ_1, ..., x_n ↦ ρ_n }, R, e)
```

From premise and knowledge that `e` is of the form `let (μ x, ..., μ x): τ ⊗ ... ⊗ τ = e_1; e_2`,
either:
```
Σ; Δ; Ρ; Γ ⊢ e_1 : (&r_1 1 τ_1 ⊗ ... ⊗ &r_n 1 τ_n) ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1, x_1 ↦ r_1, ... x_n ↦ r_n ⊢ e_2 : t_r ⇒ Ρ_2; Γ_2
r ∉ dom(Ρ_2)
----------------------------------------------------------------------- T-LetTup
Σ; Δ; Ρ; Γ ⊢ let (μ_1 x_1, ..., μ_n x_n): τ_1 ⊗ ... ⊗ τ_n = e_1; e_2
           : τ_r ⇒ Ρ_2; Γ_2
```

`Γ'` and `Γ' ⊢ σ'`: `E-LetTup`, like `E-App`, adds bindings for `x_1` through `x_n` to `σ`. We can
mirror this by picking `Γ'` to be `Γ, x_1 ↦ ρ_1, ..., x_n ↦ ρ_n`. Since we picked this change to
mirror the one in `σ'`, `Γ' ⊢ σ'` still holds.

`Ρ'` and `Ρ' ⊢ R'`: `E-LetTup` leaves `R` unchanged and so we can pick `Ρ'` to be `Ρ`. Since `R'`
and `Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: We know from `T-LetTup` that `e_2`, our result, is well-typed with the changes
we made in `Γ'` (i.e. adding bindings for `x_1` through `x_n`).

##### Case `E-TApp`:

From premise:
```
------------------------------------------ E-TApp
(σ, R, (Λς: κ. e) [χ]) → (σ, R, e[χ / ς])
```

From premise and knowledge that `e` is of the form `e [χ]`, either:
```
Σ; Δ; Ρ; Γ ⊢ e : ∀ς: κ. τ ⇒ Ρ'; Γ'
Δ ⊢ χ : κ
χ ~ f ⇒ χ ≠ 0
---------------------------------------- T-TApp
Σ; Δ; Ρ; Γ ⊢ e [χ] : τ[χ / ς] ⇒ Ρ'; Γ'
```

`Γ'` and `Γ' ⊢ σ'`: `E-TApp` leaves `σ` unchanged, and so we can pick `Γ'` to be `Γ`. Since `σ'` and
`Γ'` are both unchanged, `Γ ⊢ σ` gives us `Γ' ⊢ σ'`.

`Ρ'` and `Ρ' ⊢ R'`: `E-TApp` leaves `R` unchanged, and so we can pick `Ρ'` to be `Ρ`. Since `R'` and
`Ρ'` are both unchanged, `Ρ ⊢ R` gives us `Ρ' ⊢ R'`.

`e'` is well-typed: Since we left `Γ'` and `Ρ'` unchanged, we still know from our premise that our
result is well-typed.

[˄ Back to top][toc]

## A less minimal Oxide0

`Oxide0` as described throughout this document is still a very minimal language, and lacks many of
the operations we need to write meaningful programs. The following presents some extensions to the
language that make it closer to a "real" language. Notably, we continue to replicate the pattern of
using every value behind a reference type so that it is packaged with its capability.

### Syntax

```
unary operators unop ::= ! | -
binary operators bop ::= + | * | == | != | && | ||

expressions e ::= ...
                | e_1 bop e_2
                | unop e
```

### Statics

```
binop ∈ { +, * }
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_1 1 u32 ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &ρ_2 1 u32 ⇒ Ρ_2; Γ_2
fresh ρ
---------------------------------------------------- T-AddMul
Σ; Δ; Ρ; Γ ⊢ e_1 binop e_2 : &ρ 1 u32
           ⇒ Ρ_2, ρ ↦ u32 ⊗ 1 ⊗ { ε ↦ u32 }; Γ_2

binop ∈ { ==, != }
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_1 1 τ ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &ρ_2 1 τ ⇒ Ρ_2; Γ_2
fresh ρ
------------------------------------------------------ T-EqNotEq
Σ; Δ; Ρ; Γ ⊢ e_1 binop e_2 : &ρ 1 bool
           ⇒ Ρ_2, ρ ↦ bool ⊗ 1 ⊗ { ε ↦ bool }; Γ_2

binop ∈ { &&, || }
Σ; Δ; Ρ; Γ ⊢ e_1 : &ρ_1 1 bool ⇒ Ρ_1; Γ_1
Σ; Δ; Ρ_1; Γ_1 ⊢ e_2 : &ρ_2 1 bool ⇒ Ρ_2; Γ_2
fresh ρ
------------------------------------------------------ T-AndOr
Σ; Δ; Ρ; Γ ⊢ e_1 binop e_2 : &ρ 1 bool
           ⇒ Ρ_2, ρ ↦ bool ⊗ 1 ⊗ { ε ↦ bool }; Γ_2

Σ; Δ; Ρ; Γ ⊢ e : &ρ_1 1 bool ⇒ Ρ'; Γ'
fresh ρ
--------------------------------------------------- T-Not
Σ; Δ; Ρ; Γ ⊢ ! e : &ρ 1 bool
           ⇒ Ρ', ρ ↦ bool ⊗ 1 ⊗ { ε ↦ bool }; Γ'

Σ; Δ; Ρ; Γ ⊢ e : &ρ_1 1 u32 ⇒ Ρ'; Γ'
fresh ρ
------------------------------------------------- T-Neg
Σ; Δ; Ρ; Γ ⊢ ! e : &ρ 1 u32
           ⇒ Ρ', ρ ↦ u32 ⊗ 1 ⊗ { ε ↦ u32 }; Γ'
```

[˄ Back to top][toc]

[toc]: #table-of-contents
