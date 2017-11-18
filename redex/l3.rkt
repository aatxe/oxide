#lang racket/base

(require redex
         redex-chk)

(define-language L3
  ;; locations
  (η ::=
     ;; concrete locations (not in source program)
     l
     ;; location variables
     ρ)

  (τ ::=
     unit
     ;; tensor product
     (tensor τ τ)
     ;; linear function
     (lolipop τ τ)

     ;; of-course (non-linear) type
     (! τ)
     ;; pointer type
     (ptr τ)
     ;; capability type
     (cap η τ)

     ;; universal for location variables
     (∀ ρ τ)
     ;; existential for location variables
     (∃ ρ τ))

  (e ::=
     ;; unit
     ()
     ;; destructing let for unit
     (let () = e in e)

     ;; tensor product
     (prod e e)
     ;; destructuring let for products
     (let (prod x x) = e in e)

     ;; variables
     x
     ;; functions
     (λ x e)
     ;; function application
     (e e)

     ;; of-course values
     (! v)
     ;; destructuring let for of-course values
     (let (! x) = e in e)
     ;; weaking for of-course values
     (dup e)
     ;; contraction for of-course values
     (drop e)

     ;; pointer to location l
     (ptr l)
     ;; capability to use location l
     (cap l)
     ;; allocate new e
     (new e)
     ;; de-allocate e
     (free e)
     ;; swap a value into the heap
     (swap e e)

     ;; location abstraction
     (Λ ρ e)
     ;; location application
     (e [η])
     ;; pack with location
     (pack η e)
     ;; unpack
     (let (pack ρ x) = e in e))

  (v ::=
     ;; unit
     ()
     ;; products of values
     (prod v v)
     ;; variables
     x
     ;; functions
     (λ x e)
     ;; of-course values
     (! v)
     ;; pointers
     (ptr l)
     ;; capabilities
     (cap l)
     ;; location abstraction
     (Λ ρ e)
     ;; pack with location
     (pack η v))

  ;; variables
  (x ::= variable-not-otherwise-mentioned)
  ;; concrete locations
  (l ::= variable-not-otherwise-mentioned)
  ;; location variables
  (ρ ::= variable-not-otherwise-mentioned))

(define-extended-language L3-dynamics L3
  ;; stores
  (σ ::= (env (l v) ...))

  ;; evaluation contexts
  (E ::=
     ;; destructing let for unit
     (let () = E in e)

     ;; tensor product
     (prod E e)
     (prod v E)
     ;; destructuring let for products
     (let (prod x x) = E in e)

     ;; function application
     (E e)
     (v E)

     ;; destructuring let for of-course values
     (let (! x) = E in e)
     ;; weaking for of-course values
     (dup E)
     ;; contraction for of-course values
     (drop E)

     ;; allocate new e
     (new E)
     ;; de-allocate e
     (free E)
     ;; swap a value into the heap
     (swap E e)
     (swap v E)

     ;; location application
     (E [η])
     ;; pack with location
     (pack η E)
     ;; unpack
     (let (pack ρ x) = E in e)))
