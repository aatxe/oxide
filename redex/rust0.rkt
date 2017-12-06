#lang racket/base

(require redex
         redex-chk
         racket/list)

(define-language Rust0
  ;; programs
  (prog ::= (tls ...))

  ;; top-level statements
  (tls ::=
       (struct sid [(lft ι) ... T ...] {(x t) ...})
       (enum sid [(lft ι) ... T ...] {(vid t ...) ...})
       (fn f [(lft ι) ... T ...] ((x t) ...) { st ... }))

  ;; statements
  (st ::=
      ;; let bindings (immutable and mutable)
      (let (pat t) = e)
      (let mut (pat t) = e)
      ;; assignment (only for mutable bindings)
      (lv := e)

      ;; expressions
      e)

  ;; lvalues - expressions that can appear on the left-side of an assignment
  (lv ::=
      ;; variable
      x
      ;; pointer dereference
      (deref lv)
      ;; projecting a field from a struct variable
      (proj x x)
      ;; lvalue products
      (tup lv ...))

  ;; expressions
  (e ::=
     ;; variables
     x
     ;; branching
     (if e e e)
     ;; tuples
     (tup e ...)
     ;; project the first arg from the second arg
     (proj e e)
     ;; named tuple - a kind of struct and enum variant
     (sid e ...)
     ;; named record - a kind of struct and enum variant
     (sid {(x e) ...})

     ;; function calls
     (f [(lft ι) ... t ...] (e ...))
     ;; blocks - sequence of statements, takes value of last statement which is unit if not an expression
     (block st ...)
     ;; pattern matching
     (match rv {(pat => e) ...})

     ;; base values
     const
     ;; references
     (ref ι e)

     ;; abort (errors) -- in real Rust, there's multiple options here with messages, etc.
     (abort!)

     ;; operations
     (e binop e)
     (unop e))

  ;; constants
  (const ::=
         number
         true
         false)

  ;; patterns
  (pat ::=
       ;; wildcard pattern
       underscore
       ;; variable pattern
       x
       ;; tuple pattern
       (tup pat ...)
       ;; named tuple pattern
       (sid pat ...)
       ;; named record pattern
       (sid {(x pat) ...})
       ;; reference pattern
       (ref pat))

  ;; operators
  (binop ::= + = ∧ ∨)
  (unop ::= deref - ¬)

  ;; types
  (t ::=
     ;; type variables
     T
     ;; references (&'a t)
     (ref ι t)
     ;; tuple types
     (tup t ...)

     ;; struct and enum names
     sid
     ;; type application e.g. (Option [num])
     (t [t])

     ;; function types - universally quantified, multi-argument functions
     (fn [ι ... T ...] (t ...) -> t)

     ;; base types
     num
     bool)

  ;; shorthand for numbers
  (n ::= number)

  ;; variables
  (x ::= variable-not-otherwise-mentioned)
  ;; type variables
  (T ::= variable-not-otherwise-mentioned)
  ;; lifetime variables
  (ι ::= variable-not-otherwise-mentioned)
  ;; function identifiers
  (f ::= variable-not-otherwise-mentioned)
  ;; struct and enum identifiers
  (sid ::= variable-not-otherwise-mentioned))
