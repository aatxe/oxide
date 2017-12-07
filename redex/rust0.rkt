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
       (enum sid [(lft ι) ... T ...] {dt ...})
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

  ;; data structures - struct and variant kinds
  (d ::=
     ;; named tuple - a kind of struct and enum variant
     (sid e ...)
     ;; named record - a kind of struct and enum variant
     (sid {(x e) ...}))

  ;; data structure typeforms - struct and variant kinds with types
  ;; n.b. these are not an actual kind of type, but are used in definitions
  (dt ::=
      (sid t ...)
      (sid {(x t) ...}))

  ;; expressions
  (e ::=
     ;; variables
     x
     ;; branching
     (if e e e)
     ;; tuples
     (tup e ...)
     ;; data structures
     d
     ;; project the first arg from the second arg
     (proj e e)

     ;; function calls
     (f [(lft ι) ... t ...] (e ...))
     ;; blocks - sequence of statements, takes value of last expression or unit if statement
     (block st ...)
     ;; pattern matching
     (match e {(pat => e) ...})

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

;; syntax tests
(redex-chk
 #:lang Rust0

 ;; valid programs
 #:m prog ((enum Option [T] { (None) (Some T) })
           (fn unwrap [T] ((opt (Option [T]))) { (match opt { ((Option::None) => (abort!))
                                                            ((Option::Some x) => x) }) }))
 #:m prog ((fn main [] () { (tup) }))

 ;; valid top-level statements
 #:m tls (struct Point [] { (x num)
                            (y num) })
 #:m tls (struct Ref [(lft α) T] { (inner (ref α T)) })
 #:m tls (enum Option [T] { (None)
                            (Some T) })
 #:m tls (enum WeirdOption [T] { (None)
                                 (Some T)
                                 (Double T T) })
 #:m tls (fn main [] () { (tup) (tup) (tup) })
 #:m tls (fn main [] () { (let [(tup x y) (tup num num)] = (tup 1 2)) })
 #:m tls (fn sum_to [] ((x num)) { (if (x = 0)
                                       1
                                       (x + (sum_to [] ((x + -1))))) })

 ;; invalid top-level statements
 #:f #:m tls (fn main [] () { (let [(tup 1 2) (tup num num)] = (tup 3 4)) }))
