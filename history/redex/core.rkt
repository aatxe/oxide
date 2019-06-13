#lang racket/base

(require redex
         redex-chk)

(define-language Core
  ;; expressions
  (e ::=
     ;; functions
     (λ (x t) e)
     ;; application
     (e e)
     ;; identifiers
     x
     ;; branching
     (if e e e)

     ;; products
     (tup e ...)
     ;; product projection (proj n (tup ...))
     (proj e e)

     ;; sums
     (inl e)
     (inr e)
     ;; sum elimination
     (case e (inl x e) (inr x e))

     ;; base values
     number
     true
     false

     ;; primitive ops
     (+ e e)
     (= e e)
     (- e)
     (∧ e e)
     (∨ e e)
     (¬ e)

     #:binding-forms
     (λ (x t) e #:refers-to x))

  ;; types
  (t ::=
     (→ t t)
     (tup t ...)
     num
     bool)

  (x ::= variable-not-otherwise-mentioned))

;; syntactic tests
(redex-chk
 #:lang Core
 #:f #:m e (λ (x) x)
 #:m e (λ (x (tup)) x)
 #:m e (tup)
 #:m e (inl (tup))
 #:m e (inr (tup))
 #:m e (case (inl (tup))
         (inl x x)
         (inr x x))
 #:m e (if (∨ (= 0 x) (= 255 x))
         (λ (x num) x)
         (λ (x num) (+ x 1))))

(define-extended-language Core-Ev Core
  (E ::=
     ;; application
     (v E)
     (E e)
     ;; branching
     (if E e e)

     ;; products
     (tup v ... E e ...)
     ;; product projection
     (proj E e)
     (proj v E)

     ;; sums
     (inl E)
     (inr E)
     ;; sum elimination
     (case E (inl x e) (inr x e))

     ;; primitive ops
     (+ v E)
     (+ E e)
     (= v E)
     (= E e)
     (- E)
     (∧ v E)
     (∧ E e)
     (∨ v E)
     (∨ E e)
     (¬ E)

     hole)

  (n ::= number)
  (b ::=
     true
     false)

  (v ::=
     (λ (x t) e)
     (tup v ...)
     (inl v)
     (inr v)
     number
     true
     false))

(define-metafunction Core-Ev
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction Core-Ev
  negative : number -> number
  [(negative number) ,(- (term number))])

(define-metafunction Core-Ev
  project : number v -> v
  [(project number (tup v ...)) ,(list-ref (term (v ...)) (- (term number) 1))])

(redex-chk
 (project 2 (tup 1 2 3 4)) 2
 (project 3 (tup 1 2 3)) 3)

(define -->Core
  (reduction-relation
   Core-Ev
   #:domain e

   (--> (in-hole E ((λ (x t) e) v))
        (in-hole E (substitute e x v))
        "E-App")

   (--> (in-hole E (if true e_1 e_2))
        (in-hole E e_1)
        "E-IfTrue")
   (--> (in-hole E (if false e_1 e_2))
        (in-hole E e_2)
        "E-IfFalse")

   (--> (in-hole E (proj n (tup v ...)))
        (in-hole E (project n (tup v ...)))
        "E-ProjN")

   (--> (in-hole E (case (inl v) (inl x_1 e_1) (inr x_2 e_2)))
        (in-hole E (substitute e_1 x_1 v))
        "E-CaseInl")
   (--> (in-hole E (case (inr v) (inl x_1 e_1) (inr x_2 e_2)))
        (in-hole E (substitute e_2 x_2 v))
        "E-CaseInr")

   (--> (in-hole E (+ n_1 n_2))
        (in-hole E (Σ n_1 n_2))
        "E-Add")
   (--> (in-hole E (= v v))
        (in-hole E true)
        "E-EqTrue")
   (--> (in-hole E (= v_!_1 v_!_1))
        (in-hole E false)
        "E-EqFalse")
   (--> (in-hole E (- n))
        (in-hole E (negative n))
        "E-Negative")

   (--> (in-hole E (∧ true true))
        (in-hole E true)
        "E-TrueAndTrue")
   (--> (in-hole E (∧ false b))
        (in-hole E false)
        "E-FalseAnd")
   (--> (in-hole E (∧ true false))
        (in-hole E false)
        "E-TrueAndFalse")
   (--> (in-hole E (∨ true b))
        (in-hole E true)
        "E-TrueOr")
   (--> (in-hole E (∨ false true))
        (in-hole E true)
        "E-FalseOrTrue")
   (--> (in-hole E (∨ false false))
        (in-hole E false)
        "E-FalseOrFalse")
   (--> (in-hole E (¬ true))
        (in-hole E false)
        "E-NegTrue")
   (--> (in-hole E (¬ false))
        (in-hole E true)
        "E-NegFalse")))

(define-metafunction Core-Ev
  eval : e -> v
  [(eval e) ,(car (apply-reduction-relation* -->Core (term e)))])

(redex-chk
 (eval (∧ true true)) true
 (eval ((λ (x num) (+ 1 x)) 3)) 4
 (eval ((λ (x bool) (if x 1 0)) true)) 1
 (eval (proj 2 (tup (if true 1 2) (if false 1 3)))) 3
 (eval (case (inl (+ 1 1)) (inl x (+ x 1)) (inr x (+ x 2)))) 3
 (eval (case (inr (+ 1 1)) (inl x (+ x 1)) (inr x (+ x 2)))) 4)
