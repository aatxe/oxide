#lang racket/base

(require redex)

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

     ;; base values
     unit
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
     unit
     num
     bool)

  (x ::= variable-not-otherwise-mentioned))

;; syntactic tests
(test-equal (redex-match Core e (term (λ (x) x)))
            #f)
(test-equal (length (redex-match Core e (term (λ (x unit) x))))
            1)
(test-equal (length (redex-match Core e (term
                                         (if (∨ (= 0 x) (= 255 x))
                                             (λ (x num) x)
                                             (λ (x num) (+ x 1))))))
            1)
