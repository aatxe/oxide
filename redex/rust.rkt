#lang racket/base

(require redex
         redex-chk)

(define-language Rust0
  ;; programs
  (prog ::= (tls ...))

  ;; top-level statements
  (tls ::=
       (struct sid [(lft ι) ... α ...] {(x t) ...})
       (enum sid [(lft ι) ... α ...] {(vid t ...) ...})
       (fn f [(lft ι) ... α ...] ((x t) ...) { st ... }))

  ;; statements
  (st ::=
      ;; let bindings (immutable and mutable)
      (let (lv t) = rv)
      (let mut (lv t) = rv)
      ;; assignment (only for mutable bindings)
      (lv := rv)

      ;; expressions (rvalues)
      rv)

  ;; lvalues (expressions that can appear on the left-side of a binding or assignment)
  (lv ::=
      ;; variable
      x
      ;; pointer dereference
      (* lv)
      ;; lvalue products
      (tup lv ...))

  ;; rvalues (expressions)
  (rv ::=
      ;; all lvalues
      lv
      ;; branching
      (if rv rv rv)
      ;; rvalue products
      (tup rv ...)
      ;; tuple projection (and also probably struct projection)
      (proj rv rv)
      ;; enum variant construction
      (vid rv ...)

      ;; function calls
      (f [(lft ι) ... t ...] (rv ...))
      ;; blocks (sequence of statements, takes value of last statement)
      (block st ...)
      ;; pattern matching
      (match rv {(pat => rv) ...})

      ;; base values
      const

      ;; abort (errors) -- in real Rust, there's multiple options here with messages, etc.
      (abort!)

      ;; operations
      (rv binop rv)
      (unop rv))

  ;; constants
  (const ::=
         number
         true
         false)

  ;; patterns
  (pat ::=
       ;; wildcard pattern
       _
       ;; variable pattern
       x
       ;; enum variant pattern
       (sid pat ...)
       ;; tuple pattern
       (tup pat ...)
       ;; reference pattern
       (ref pat))

  ;; operators
  (binop ::= + = ∧ ∨)
  (unop ::= - ¬)

  ;; types
  (t ::=
     ;; type variables
     α
     ;; references (&'a t)
     (ref ι t)
     ;; tuple types
     (tup t ...)

     ;; struct and enum names
     sid
     ;; type application
     (t t)

     ;; base types
     num
     bool)

  ;; values
  (v ::=
     ;; constants
     const
     ;; tuples of values
     (tup v ...)
     ;; enum variants of values
     (vid v ...))

  ;; shorthand for numbers
  (n ::= number)

  ;; variables
  (x ::= variable-not-otherwise-mentioned)
  ;; type variables
  (α ::= variable-not-otherwise-mentioned)
  ;; lifetime variables
  (ι ::= variable-not-otherwise-mentioned)
  ;; function identifiers
  (f ::= variable-not-otherwise-mentioned)
  ;; struct and enum identifiers
  (sid ::= variable-not-otherwise-mentioned)
  ;; enum variant identifiers
  (vid ::= variable-not-otherwise-mentioned))

;; syntax tests
(redex-chk
 #:lang Rust0

 ;; valid programs
 #:m prog ((enum Option [T] { (None) (Some T) })
           (fn unwrap [T] ((opt (Option T))) { (match opt { ((Option::None) => (abort!))
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

(define-extended-language Rust0-Machine Rust0
  ;; flags indicating variable mutability in environment
  (flag ::=
        imm
        mut)

  ;; control strings (· or single statements)
  (c ::=
     ·
     st)

  ;; control values
  (cv ::=
      ·
      v)

  ;; variable environment
  (ρ ::= (env (flag x v) ...))

  ;; continuations
  (κ ::=
     ;; halt
     halt
     ;; special start continuation indicating main should be called
     start
     ;; function call continuation
     (fun x st ρ κ)
     ;; continuation representing a block of statements to execute before continuing to κ
     (block st ... κ))

  ;; evaluation contexts
  (E ::=
     ;; top-level evaluation contexts (format: CEK + prog)
     (exec E ρ κ prog)

     ;; other evaluation contexts
     hole
     (let (lv t) = E)
     (let mut (lv t) = E)
     (lv := E)

     ;; enum variants
     (vid v ... E e ...)

     ;; function calls
     (f [(lft ι) ... t ...] (v ... E rv ...))

     ;; simple evaluation contextx (from core.rkt)

     ;; branching
     (if E rv rv)

     ;; products
     (tup v ... E rv ...)
     ;; product projection
     (proj E rv)
     (proj v E)

     ;; primitive ops
     (v + E)
     (E + rv)
     (v = E)
     (E = rv)
     (- E)
     (v ∧ E)
     (E ∧ rv)
     (v ∨ E)
     (E ∨ rv)
     (¬ E)))

(define -->Rust0
  (reduction-relation
   Rust0-Machine

   (--> (exec · ρ start prog)
        (exec st_0 ρ (block st_1 ... halt) prog)
        (where (fn main [] () { st_0 st_1 ... }) (lookup-fn prog main))
        "E-StartMain")
   (--> (exec v ρ halt prog)
        v
        "E-HaltProgram")

   (--> (exec (let (x_1 t) = v_1) (env (flag x v) ...) κ prog)
        (exec (tup) (env (imm x_1 v_1)(flag x v) ...) κ prog)
        "E-ImmBinding")
   (--> (exec (let mut (x_1 t) = v_1) (env (flag x v) ...) κ prog)
        (exec (tup) (env (mut x_1 v_1)(flag x v) ...) κ prog)
        "E-MutBinding")
   (--> (exec (x_t := v_t) (env (flag_1 x_1 v_1) ... (mut x_t v_old) (flag_2 x_2 v_2) ...) κ prog)
        (exec (tup) (env (flag_1 x_1 v_1) ... (mut x_t v_t) (flag_2 x_2 v_2) ...) κ prog)
        "E-Assign")

   (--> (exec (in-hole E x) (env (flag_1 x_1 v_1) ... (flag x v) (flag_2 x_2 v_2) ...) κ prog)
        (exec (in-hole E v) (env (flag_1 x_1 v_1) ... (flag x v) (flag_2 x_2 v_2) ...) κ prog)
        "E-Id")

   (--> (exec (in-hole E (f [] (v ...))) ρ κ prog)
        (exec st_0 (env (imm x v) ...) (block st_1 ... (fun x_f (in-hole E x_f) ρ κ)) prog)
        (where (fn f [] ((x t) ...) { st_0 st_1 ... }) (lookup-fn prog f))
        (fresh x_f)
        "E-App")
   (--> (exec v_1 _ (fun x_1 st (env (flag_2 x_2 v_2) ...) κ) prog)
        (exec st (env (imm x_1 v_1) (flag_2 x_2 v_2) ...) κ prog)
        "E-Return")

   (--> (exec (block st ...) ρ κ prog)
        (exec · ρ (block st ... κ) prog)
        "E-StartBlock")
   (--> (exec cv ρ (block st_0 st_1 ... κ) prog)
        (exec st_0 ρ (block st_1 ... κ) prog)
        "E-AdvanceBlock")
   (--> (exec cv ρ (block κ) prog)
        (exec cv ρ κ prog)
        "E-EndBlock")

   (--> (exec (in-hole E abort!) ρ κ prog)
        (exec (abort!) ρ (halt) prog)
        "E-Abort")

   ;; rules for evaluating rvalues that are simple expressions (as in core.rkt)
   (--> (in-hole E (if true rv_1 rv_2))
        (in-hole E rv_1)
        "E-IfTrue")
   (--> (in-hole E (if false rv_1 rv_2))
        (in-hole E rv_2)
        "E-IfFalse")

   (--> (in-hole E (proj n (tup v ...)))
        (in-hole E (project n (tup v ...)))
        "E-ProjNTup")
   (--> (in-hole E (proj n (vid v ...)))
        (in-hole E (project n (vid v ...)))
        "E-ProjNEnumVariant")

   (--> (in-hole E (n_1 + n_2))
        (in-hole E (Σ n_1 n_2))
        "E-Add")
   (--> (in-hole E (v = v))
        (in-hole E true)
        "E-EqTrue")
   (--> (in-hole E (v_!_1 = v_!_1))
        (in-hole E false)
        "E-EqFalse")
   (--> (in-hole E (- n))
        (in-hole E (negative n))
        "E-Negative")

   (--> (in-hole E (true ∧ true))
        (in-hole E true)
        "E-TrueAndTrue")
   (--> (in-hole E (false ∧ b))
        (in-hole E false)
        "E-FalseAnd")
   (--> (in-hole E (true ∧ false))
        (in-hole E false)
        "E-TrueAndFalse")
  (--> (in-hole E (true ∨ b))
        (in-hole E true)
        "E-TrueOr")
   (--> (in-hole E (false ∨ true))
        (in-hole E true)
        "E-FalseOrTrue")
   (--> (in-hole E (false ∨ false))
        (in-hole E false)
        "E-FalseOrFalse")
   (--> (in-hole E (¬ true))
        (in-hole E false)
        "E-NegTrue")
   (--> (in-hole E (¬ false))
        (in-hole E true)
        "E-NegFalse")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rust0-Machine metafunctions ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction Rust0-Machine
  lookup-fn : prog f -> tls
  [(lookup-fn (_ ... (fn f_0 [(lft ι) ... α ...] ((x t) ...) { st ... }) _ ...) f_0)
   (fn f_0 [(lft ι) ... α ...] ((x t) ...) { st ... })]
  [(lookup-fn prog f) ,(error "lookup-fn: function with name not found:" (term f))])

(define-metafunction Rust0-Machine
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction Rust0-Machine
  negative : number -> number
  [(negative number) ,(- (term number))])

(define-metafunction Rust0-Machine
  project : number v -> v
  [(project number (tup v ...)) ,(list-ref (term (v ...)) (- (term number) 1))])

(define-metafunction Rust0-Machine
  eval : prog -> any
  [(eval prog) ,(car (apply-reduction-relation* -->Rust0 (term (exec · (env) start prog))))])

(redex-chk
 (eval ((fn main [] () { (let mut (x num) = (1 + 2)) (x := 6) (1 + x) }))) 7
 (eval ((fn main [] () { (block (3 + 3) (4 + 4) (5 + 5)) }))) 10

 (eval ((fn main [] () { (sum_to [] ((2 + 3))) })
        (fn sum_to [] ((x num)) { (if (x = 0)
                                     0
                                     (x + (sum_to [] ((x + -1))))) }))) 15)
