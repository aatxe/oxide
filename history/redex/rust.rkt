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
      (let (pat t) = rv)
      (let mut (pat t) = rv)
      ;; assignment (only for mutable bindings)
      (lv := rv)

      ;; expressions (rvalues)
      rv)

  ;; lvalues (expressions that can appear on the left-side of a binding or assignment)
  (lv ::=
      ;; variable
      x
      ;; pointer dereference
      (deref lv)
      ;; projecting a field from a struct variable
      (proj x x)
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
      ;; struct construction
      (sid {(x rv) ...})

      ;; function calls
      (f [(lft ι) ... t ...] (rv ...))
      ;; blocks (sequence of statements, takes value of last statement)
      (block st ...)
      ;; pattern matching
      (match rv {(pat => rv) ...})

      ;; base values
      const
      ;; references
      (ref ι rv)

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
       underscore
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
     ;; type application
     (t t)

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

  ;; base values
  (bv ::=
     ;; constants
     const
     ;; pointer to an address (runtime value for references)
     (ptr α)
     ;; tuples of addresses (pointing to values)
     (tup α ...)
     ;; enum variants of addresses
     (vid α ...)
     ;; runtime struct values
     (sid {(x α) ...}))

  (v ::=
     ;; bare address (used in pattern matching and stuff)
     α
     ;; base values
     bv)

  ;; control values (normal values with indirection removed + abort + ·)
  (cv ::=
      ·
      (abort!)
      (ptr α)
      const
      (tup cv ...)
      (vid cv ...)
      (sid {(x cv) ...}))

  ;; addresses
  (α ::= variable-not-otherwise-mentioned)

  ;; variable environment
  (ρ ::= (env (flag x α) ...))
  (ψ ::= (mem (α v) ...))

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
     ;; top-level evaluation contexts (format: control string, variable-to-address map, mem, call stack, whole program)
     (exec E ρ ψ κ prog)

     ;; other evaluation contexts
     hole
     (let (pat t) = E)
     (let mut (pat t) = E)
     (lv := E)

     ;; enum variants
     (vid v ... E rv ...)
     ;; struct instances
     (sid {(x v) ... (x E) (x rv) ...})

     ;; function calls
     (f [(lft ι) ... t ...] (v ... E rv ...))
     ;; pattern matching
     (match E {(pat => rv) ...})

     ;; simple evaluation context (from core.rkt)

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
     (¬ E)
     (deref E)))

(define -->Rust0
  (reduction-relation
   Rust0-Machine

   (--> (exec · ρ ψ start prog)
        (exec st_0 ρ ψ (block st_1 ... halt) prog)
        (where (fn main [] () { st_0 st_1 ... }) (lookup-fn prog main))
        "E-StartMain")
   (--> (exec cv ρ ψ halt prog)
        cv
        "E-HaltProgram")

   (--> (exec (let (pat t) = v)
              (env (flag x_e α_e) ...)
              (name ψ (mem (α_m v_m) ...))
              κ prog)
        (exec (tup)
              (env (imm x_n α_n) ... (flag x_e α_e) ...)
              (mem (α_n v_n) ... (α_m v_m) ...)
              κ prog)
        (where ((x_n v_n) ...) (match-pat-or-err pat v ψ))
        (where (α_n ...) ,(variables-not-in (term (x_e ... x_n ... α_e ... α_m ...))
                                            (term (x_n ...))))
        "E-ImmBinding")
   (--> (exec (let mut (pat t) = v)
              (env (flag x_e α_e) ...)
              (name ψ (mem (α_m v_m) ...))
              κ prog)
        (exec (tup)
              (env (mut x_n α_n) ... (flag x_e α_e) ...)
              (mem (α_n v_n) ... (α_m v_m) ...)
              κ prog)
        (where ((x_n v_n) ...) (match-pat-or-err pat v ψ))
        (where (α_n ...) ,(variables-not-in (term (x_e ... x_n ... α_e ... α_m ...))
                                            (term (x_n ...))))
        "E-MutBinding")
   (--> (exec (x_t := v_t)
              (env (flag_1 x_1 α_1) ... (mut x_t α_t) (flag_2 x_2 α_2) ...)
              (mem (α_3 v_3) ... (α_t v_old) (α_4 v_4) ...)
              κ prog)
        (exec (tup)
              (env (flag_1 x_1 α_1) ... (mut x_t α_t) (flag_2 x_2 α_2) ...)
              (mem (α_3 v_3) ... (α_t v_t) (α_4 v_4) ...)
              κ prog)
        "E-AssignId")
   (--> (exec ((deref lv) := v_t)
              ;; NOTE: because we require a mutable binding to appear to this address, we actually
              ;; operationally enforce that you can't mutate through references to immutable things
              ;; we could remove this requirement if we desired by replacing the next line with ρ
              (name ρ (env (flag_1 x_1 α_1) ... (mut x_t α_t) (flag_2 x_2 α_2) ...))
              (name ψ (mem (α_3 v_3) ... (α_t v_old) (α_4 v_4) ...))
              κ prog)
        (exec (tup)
              (env (flag_1 x_1 α_1) ... (mut x_t α_t) (flag_2 x_2 α_2) ...)
              (mem (α_3 v_3) ... (α_t v_t) (α_4 v_4) ...)
              κ prog)
        (where (ptr α_t) (eval-simple-expr-in lv ρ ψ))
        "E-AssignDeref")

   (--> (exec (in-hole E x)
              (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
              (mem (α_3 v_3) ... (α v) (α_4 v_4) ...)
              κ prog)
        (exec (in-hole E v)
              (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
              (mem (α_3 v_3) ... (α v) (α_4 v_4) ...)
              κ prog)
        "E-Id")

   (--> (exec (in-hole E (tup cv_n ...))
              (env (flag x α) ...)
              (mem (α_m v_m) ...)
              κ prog)
        (exec (in-hole E (tup α_n ...))
              (env (flag x α) ...)
              (mem (α_n cv_n) ... (α_m v_m) ...)
              κ prog)
        (where (α_n ...) ,(variables-not-in (term (x ... α ... α_m ... v_m ...))
                                            (map (lambda (x) (gensym)) (term (cv_n ...)))))
        "E-AllocTup")
   (--> (exec (in-hole E (vid cv_n ...))
              (env (flag x α) ...)
              (mem (α_m v_m) ...)
              κ prog)
        (exec (in-hole E (vid α_n ...))
              (env (flag x α) ...)
              (mem (α_n cv_n) ... (α_m v_m) ...)
              κ prog)
        (where (α_n ...) ,(variables-not-in (term (x ... α ... α_m ... v_m ...))
                                            (map (lambda (x) (gensym)) (term (cv_n ...)))))
        "E-AllocEnumVariant")

   (--> (exec (in-hole E (f [any ...] (bv ...))) ρ
              (name ψ (mem (α_m v_m) ...))
              κ prog)
        (exec st_0
              (env (imm x α) ...)
              (mem (α bv) ... (α_m v_m) ...)
              (block st_1 ... (fun x_f (in-hole E x_f) ρ κ)) prog)
        (where (fn f [(lft ι) ... T ...] ((x t) ...) { st_0 st_1 ... })
               (lookup-fn prog f))
        (where _ ,(println (term κ)))
        (where (α ...) ,(variables-not-in (term (x_f x ... bv ... α_m ... v_m ...)) (term (x ...))))
        (fresh x_f)
        "E-App")
   ;; TODO: return should de-allocate memory that is no longer accessible (equivalent of calling drop)
   (--> (exec v_1 _ (mem (α_m v_m) ...) (fun x_1 st (env (flag_2 x_2 α_2) ...) κ) prog)
        (exec st (env (imm x_1 α_1) (flag_2 x_2 α_2) ...) (mem (α_1 v_1) (α_m v_m) ...) κ prog)
        (fresh α_1)
        "E-Return")

   (--> (exec (in-hole E (match bv_match {(pat => rv) ...}))
              (env (flag x α) ...)
              (name ψ (mem (α_m v_m) ...))
              κ prog)
        (exec (in-hole E rv_m)
              (env (imm x_n α_n) ... (flag x α) ...)
              (mem (α_n v_n) ... (α_m v_m) ...)
              κ prog)
        (where (rv_m (x_n v_n) ...) (first-match ψ bv_match ((pat => rv) ...)) )
        (where (α_n ...) ,(variables-not-in (term (α_m ...)) (term (x_n ...))))
        "E-Match")

   (--> (exec (in-hole E (deref (ptr α))) ρ (mem (α_1 v_1) ... (α v) (α_2 v_2) ...) κ prog)
        (exec (in-hole E v) ρ (mem (α_1 v_1) ... (α v) (α_2 v_2) ...) κ prog)
        "E-Deref")
   (--> (exec (in-hole E (ref ι x))
              (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
              ψ κ prog)
        (exec (in-hole E (ptr α))
              (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
              ψ κ prog)
        "E-RefId")

   (--> (exec (block st ...) ρ ψ κ prog)
        (exec · ρ ψ (block st ... κ) prog)
        "E-StartBlock")
   (--> (exec cv ρ ψ (block st_0 st_1 ... κ) prog)
        (exec st_0 ρ ψ (block st_1 ... κ) prog)
        "E-AdvanceBlock")
   (--> (exec cv ρ ψ (block κ) prog)
        (exec cv ρ ψ κ prog)
        "E-EndBlock")

   (--> (exec (in-hole E abort!) ρ ψ κ prog)
        (exec (abort!) ρ ψ κ prog)
        "E-Abort")
   (--> (exec (abort!) ρ ψ κ prog)
        (exec (abort!) ρ ψ halt prog)
        "E-AbortKillsStack")

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
   (--> (in-hole E (proj x_f (sid {(x_1 v_1) ... (x_f v_f) (x_2 v_2) ...})))
        (in-hole E v_f)
        "E-ProjStructField")

   (--> (in-hole E (n_1 + n_2))
        (in-hole E (Σ n_1 n_2))
        "E-Add")
   (--> (in-hole E (bv = bv))
        (in-hole E true)
        "E-EqTrue")
   (--> (in-hole E (bv_!_1 = bv_!_1))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions for metafunctions ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (group n lst)
  (if (empty? lst)
      '()
      (cons (take lst n) (group n (drop lst n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rust0-Machine metafunctions ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-metafunction Rust0-Machine
  lookup-fn : prog f -> tls
  [(lookup-fn (_ ... (fn f_0 [(lft ι) ... T ...] ((x t) ...) { st ... }) _ ...) f_0)
   (fn f_0 [(lft ι) ... T ...] ((x t) ...) { st ... })]
  [(lookup-fn prog f) ,(error "lookup-fn: function with name not found:" (term f))])

(redex-chk
 (lookup-fn ((enum Option [T] { (None) (Some T) })
             (fn unwrap [T] ((opt (Option T))) { (match opt { ((Option::None) => (abort!))
                                                              ((Option::Some x) => x) }) }))
            unwrap) (fn unwrap [T] ((opt (Option T))) { (match opt { ((Option::None) => (abort!))
                                                                     ((Option::Some x) => x) }) }))
(define-metafunction Rust0-Machine
  lookup-addr : ψ α -> v
  [(lookup-addr (mem (α_!_1 v_1) ... ((name α α_!_1) v_2) (α_!_1 v_3) ...) α) v_2]
  [(lookup-addr (name ψ (mem (α_!_1 v) ...)) (name α α_!_1))
   ,(error "failed to look up address " (term α) " in " (term ψ))])

(redex-chk
 (lookup-addr (mem (α1 3) (α2 5) (α3 6)) α2) 5
 (lookup-addr (mem (α1 3) (α2 5) (α3 6)) α1) 3
 (lookup-addr (mem (α1 3) (α2 5) (α3 6)) α3) 6)

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
  match-pat : pat v ψ -> any
  ;; matching against an address directly will dereference it
  [(match-pat x α ψ) ((x (lookup-addr ψ α)))]
  ;; trivial variable patterns produce a binding
  [(match-pat x v ψ) ((x v))]

  ;; tuple patterns recursively match against the components of the tuple
  [(match-pat (tup pat ...) (tup α ...) ψ)
   ,(group 2 (flatten (term ((match-pat pat (lookup-addr ψ α) ψ) ...))))]
  ;; matching a tuple against anything else will fail
  [(match-pat (tup pat ...) v ψ) (failed)]

  ;; enum variant patterns recursively match against the fields of the variant
  [(match-pat (vid pat ...) (vid α ...) ψ)
   ,(group 2 (flatten (term ((match-pat pat (lookup-addr ψ α) ψ) ...))))]
  ;; if there's a name mismatch, the enum variants don't match
  [(match-pat ((name expected vid_!_1) _ ...) ((name found vid_!_1) _ ...) ψ) (failed)]
  ;; matching an enum variant pattern with anything else will fail
  [(match-pat (vid pat ...) v ψ) (failed)]

  ;; wildcard pattern matches everything, but binds nothing
  [(match-pat underscore _ ψ) ()])

(redex-chk
 (match-pat x 5 (mem)) ((x 5))
 (match-pat x α (mem (α 7))) ((x 7))

 (match-pat (Foo x y)
            (Foo α1 α2)
            (mem (α2 5) (α1 17)))
 ((x 17) (y 5))

 (match-pat (Foo (Bar x) (Bar y) z)
            (Foo α1 α2 α3)
            (mem (α5 13) (α4 15) (α3 8) (α2 (Bar α4)) (α1 (Bar α5))))
 ((x 13) (y 15) (z 8)))

(define-metafunction Rust0-Machine
  match-pat-or-err : pat v ψ -> any
  [(match-pat-or-err pat v ψ) ,(let ([binds (term (match-pat pat v ψ))])
                                 (if (not (member (term failed) binds))
                                     binds
                                     (error "failed to match pattern " (term pat)
                                            " against " (term v))))])

(define-metafunction Rust0-Machine
  first-match : ψ v ((pat => rv) ...) -> any
  [(first-match ψ v ((pat => rv) (pat_2 => rv_2) ...))
   ,(let ([binds (term (match-pat pat v ψ))])
      (if (not (member (term failed) binds))
          (cons (term rv) binds)
          (term (first-match ψ v ((pat_2 => rv_2) ...)))))]
  [(first-match ψ v ()) ,(error "failed to find match for value:" (term v))])

(redex-chk
 (first-match (mem) 3 (((Foo) => 1) (x => 2) (x => 4))) (2 (x 3))
 (first-match (mem (α2 2) (α1 1)) (Foo α1 α2) (((Foo x y) => (x + y)))) ((x + y) (x 1) (y 2)))

(define-metafunction Rust0-Machine
  eval-simple-expr-in : lv ρ ψ -> cv
  [(eval-simple-expr-in lv ρ ψ)
   ,(car (apply-reduction-relation* -->Rust0 (term (exec lv ρ ψ halt ()))))])

(redex-chk
 (eval-simple-expr-in y (env (mut y y1) (imm x x1)) (mem (y1 (ptr x1)) (x1 5))) (ptr x1))

(define-metafunction Rust0-Machine
  eval : prog -> any
  [(eval prog) ,(car (apply-reduction-relation* -->Rust0 (term (exec · (env) (mem) start prog))))])

(redex-chk
 (eval ((fn main [] () { (let mut (x num) = (1 + 2)) (x := 6) (1 + x) }))) 7
 (eval ((fn main [] () { (let mut (x num) = (1 + 2))
                         (let mut (unused num) = 5)
                         (x := 6)
                         (1 + x) }))) 7
 (eval ((fn main [] () { (let mut (unused num) = 5)
                         (let mut (x num) = (1 + 2))
                         (x := 6)
                         (1 + x) }))) 7
 (eval ((fn main [] () { (block (3 + 3) (4 + 4) (5 + 5)) }))) 10
 (eval ((fn main [] () { (proj x (Point { (x 0) (y 1) })) }))) 0
 (eval ((fn main [] () { (let ((tup x y) (tup num num)) = (tup 4 5))
                         (x + y) }))) 9
 (eval ((fn main [] () { (let (x num) = 3)
                         (let (y (ref ι num)) = (ref ι x))
                         (let mut (z num) = (deref y))
                         (z := 5)
                         (x + z) }))) 8
 (eval ((fn main [] () { (let mut (x num) = 3)
                         (let (y (ref ι num)) = (ref ι x))
                         (let (z num) = (deref y))
                         (x := 5)
                         (x + z) }))) 8

 (eval ((fn main [] () { (let mut (x num) = 5)
                         (let mut (y (ref ι num)) = (ref ι x))
                         ((deref y) := 4)
                         x }))) 4
 (eval ((fn main [] () { (let mut (n num) = 5)
                         (let mut (x (ref ι num)) = (ref ι n))
                         (let mut (y (ref ι (ref ι num))) = (ref ι x))
                         (let mut (m num) = 3)
                         (let mut (z (ref ι num)) = (ref ι m))
                         ((deref y) := z)
                         ((deref (deref y)) := 9)
                         (m + n) }))) 14

 (eval ((fn main [] () { (add_doubles [] (2 3)) })
        (fn add_doubles [] ((x num) (y num)) { ((x + x) + (y + y)) }))) 10

 (eval ((fn main [] () { (sum_to [] ((2 + 3))) })
        (fn sum_to [] ((x num)) { (if (x = 0)
                                     0
                                     (x + (sum_to [] ((x + -1))))) }))) 15
 (eval ((enum Option [T] { (None) (Some T) })
        (fn unwrap [T] ((opt (Option T))) { (match opt { ((Option::None) => (abort!))
                                                         ((Option::Some x) => x) }) })
        (fn main [] () { (let (x (Option num)) = (Option::Some 2))
                         (unwrap [num] (x)) }))) 2
 (eval ((enum Option [T] { (None) (Some T) })
        (fn unwrap [T] ((opt (Option T))) { (match opt { ((Option::None) => (abort!))
                                                         ((Option::Some x) => x) }) })
        (fn main [] () { (let (x (Option num)) = (Option::None))
                         (unwrap [num] (x)) }))) (abort!))
