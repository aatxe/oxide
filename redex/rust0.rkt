#lang racket/base

(require redex
         redex-chk
         racket/block
         racket/list
         rackunit)

(define-language Rust0
  ;; programs
  (prog ::= (tls ...))

  ;; top-level statements
  (tls ::=
       defn
       (fn f [(lft ι) ... T ...] ((x t) ...) -> t { e }))

  ;; definitions for data structures
  (defn ::=
    (struct sid [(lft ι) ... T ...] {(x t) ...})
    (struct sid [(lft ι) ... T ...] t ...)
    (enum sid [(lft ι) ... T ...] {dt ...}))

  ;; lvalues - expressions that can appear on the left-side of an assignment
  (lv ::=
      ;; variable
      x
      ;; pointer dereference
      (deref lv)
      ;; field projection
      (proj x lv)
      ;; product projection
      (proj n lv))

  ;; data structures - struct and variant kinds
  (d ::=
     ;; named tuple - a kind of struct and enum variant
     (sid [(lft ι) ... t ...] e ...)
     ;; named record - a kind of struct and enum variant
     (sid [(lft ι) ... t ...] {(x e) ...}))

  ;; data structure typeforms - struct and variant kinds with types
  ;; n.b. these are not an actual kind of type, but are used in definitions for enums
  (dt ::=
      (sid t ...)
      (sid {(x t) ...}))

  ;; expressions
  (e ::=
     ;; variables
     x
     ;; let bindings (immutable and mutable)
     (let [(pat t) = e] e)
     (let mut [(pat t) = e] e)
     ;; assignment (only for mutable bindings)
     (lv := e)

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
     ;; blocks - sequence of expressions, takes value of last expression
     (block e ...)
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
       (sid {(x pat) ...}))

  ;; operators
  (binop ::= + * = ∧ ∨)
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
           (fn unwrap [T] ((opt (Option [T]))) -> T { (match opt { ((Option::None) => (abort!))
                                                                   ((Option::Some x) => x) }) }))
 #:m prog ((fn main [] () -> (tup) { (tup) }))
 #:m prog ((fn main [] () -> num { 7 }))

 ;; valid top-level statements
 #:m tls (struct Point [] { (x num)
                            (y num) })
 #:m tls (struct Ref [(lft α) T] { (inner (ref α T)) })
 #:m tls (enum Option [T] { (None)
                            (Some T) })
 #:m tls (enum WeirdOption [T] { (None)
                                 (Some T)
                                 (Double T T) })
 #:m tls (fn main [] () -> (tup) { (block (tup) (tup) (tup)) })
 #:m tls (fn main [] () -> (tup) { (let ([(tup x y) (tup num num)] = (tup 1 2))
                                     (tup)) })
 #:m tls (fn sum_to [] ((x num)) -> num { (if (x = 0)
                                              1
                                              (x + (sum_to [] ((x + -1))))) })

 ;; invalid top-level statements
 #:f #:m tls (fn main [] () -> num { (let ([(tup 1 2) (tup num num)] = (tup 3 4))
                                       (tup)) }))

(define-extended-language Rust0-Machine Rust0
  ;; flags indicating immutable or mutable
  (flag ::=
     imm
     mut)

  ;; addresses
  (α ::= variable-not-otherwise-mentioned)

  ;; variable environment - maps identifiers to addresses
  (ρ ::= (env (flag x α) ...))
  ;; memory - maps addresses to values
  (ψ ::= (mem (α v) ...))

  ;; values
  (v ::=
     ;; constants
     const
     ;; pointers to α (a live reference)
     (ptr α)
     ;; allocated tuple (tuple with addresses)
     (tup α ...)
     ;; allocated named-tuple
     (sid [(lft ι) ... t ...] α ...)
     ;; allocated named-record
     (sid [(lft ι) ... t ...] {(x α) ...}))

  ;; control strings
  (c ::=
     ;; empty
     ·
     ;; statement
     e)

  ;; control values - flattened values (i.e. with no indirection via pointers) and abort! and ·
  (cv ::=
      ·
      (abort!)
      (ptr α)
      const
      (tup cv ...)
      (sid [(lft ι) ... t ...] cv ...)
      (sid [(lft ι) ... t ...] {(x cv) ...}))

  ;; continuations
  (κ ::=
     ;; halt
     halt
     ;; special start continuation indicating main should be called
     start
     ;; function call continuation - the hole in st should be bound to x
     (fun x e ρ κ)
     ;; continuation representing a block of statements to execute before continuing to κ
     (block e ... κ))

  ;; lvalues
  (lv ::=
      ....
      ;; pointers appear in the runtime interpretation of lvalues
      (ptr α))

  ;; LValue contexts
  (LV ::=
      hole
      ;; pointer dereference
      (deref LV)
      ;; field projection
      (proj x LV)
      ;; product projection
      (proj n LV))

  ;; evaluation contexts
  (E ::=
     ;; top-level evaluation context, format: c ρ ψ κ prog
     (E ρ ψ κ prog)

     ;; hole
     hole

     ;; let bindings
     (let [(pat t) = E] e)
     (let mut [(pat t) = E] e)
     ;; assignment
     (lv := E)

     ;; data structures (enum variants and structs)
     (sid [(lft ι) ... t ...] v ... E e ...)
     (sid [(lft ι) ... t ...] {(x v) ... (x E) (x e) ...})
     ;; record projection
     (proj x E)

     ;; function calls
     (f [(lft ι) ... t ...] (v ... E e ...))
     ;; pattern matching
     (match E {(pat => e) ...})

     ;; branching
     (if E e e)

     ;; products
     (tup v ... E e ...)
     ;; product projection
     (proj n E)

     ;; primitive ops
     (v + E)
     (E + e)
     (v * E)
     (E * e)
     (v = E)
     (E = e)
     (- E)
     (v ∧ E)
     (E ∧ e)
     (v ∨ E)
     (E ∨ e)
     (¬ E)
     (deref E)))

(define -->Rust0-LValue
  (reduction-relation
   Rust0-Machine

   (--> ((in-hole LV x) (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...) ψ)
        ((in-hole LV (ptr α)) (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...) ψ)
        "LV-Id")
   ;; NOTE: I think real Rust does auto-dereferencing, so, one deref is automatically the correct number of derefs?
   (--> ((in-hole LV (deref (ptr α))) ρ (name ψ (mem (α_1 v_1) ... (α (ptr α_t)) (α_2 v_2) ...)))
        ((in-hole LV (ptr α_t)) ρ ψ)
        "LV-Deref")
   (--> ((in-hole LV (proj n (ptr α_t)))
         ρ
         (mem (α_1 v_1) ... (α_t (tup α_tc ...)) (α_2 v_2) ...))
        ((in-hole LV (ptr (proj-tup n (tup α_tc ...))))
         ρ
         (mem (α_1 v_1) ... (α_t (tup α_tc ...)) (α_2 v_2) ...))
        "LV-ProjTup")
   (--> ((in-hole LV (proj n (ptr α_t)))
         ρ
         (mem (α_1 v_1) ... (α_t (sid [] α_tc ...)) (α_2 v_2) ...))
        ((in-hole LV (ptr (proj-tup n (sid [] α_tc ...))))
         ρ
         (mem (α_1 v_1) ... (α_t (sid [] α_tc ...)) (α_2 v_2) ...))
        "LV-ProjNamedTup")
   (--> ((in-hole LV (proj x_t (ptr α_t)))
         ρ
         (mem (α_1 v_1) ... (α_t (sid [] { (x_tc α_tc) ... })) (α_2 v_2) ...))
        ((in-hole LV (ptr (proj-rec x_t (sid [] { (x_tc α_tc) ... }))))
         ρ
         (mem (α_1 v_1) ... (α_t (sid [] { (x_tc α_tc) ... })) (α_2 v_2) ...))
        "LV-ProjNamedRec")

  (--> ((ptr α) ρ ψ)
       (ptr α)
       "LV-FinishReduce")))

(define -->Rust0
  (reduction-relation
   Rust0-Machine

   (--> (· ρ ψ start prog)
        (e ρ ψ halt prog)
        (where (fn main [] () -> t { e }) (lookup-fn prog main))
        "E-StartMain")
   (--> (cv ρ ψ halt prog)
        cv
        "E-HaltProgram")

   (--> ((block e ...) ρ ψ κ prog)
        (· ρ ψ (block e ... κ) prog)
        "E-StartBlock")
   (--> (cv ρ ψ (block e_0 e_1 ... κ) prog)
        (e_0 ρ ψ (block e_1 ... κ) prog)
        "E-AdvanceBlock")
   (--> (cv ρ ψ (block κ) prog)
        (cv ρ ψ κ prog)
        "E-EndBlock")

   (--> ((in-hole E abort!) ρ ψ κ prog)
        ((abort!) ρ ψ κ prog)
        "E-Abort")
   (--> ((abort!) ρ ψ κ prog)
        ((abort!) ρ ψ halt prog)
        "E-AbortKillsStack")

   (--> ((in-hole E (tup v_n ...))
         (env (flag x α) ...)
         (mem (α_m v_m) ...)
         κ prog)
        ((in-hole E (tup α_n ...))
         (env (flag x α) ...)
         (mem (α_n v_n) ... (α_m v_m) ...)
         κ prog)
        ;; NOTE: rather than these alloc/dealloc constraints, I think I could just add (ret cv κ)?
        ;; allocate if it's not a bare expression
        (side-condition (or (not (eq? (term E) (term hole)))
                            ;; or if it is a bare expression and we're returning from a function
                            (and (pair? (term κ))
                                 (eq? (car (term κ)) (term fun)))))
        (where (α_n ...) ,(variables-not-in (term (v_n ... x ... α ... α_m ... v_m ...))
                                            (map (lambda (x) (gensym)) (term (v_n ...)))))
        "E-AllocTup")
   (--> ((tup α_t ...) ρ ψ κ prog)
        ;; TODO: actually remove every α_t from ψ
        ((tup (lookup-addr ψ α_t) ...) ρ ψ κ prog)
        ;; dealloc only when we're not returning from a function
        (side-condition (or (not (pair? (term κ)))
                            (not (eq? (car (term κ)) (term fun)))))
        "E-DeallocTup")

   (--> ((in-hole E (sid [(lft ι) ... t ...] v_n ...))
         (env (flag x α) ...)
         (mem (α_m v_m) ...)
         κ prog)
        ((in-hole E (sid [(lft ι) ... t ...] α_n ...))
         (env (flag x α) ...)
         (mem (α_n v_n) ... (α_m v_m) ...)
         κ prog)
        ;; NOTE: rather than these alloc/dealloc constraints, I think I could just add (ret cv κ)?
        ;; allocate if it's not a bare expression
        (side-condition (or (not (eq? (term E) (term hole)))
                            ;; or if it is a bare expression and we're returning from a function
                            (and (pair? (term κ))
                                 (eq? (car (term κ)) (term fun)))))
        (where (α_n ...) ,(variables-not-in (term (v_n ... x ... α ... α_m ... v_m ...))
                                            (map (lambda (x) (gensym)) (term (v_n ...)))))
        "E-AllocNamedTup")
   (--> ((sid [(lft ι) ... t ...] α_t ...) ρ ψ κ prog)
        ;; TODO: actually remove every α_t from ψ
        ((sid [(lft ι) ... t ...] (lookup-addr ψ α_t) ...) ρ ψ κ prog)
        ;; dealloc only when we're not returning from a function
        (side-condition (or (not (pair? (term κ)))
                            (not (eq? (car (term κ)) (term fun)))))
        "E-DeallocNamedTup")
   (--> ((in-hole E (sid [(lft ι) ... t ...] { (x_n v_n) ... }))
         (env (flag x α) ...)
         (mem (α_m v_m) ...)
         κ prog)
        ((in-hole E (sid [(lft ι) ... t ...] { (x_n α_n) ... }))
         (env (flag x α) ...)
         (mem (α_n v_n) ... (α_m v_m) ...)
         κ prog)
        ;; NOTE: rather than these alloc/dealloc constraints, I think I could just add (ret cv κ)?
        ;; allocate if it's not a bare expression
        (side-condition (or (not (eq? (term E) (term hole)))
                            ;; or if it is a bare expression and we're returning from a function
                            (and (pair? (term κ))
                                 (eq? (car (term κ)) (term fun)))))
        (where (α_n ...) ,(variables-not-in (term (v_n ... x ... α ... x_n ... α_m ... v_m ...))
                                            (term (x_n ...))))
        "E-AllocNamedRecord")
   (--> ((sid [(lft ι) ... t ...] { (x_t α_t) ... }) ρ ψ κ prog)
        ((sid [(lft ι) ... t ...] { (x_t (lookup-addr ψ α_t)) ... }) ρ ψ κ prog)
        ;; dealloc only when we're not returning from a function
        (side-condition (or (not (pair? (term κ)))
                            (not (eq? (car (term κ)) (term fun)))))
        "E-DeallocNamedRecord")

   (--> ((let [(pat t) = v] e)
         (env (flag x_e α_e) ...)
         (name ψ (mem (α_m v_m) ...))
         κ prog)
        (e
         (env (imm x_n α_n) ... (flag x_e α_e) ...)
         (mem (α_n v_n) ... (α_m v_m) ...)
         κ prog)
        (where ((x_n v_n) ...) (match-pat-or-err pat v ψ))
        (where (α_n ...) ,(variables-not-in (term (x_e ... x_n ... α_e ... α_m ...))
                                            (term (x_n ...))))
        "E-ImmBinding")
   (--> ((let mut [(pat t) = v] e)
         (env (flag x_e α_e) ...)
         (name ψ (mem (α_m v_m) ...))
         κ prog)
        (e
         (env (mut x_n α_n) ... (flag x_e α_e) ...)
         (mem (α_n v_n) ... (α_m v_m) ...)
         κ prog)
        (where ((x_n v_n) ...) (match-pat-or-err pat v ψ))
        (where (α_n ...) ,(variables-not-in (term (x_e ... x_n ... α_e ... α_m ...))
                                            (term (x_n ...))))
        "E-MutBinding")

   (--> ((in-hole E x)
         (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
         (mem (α_3 v_3) ... (α v) (α_4 v_4) ...)
         κ prog)
        ((in-hole E v)
         (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
         (mem (α_3 v_3) ... (α v) (α_4 v_4) ...)
         κ prog)
        "E-Id")

   (--> ((in-hole E (f [any ...] (v ...)))
         ρ
         (name ψ (mem (α_m v_m) ...))
         κ prog)
        (e
         (env (imm x α) ...)
         (mem (α v) ... (α_m v_m) ...)
         (fun x_f (in-hole E x_f) ρ κ) prog)
        (where (fn f [(lft ι) ... T ...] ((x t) ...) -> t_ret { e })
               (lookup-fn prog f))
        (where (α ...) ,(variables-not-in (term (x_f x ... v ... α_m ... v_m ...))
                                          (term (x ...))))
        (fresh x_f)
        "E-App")
   ;; TODO: return should de-allocate memory that is no longer accessible (eqv. calling drop)
   (--> (v_1 _ (mem (α_m v_m) ...) (fun x_1 e (env (flag_2 x_2 α_2) ...) κ) prog)
        (e (env (imm x_1 α_1) (flag_2 x_2 α_2) ...) (mem (α_1 v_1) (α_m v_m) ...) κ prog)
        (fresh α_1)
        "E-Return")

   (--> ((in-hole E (match v_match {(pat => e) ...}))
         (env (flag x α) ...)
         (name ψ (mem (α_m v_m) ...))
         κ prog)
        ((in-hole E e_m)
         (env (imm x_n α_n) ... (flag x α) ...)
         (mem (α_n v_n) ... (α_m v_m) ...)
         κ prog)
        (where (e_m (x_n v_n) ...) (first-match ψ v_match ((pat => e) ...)) )
        (where (α_n ...) ,(variables-not-in (term (α_m ...)) (term (x_n ...))))
        "E-Match")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; References and Assignment ;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (--> ((in-hole E (deref (ptr α))) ρ (mem (α_1 v_1) ... (α v) (α_2 v_2) ...) κ prog)
        ((in-hole E v) ρ (mem (α_1 v_1) ... (α v) (α_2 v_2) ...) κ prog)
        "E-Deref")
   ;; projections are a kind of dereference
   (--> ((in-hole E (proj n (tup α ...))) ρ (mem (α_1 v_1) ... (α_t v_t) (α_2 v_2) ... ) κ prog)
        ((in-hole E v_t) ρ (mem (α_1 v_1) ... (α_t v_t) (α_2 v_2) ...) κ prog)
        (where α_t (proj-tup n (tup α ...)))
        "E-ProjTup")
   (--> ((in-hole E (proj n (sid [] α ...))) ρ (mem (α_1 v_1) ... (α_t v_t) (α_2 v_2) ... ) κ prog)
        ((in-hole E v_t) ρ (mem (α_1 v_1) ... (α_t v_t) (α_2 v_2) ...) κ prog)
        (where α_t (proj-tup n (sid [] α ...)))
        "E-ProjNamedTup")
   (--> ((in-hole E (proj x_t (sid [] { (x α) ... }))) ρ (mem (α_1 v_1) ... (α_t v_t) (α_2 v_2) ...) κ prog)
        ((in-hole E v_t) ρ (mem (α_1 v_1) ... (α_t v_t) (α_2 v_2) ...) κ prog)
        (where α_t (proj-rec x_t (sid [] { (x α) ... })))
        "E-ProjNamedRec")

   (--> ((in-hole E (ref ι x))
         (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
         ψ κ prog)
        ((in-hole E (ptr α))
         (env (flag_1 x_1 α_1) ... (flag x α) (flag_2 x_2 α_2) ...)
         ψ κ prog)
        "E-RefId")

   (--> ((lv := v_t)
         ρ
         (name ψ (mem (α_3 v_3) ... (α_t v_old) (α_4 v_4) ...))
         κ prog)
        ((tup)
         ρ
         (mem (α_3 v_3) ... (α_t v_t) (α_4 v_4) ...)
         κ prog)
        (where (ptr α_t) (reduce-lv-in lv ρ ψ))
        "E-Assign")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; Pure Reduction Rules ;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;

   ;; Branching
   (--> (in-hole E (if true e_1 e_2))
        (in-hole E e_1)
        "E-IfTrue")
   (--> (in-hole E (if false e_1 e_2))
        (in-hole E e_2)
        "E-IfFalse")

   ;; Numbers
   (--> (in-hole E (n_1 + n_2))
        (in-hole E (Σ n_1 n_2))
        "E-Add")
   (--> (in-hole E (n_1 * n_2))
        (in-hole E (Π n_1 n_2))
        "E-Mult")
   (--> (in-hole E (v = v))
        (in-hole E true)
        "E-EqTrue")
   (--> (in-hole E (v_!_1 = v_!_1))
        (in-hole E false)
        "E-EqFalse")
   (--> (in-hole E (- n))
        (in-hole E (negative n))
        "E-Negative")

   ;; Booleans
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
  [(lookup-fn (_ ... (fn f_0 [(lft ι) ... T ...] ((x t) ...) -> t_ret { e }) _ ...) f_0)
   (fn f_0 [(lft ι) ... T ...] ((x t) ...) -> t_ret { e })]
  [(lookup-fn prog f) ,(error "lookup-fn: function with name not found:" (term f))])

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
  match-pat : pat any ψ -> any
  ;; matching against an address directly will dereference it
  [(match-pat x α ψ) ((x (lookup-addr ψ α)))]
  ;; trivial variable patterns produce a binding
  [(match-pat x v ψ) ((x v))]

  ;; tuple patterns recursively match against the components of the tuple
  [(match-pat (tup pat ...) (tup α ...) ψ)
   ,(group 2 (flatten (term ((match-pat pat (lookup-addr ψ α) ψ) ...))))]
  ;; matching a tuple against anything else will fail
  [(match-pat (tup pat ...) v ψ) (failed)]

  ;; named tuple patterns recursively match against the fields of the variant
  [(match-pat (sid pat ...) (sid [_ ...] α ...) ψ)
   ,(group 2 (flatten (term ((match-pat pat (lookup-addr ψ α) ψ) ...))))]
  ;; if there's a name mismatch, the named tuples don't match
  [(match-pat ((name expected sid_!_1) _ ...) ((name found sid_!_1) _ ...) ψ) (failed)]
  ;; matching a named tuple pattern with anything else will fail
  [(match-pat (sid pat ...) v ψ) (failed)]

  ;; wildcard pattern matches everything, but binds nothing
  [(match-pat underscore _ ψ) ()])

(redex-chk
 (match-pat x 5 (mem)) ((x 5))
 (match-pat x α (mem (α 7))) ((x 7))

 (match-pat (Foo x y)
            (Foo [] α1 α2)
            (mem (α2 5) (α1 17)))
 ((x 17) (y 5))

 (match-pat (Foo (Bar x) (Bar y) z)
            (Foo [] α1 α2 α3)
            (mem (α5 13) (α4 15) (α3 8) (α2 (Bar [] α4)) (α1 (Bar [] α5))))
 ((x 13) (y 15) (z 8)))

(define-metafunction Rust0-Machine
  match-pat-or-err : pat v ψ -> any
  [(match-pat-or-err pat v ψ) ,(let ([binds (term (match-pat pat v ψ))])
                                 (if (not (member (term failed) binds))
                                     binds
                                     (error "failed to match pattern " (term pat)
                                            " against " (term v))))])

(define-metafunction Rust0-Machine
  first-match : ψ v ((pat => e) ...) -> any
  [(first-match ψ v ((pat => e) (pat_2 => e_2) ...))
   ,(let ([binds (term (match-pat pat v ψ))])
      (if (not (member (term failed) binds))
          (cons (term e) binds)
          (term (first-match ψ v ((pat_2 => e_2) ...)))))]
  [(first-match ψ v ()) ,(error "failed to find match for value:" (term v))])

(redex-chk
 (first-match (mem) 3 (((Foo) => 1) (x => 2) (x => 4))) (2 (x 3))
 (first-match (mem (α2 2) (α1 1)) (Foo [] α1 α2) (((Foo x y) => (x + y)))) ((x + y) (x 1) (y 2)))

(define-metafunction Rust0-Machine
  Σ : number ... -> number
  [(Σ number ...) ,(apply + (term (number ...)))])

(define-metafunction Rust0-Machine
  Π : number ... -> number
  [(Π number ...) ,(apply * (term (number ...)))])

(define-metafunction Rust0-Machine
  proj-tup : number v -> α
  [(proj-tup number (tup α ...)) ,(list-ref (term (α ...)) (- (term number) 1))]
  [(proj-tup number (sid [] α ...)) ,(list-ref (term (α ...)) (- (term number) 1))])

(define-metafunction Rust0-Machine
  proj-rec : x v -> α
  [(proj-rec x (sid [] { (x_1 α_1) ... (x α) (x_2 α_2) ... })) α]
  [(proj-rec (name x x_!_1) (name v (sid [] { (x_!_1 α) ... }))) ,(error "failed to find field " (term x)
                                                                         " in " (term v))])
(define-metafunction Rust0-Machine
  negative : number -> number
  [(negative number) ,(- (term number))])

(define-metafunction Rust0-Machine
  reduce-lv-in : lv ρ ψ -> (ptr α)
  [(reduce-lv-in lv ρ ψ)
   ,(car (apply-reduction-relation* -->Rust0-LValue (term (lv ρ ψ))))])

(redex-chk
 (reduce-lv-in y (env (mut y y1)) (mem (y1 5))) (ptr y1))

(define-metafunction Rust0-Machine
  eval : prog -> any
  [(eval prog) ,(car (apply-reduction-relation* -->Rust0 (term (· (env) (mem) start prog))))])

(redex-chk
 ;; Straight line code
 (eval ((fn main [] () -> num { 7 }))) 7
 (eval ((fn main [] () -> num { (block 3 2) }))) 2
 (eval ((fn main [] () -> num { ((3 + 2) * 6) }))) 30
 (eval ((fn main [] () -> num { (block 4 5) }))) 5
 (eval ((fn main [] () -> (tup num num) { (tup 1 2) }))) (tup 1 2)
 (eval ((fn main [] () -> (tup num num) { (let [(x (tup num num)) = (tup 5 9)]
                                            x) }))) (tup 5 9)
 (eval ((fn main [] () -> num { (let [(x (tup num num)) = (tup 5 9)]
                                  ((proj 1 x) + (proj 2 x))) }))) 14
 (eval ((struct Point [] num num)
        (fn main [] () -> Point { (let [(x Point) = (Point [] 1 9)]
                                    x) }))) (Point [] 1 9)
 (eval ((struct Point [] num num)
        (fn main [] () -> num { (let [(x Point) = (Point [] 1 9)]
                                  ((proj 1 x) + (proj 2 x))) }))) 10
 (eval ((struct Point [] { (x num) (y num) })
        (fn main [] () -> Point { (let [(p Point) = (Point [] { (x 1) (y 9)})]
                                    p) }))) (Point [] { (x 1) (y 9) })
 (eval ((struct Point [] { (x num) (y num) })
        (fn main [] () -> num { (let [(p Point) = (Point [] { (x 1) (y 9)})]
                                  ((proj x p) + (proj y p))) }))) 10
 (eval ((struct Foo [] { (x (tup num num)) (y (tup num num)) })
        (fn main [] () -> (tup num num) { (let [(p Foo) = (Foo [] { (x (tup 1 2)) (y (tup 3 4)) })]
                                            (proj x p)) }))) (tup 1 2)
 (eval ((fn main [] () -> num { (block (3 + 3) (4 + 4) (5 + 5)) }))) 10
 (eval ((fn main [] () -> num { (let mut [(x (tup num num num)) = (tup 2 3 4)]
                                  (block
                                   ((proj 3 x) := 7)
                                   (proj 3 x))) }))) 7
 (eval ((struct Point [] num num)
        (fn main [] () -> num { (let [(x Point) = (Point [] 1 9)]
                                  (block
                                   ((proj 1 x) := 6)
                                   ((proj 1 x) + (proj 2 x)))) }))) 15
 (eval ((struct Point [] { (x num) (y num) })
        (fn main [] () -> num { (let [(p Point) = (Point [] { (x 1) (y 9)})]
                                  (block
                                   ((proj x p) := 11)
                                   ((proj x p) + (proj y p)))) }))) 20

 ;; Simple non-recursive functions
 (eval ((fn main [] () -> num { (id [] (5)) })
        (fn id [] ((x num)) -> num { x }))) 5
 (eval ((fn main [] () -> (tup num num) { (id [] ((tup 7 4))) })
        (fn id [] ((x (tup num num))) -> (tup num num) { x }))) (tup 7 4)
 (eval ((fn main [] () -> num { (sum_of_squares [] (2 3)) })
        (fn sum_of_squares [] ((x num) (y num)) -> num { ((x * x) + (y * y)) }))) 13

;;  ;; Complex functions with recursion, pattern matching, abort
 (eval ((fn main [] () -> num { (sum_to [] ((2 + 3))) })
        (fn sum_to [] ((x num)) -> num { (if (x = 0)
                                             0
                                             (x + (sum_to [] ((x + -1))))) }))) 15
 (eval ((enum Option [T] { (None) (Some T) })
        (fn unwrap [T] ((opt (Option [T]))) -> T { (match opt { ((Option::None) => (abort!))
                                                                ((Option::Some x) => x) }) })
        (fn main [] () -> num { (let [(x (Option [num])) = (Option::Some [] 2)]
                                  (unwrap [num] (x))) }))) 2
(eval ((enum Option [T] { (None) (Some T) })
       (fn unwrap [T] ((opt (Option [T]))) -> T { (match opt { ((Option::None) => (abort!))
                                                               ((Option::Some x) => x) }) })
       ;; NOTE: we don't have a clear story for the type of abort! yet
       (fn main [] () -> (tup) { (let [(x (Option [num])) = (Option::None [])]
                                   (unwrap [num] (x))) }))) (abort!)

 ;; Straight line code with references
 (eval ((fn main [] () -> num { (let [(x num) = 3]
                                  (let [(y (ref ι num)) = (ref ι x)]
                                    (let mut [(z num) = (deref y)]
                                      (block
                                       (z := 5)
                                       (x + z))))) }))) 8
 (eval ((fn main [] () -> num { (let mut [(x num) = 3]
                                  (let [(y (ref ι num)) = (ref ι x)]
                                    (let [(z num) = (deref y)]
                                      (block
                                       (x := 5)
                                       (x + z))))) }))) 8
 (eval ((fn main [] () -> num { (let mut [(x num) = 5]
                                  (let mut [(y (ref ι num)) = (ref ι x)]
                                    (block
                                     ((deref y) := 4)
                                     x))) }))) 4
 (eval ((fn main [] () -> num { (let mut [(n num) = 5]
                                  (let mut [(x (ref ι num)) = (ref ι n)]
                                    (let mut [(y (ref ι (ref ι num))) = (ref ι x)]
                                      (let mut [(m num) = 3]
                                        (let mut [(z (ref ι num)) = (ref ι m)]
                                          (block
                                           ((deref y) := z)
                                           ((deref (deref y)) := 9)
                                           (m + n))))))) }))) 14)

(define-extended-language Rust0-statics Rust0
  ;; value contexts
  (Γ ::=
     •
     (Γ (x t)))

  ;; data structure contexts
  (Θ ::=
     •
     (Θ defn)))

(define-judgment-form Rust0-statics
  #:mode (in I I I O)
  #:contract (in Γ x = t)

  [---------------------
   (in (Γ (x t)) x = t)]

  [(in Γ x = t)
   --------------------------------------
   (in (Γ (x_!_1 t)) (name x x_!_1) = t)])

(define-judgment-form Rust0-statics
  #:mode (meets-def I I I I I O)
  #:contract (meets-def Γ Θ ⊢ e : t)

  ;; patterns that matched

  [(type? Γ Θ ⊢ e : t) ...
   ------------------------------------------- "T-TupStructMeetsDefn"
   (meets-def Γ (Θ (struct sid [_ ...] t ...))
              ⊢ (sid [_ ...] e ...) : sid)   ]

  [(type? Γ Θ ⊢ e : t) ...
   --------------------------------------------------- "T-RecStructMeetsDefn"
   (meets-def Γ (Θ (struct sid [_ ...] { (x t) ... }))
              ⊢ (sid [_ ...] { (x e) ... }) : sid)   ]

  ;; patterns that did not match

  [(meets-def Γ Θ ⊢ e : t)
   --------------------------------------------------- "T-TupStructPassDifferentId"
   (meets-def Γ (Θ (struct sid_!_1 [_ ...] _ ...))
              ⊢ (name e (sid_!_1 [_ ...] _ ...)) : t)]
  [(meets-def Γ Θ ⊢ e : t)
   --------------------------------------------------- "T-TupStructPassRecStruct"
   (meets-def Γ (Θ (struct sid_!_1 [_ ...] { _ ... }))
              ⊢ (name e (sid_!_1 [_ ...] _ ...)) : t)]
  [(meets-def Γ Θ ⊢ e : t)
   --------------------------------------------------- "T-TupStructPassEnum"
   (meets-def Γ (Θ (enum sid_!_1 [_ ...] { _ ... }))
              ⊢ (name e (sid_!_1 [_ ...] _ ...)) : t)]

  [(meets-def Γ Θ ⊢ e : t)
   ------------------------------------------------------- "T-RecStructPassDifferentId"
   (meets-def Γ (Θ (struct sid_!_1 [_ ...] { _ ... }))
              ⊢ (name e (sid_!_1 [_ ...] { _ ... })) : t)]
  [(meets-def Γ Θ ⊢ e : t)
   ------------------------------------------------------- "T-RecStructPassTupStruct"
   (meets-def Γ (Θ (struct sid_!_1 [_ ...] _ ...))
              ⊢ (name e (sid_!_1 [_ ...] { _ ... })) : t)]
  [(meets-def Γ Θ ⊢ e : t)
   ------------------------------------------------------- "T-RecStructPassEnum"
   (meets-def Γ (Θ (enum sid_!_1 [_ ...] { _ ... }))
              ⊢ (name e (sid_!_1 [_ ...] { _ ... })) : t)])

(define-judgment-form Rust0-statics
  #:mode (type? I I I I I O)
  #:contract (type? Γ Θ ⊢ e : t)

  [(in Γ x = t)
   -------------------- "T-Id"
   (type? Γ Θ ⊢ x : t)]

  [---------------------- "T-Num"
   (type? Γ Θ ⊢ n : num)]

  [-------------------------- "T-True"
   (type? Γ Θ ⊢ true : bool)]

  [--------------------------- "T-False"
   (type? Γ Θ ⊢ false : bool)]

  [(type? Γ Θ ⊢ e : t) ...
   ---------------------------------------- "T-Tuple"
   (type? Γ Θ ⊢ (tup e ...) : (tup t ...))]

  [(meets-def Γ Θ ⊢ e : t_res)
   --------------------------- "T-DataStructure"
   (type? Γ Θ ⊢ e : t_res)   ]

  [ ;; TODO: type-check the pattern
   (type? Γ Θ ⊢ e_1 : t_1)
   ;; TODO: add bindings from pattern
   (type? Γ Θ ⊢ e_2 : t_2)
   ---------------------------------------- "T-Let"
   (type? Γ Θ ⊢ (let [(pat t_1) = e_1] e_2) : t_2)]

  [------------------------------ "T-EmptyBlock"
   (type? Γ Θ ⊢ (block) : (tup))]

  [(type? Γ Θ ⊢ e : t) ...
   (type? Γ Θ ⊢ e_l : t_l)
   -------------------------------------- "T-Block"
   (type? Γ Θ ⊢ (block e ... e_l) : t_l)]

  [(type? Γ Θ ⊢ e_1 : bool)
   (type? Γ Θ ⊢ e_2 : t_2)
   (type? Γ Θ ⊢ e_3 : t_2)
   ------------------------------------- "T-If"
   (type? Γ Θ ⊢ (if e_1 e_2 e_3) : t_2)]

  [(type? Γ Θ ⊢ e_1 : num)
   (type? Γ Θ ⊢ e_2 : num)
   -------------------------------- "T-Add"
   (type? Γ Θ ⊢ (e_1 + e_2) : num)]

  [(type? Γ Θ ⊢ e_1 : num)
   (type? Γ Θ ⊢ e_2 : num)
   -------------------------------- "T-Mul"
   (type? Γ Θ ⊢ (e_1 * e_2) : num)]

  [(type? Γ Θ ⊢ e : num)
   -------------------------- "T-Neg"
   (type? Γ Θ ⊢ (- e) : num)]

  [(type? Γ Θ ⊢ e_1 : t)
   (type? Γ Θ ⊢ e_2 : t)
   ------------------------------ "T-Eq"
   (type? Γ Θ ⊢ (e_1 = e_2) : bool)]

  [(type? Γ Θ ⊢ e_1 : bool)
   (type? Γ Θ ⊢ e_2 : bool)
   --------------------------------- "T-And"
   (type? Γ Θ ⊢ (e_1 ∧ e_2) : bool)]

  [(type? Γ Θ ⊢ e_1 : bool)
   (type? Γ Θ ⊢ e_2 : bool)
   --------------------------------- "T-Or"
   (type? Γ Θ ⊢ (e_1 ∨ e_2) : bool)]

  [(type? Γ Θ ⊢ e : bool)
   --------------------------- "T-Not"
   (type? Γ Θ ⊢ (¬ e) : bool)])

(define-syntax-rule (in-context Γ Θ
                      (type-of x is type))
  (let ([types (judgment-holds (type? Γ Θ ⊢ x : t) t)])
    (if (eq? (quote type) 'not-defined)
        (block
         (check-false (> (length types) 1) "Type-checking returned more than one type, but should have failed.")
         (check-true (eq? (length types) 0) "Type-checking returned a type, but should have failed."))
        (block
         (check-false (eq? (length types) 0) "Type-checking did not return a type.")
         (check-true (eq? (length types) 1) "Type-checking returned more than one type.")
         (check-equal? (car types) (term type))))))
(define-syntax-rule (type-of x is type)
  (in-context • • (type-of x is type)))

(test-begin
  (type-of 5 is num)
  (type-of true is bool)
  (type-of false is bool)
  (type-of (tup true 5) is (tup bool num))
  (in-context • (• (struct Point [] num num))
    (type-of (Point [] 5 5) is Point))
  (in-context • ((• (struct Point [] num num)) (struct Unrelated [] bool bool bool))
    (type-of (Point [] 5 5) is Point))
  (in-context • ((• (struct Point [] { (x num) (y num) })) (struct Unrelated [] bool bool bool))
    (type-of (Point [] { (x 0) (y 0) }) is Point))
  (in-context (• (x num)) •
    (type-of x is num))

  (type-of (if true 3 2) is num)
  (type-of (if true 3 false) is not-defined)
  (type-of (if ((2 = 2) ∧ (¬ (3 = (- 2))))
               (2 + 2)
               (3 * 3)) is num))
