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
     (let [() e] e)

     ;; tensor product
     (prod e e)
     ;; destructuring let for products
     (let [(prod x x) e] e)

     ;; variables
     x
     ;; functions
     (λ x e)
     ;; function application
     (e e)

     ;; of-course values
     (! v)
     ;; destructuring let for of-course values
     (let [(! x) e] e)
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
     (let [(pack ρ x) e] e))

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
     ;; hole
     hole

     ;; destructing let for unit
     (let [() E] e)

     ;; tensor product
     (prod E e)
     (prod v E)
     ;; destructuring let for products
     (let [(prod x x) E] e)

     ;; function application
     (E e)
     (v E)

     ;; destructuring let for of-course values
     (let [(! x) E] e)
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
     (let [(pack ρ x) E] e)))

(define -->L3
  (reduction-relation
   L3-dynamics
   #:domain (σ e)

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; rules from the L3 paper ;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ;; rules for of-course values
   (--> (σ (in-hole E (let [(! x) (! v)] e)))
        (σ (in-hole E (substitute e x v)))
        "let-bang")
   (--> (σ (in-hole E (dup (! v))))
        (σ (in-hole E (prod (! v) (! v))))
        "dup")
   (--> (σ (in-hole E (drop (! v))))
        (σ (in-hole E ()))
        "drop")

   ;; rules for working with allocation
   (--> ((env (l_1 v_1) ...) (in-hole E (new v)))
        ((env (l v) (l_1 v_1) ...) (in-hole E (pack l (prod (cap l) (! (ptr l))))))
        (fresh l)
        "new")
   (--> ((env (l_1 v_1) ... (l_t v_t) (l_2 v_2) ...) (in-hole E (free (pack l_t (prod (cap l_t) (! (ptr l_t)))))))
        ((env (l_1 v_1) ... (l_2 v_2) ...) (in-hole E (pack l_t v_t)))
        "free")
   (--> ((env (l_1 v_1) ... (l_t v_t) (l_2 v_2) ...) (in-hole E (swap (ptr l_t) (prod (cap l_t) v_f))))
        ((env (l_1 v_1) ... (l_t v_f) (l_2 v_2) ...) (in-hole E (prod (cap l_t) v_t)))
        "swap")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; everything after this is not in the paper ;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ;; destructuring lets for everything that's not of-course values
   (--> (σ (in-hole E (let [() ()] e)))
        (σ (in-hole E e))
        "let-unit")
   (--> (σ (in-hole E (let [(prod x_1 x_2) (prod v_1 v_2)] e)))
        (σ (in-hole E (substitute (substitute e x_1 v_1) x_2 v_2)))
        "let-prod")
   (--> (σ (in-hole E (let [(pack ρ x) (pack η v)] e)))
        (σ (in-hole E (substitute (substitute e ρ η) x v)))
        "let-pack")

   ;; function application
   (--> (σ (in-hole E ((λ x e) v)))
        (σ (in-hole E (substitute e x v)))
        "app")
   ;; location application
   (--> (σ (in-hole E ((Λ ρ e) [η])))
        (σ (in-hole E (substitute e ρ η)))
        "loc-app")))

(define-metafunction L3-dynamics
  eval : e -> v
  [(eval e) ,(cadar (apply-reduction-relation* -->L3 (term ((env) e))))])

;; lrswap example from the paper
(define lrswap
  (term
   (λ r
     (λ x
       (let [(pack ρ cp) r]
         (let [(prod c0 p0) cp]
           (let [(prod p1 p2) (dup p0)]
             (let [(! p2-prime) p2]
               (let [(prod c1 y) (swap p2-prime (prod c0 x))]
                 (prod (pack ρ (prod c1 p1))
                       y))))))))))

(redex-chk
 (eval x) x
 (eval ((λ x x) y)) y
 (eval (let [(prod cp v) ((,lrswap (new x)) y)]
         (let [(pack ρ res) (free cp)]
           res))) y)

(define-extended-language L3-statics L3
  (res ::=
       ✓
       ✗)

  ;; location contexts
  (Δ ::=
     •
     (Δ ρ))

  ;; value contexts
  (Γ ::=
     •
     (Γ (x τ))))

;; written in paper as either x ∈ dom(Γ) or x ∉ dom(Γ) depending on result
;; determines whether or not x is in Γ
(define-judgment-form L3-statics
  #:mode (in I I I O)
  #:contract (in Γ x = res)

  [-------------
   (in • x = ✗)]

  [---------------------
   (in (Γ (x τ)) x = ✓)]

  [(in Γ x = res)
   ----------------------------------------
   (in (Γ (x_!_1 τ)) (name x x_!_1) = res)])

;; written in paper as Γ ⊞ Γ
(define-judgment-form L3-statics
  #:mode (box I I I O)
  #:contract (box Γ Γ = Γ)

  [--------------
   (box • • = •)]

  [(box Γ_1 Γ_2 = Γ_3)
   (in Γ_2 x = ✗)
   ------------------------------------
   (box (Γ_1 (x τ)) Γ_2 = (Γ_3 (x τ)))]

  [(box Γ_1 Γ_2 = Γ_3)
   (in Γ_1 x = ✗)
   ------------------------------------
   (box Γ_1 (Γ_2 (x τ)) = (Γ_3 (x τ)))])

;; returns whether or not the given type is an of-course type
(define-judgment-form L3-statics
  #:mode (!? I I O)
  #:contract (!? τ = res)

  [--------------
   (!? unit = ✗)]

  [--------------------------
   (!? (tensor τ_1 τ_2) = ✗)]

  [---------------------------
   (!? (lolipop τ_1 τ_2) = ✗)]

  [-----------------
   (!? (ptr τ) = ✗)]

  [-------------------
   (!? (cap η τ) = ✗)]

  [-----------------
   (!? (∀ ρ τ) = ✗)]

  [-----------------
   (!? (∃ ρ τ) = ✗)]

  [---------------
   (!? (! τ) = ✓)])

;; written in paper as |Γ|
;; computes Γ with all of-course typed variables removed
(define-judgment-form L3-statics
  #:mode (bars I I O)
  #:contract (bars Γ = Γ)

  [-------------
   (bars • = •)]

  [(bars Γ_1 = Γ_2)
   -----------------------------
   (bars (Γ_1 (x (! τ))) = Γ_2)]

  [(bars Γ_1 = Γ_2)
   (!? τ = ✗)
   -------------------------
   (bars (Γ_1 (x τ)) = Γ_2)])
