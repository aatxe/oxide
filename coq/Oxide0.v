Require Import String.

(* things that I literally cannot believe are not in the standard library *)

Fixpoint zip {A : Type} {B : Type} (xs : list A) (ys : list B) :=
  match (xs, ys) with
  | (nil, ys) => nil
  | (xs, nil) => nil
  | (cons x xs, cons y ys) => cons (x, y) (zip xs ys)
  end.

Fixpoint zip3 {A : Type} {B : Type} {C : Type} (xs : list A) (ys : list B) (zs : list C) :=
  match (xs, ys, zs) with
  | (cons x xs, cons y ys, cons z zs) => cons (x, y, z) (zip3 xs ys zs)
  | (_, _, _) => nil
  end.

Fixpoint zip4 {A : Type} {B : Type} {C : Type} {D : Type}
         (xs : list A) (ys : list B) (zs : list C) (ws : list D) :=
  match (xs, ys, zs, ws) with
  | (cons x xs, cons y ys, cons z zs, cons w ws) => cons (x, y, z, w) (zip4 xs ys zs ws)
  | (_, _, _, _) => nil
  end.

(* actual mechanization *)

Definition ident := string.

Inductive immpath : Set :=
| Field : ident -> immpath
| Proj : nat -> immpath
| Index : nat -> immpath.

Inductive path : Set :=
| Path : list immpath -> path.

Definition path_cons (Pi : immpath) (pi : path) : path :=
  match pi with
  | Path Pis => Path (Pi :: Pis)
  end.

(* an identifier qualified with a path *)
Definition qual_ident : Set := ident * path.

Inductive muta : Set :=
| Imm : muta
| Mut : muta.

Inductive kind : Set :=
| KStar : kind
| KRgn : kind
| KFrac : kind.

Inductive basety : Set :=
| TBool : basety
| Tu32 : basety
| TUnit : basety.

Inductive rgn : Set :=
| RConcrete : nat -> rgn.
(* FIXME: type vars *)

Inductive frac : Set :=
| FNat : nat -> frac
| FDiv : frac -> frac -> frac
| FAdd : frac -> frac -> frac.
(* FIXME: type vars *)

Inductive struct : Set :=
| SId : ident -> struct.

Inductive enum : Set :=
| EVar : struct -> ident -> enum.

Inductive ty : Set :=
| TBase : basety -> ty
(* FIXME: type vars *)
| TRef : rgn -> frac -> ty -> ty
(* FIXME: univerals *)
| TFn : list (rgn * frac * ty) -> ty -> ty
| TMvFn : list (rgn * frac * ty) -> ty -> ty
| TArray : ty -> nat -> ty
| TSlice : ty -> ty
| TProd : list ty -> ty
| TStruct : struct -> list gty -> ty
with gty : Set :=
(* FIXME: type vars *)
| GType : ty -> gty
| GRgn : rgn -> gty
| GFrac : frac -> gty
| GRgnOf : qual_ident -> gty
| GCapOf : qual_ident -> gty.

Definition ref (prod : rgn * frac * ty) :=
match prod with
| (r, f, t) => TRef r f t
end.

Inductive pat : Set :=
| PWild : pat
| PEnumTup : enum -> list (muta * ident) -> pat
| PEnumRec : enum -> list (ident * muta * ident) -> pat.

Inductive prim : Set :=
| EBool : bool -> prim
| ENum : nat -> prim
| EUnit : prim.

Inductive expr : Set :=
| EPrim : prim -> expr
| EAbort : string -> expr
| EAlloc : expr -> expr
| ECopy : qual_ident -> expr
| EBorrow : muta -> qual_ident -> expr
| ESlice : muta -> qual_ident -> expr -> expr -> expr
| EDrop : qual_ident -> expr
| ELet : muta -> ident -> expr -> expr -> expr
| EAssign : qual_ident -> expr -> expr
(* FIXME: type abstraction *)
| ETApp : expr -> gty -> expr
| EFn : list (ident * rgn * frac * ty) -> expr -> expr
| EMvFn : list (ident * rgn * frac * ty) -> expr -> expr
| EApp : expr -> expr -> expr
| ESeq : expr -> expr -> expr
| EIf : expr -> expr -> expr -> expr
| EMatch : expr -> list (pat * expr) -> expr
| EFor : muta -> ident -> expr -> expr -> expr
| EProd : list expr -> expr
| EArray : list expr -> expr
| EStructRec : struct -> list gty -> list (ident * expr) -> expr
| EStructTup : struct -> list gty -> list expr -> expr
| EEnumRec : enum -> list gty -> list (ident * expr) -> expr
| EEnumTup : enum -> list gty -> list expr -> expr.

Inductive pathset : Set :=
| PSNested : list (immpath * rgn) -> pathset
| PSAlias : rgn -> pathset
| PSImmediate : ty -> pathset.

Definition map (K : Type) (V : Type) := K -> option V.
Definition empty {K : Type} {V : Type} : map K V := fun _ => None.
Definition extend {K : Type} {V : Type} (eq : K -> K -> bool) (m : map K V) (x : K) (v : V) :=
  fun x' => if eq x x' then Some v else m x'.
Definition remove {K : Type} {V : Type} (eq : K -> K -> bool) (m : map K V) (x : K) :=
  fun x' => if eq x x' then None else m x'.
Definition lookup {K : Type} {V : Type} (m : map K V) (x : K) := m x.
Definition mem {K : Type} {V : Type} (m : map K V) (x : K) :=
  if m x then true else false.

Definition denv := unit.
Definition kenv := map unit kind.
Definition renv := map rgn (ty * frac * pathset).
Definition tenv := map ident rgn.

Definition none := FNat 0.
Definition whole := FNat 1.

Definition eq_rgn (a : rgn) (b : rgn) : bool :=
  match (a, b) with
  | (RConcrete n1, RConcrete n2) => Nat.eqb n1 n2
  end.
Definition rextend {V : Type} := @extend rgn V eq_rgn.
Definition rremove {V : Type} := @remove rgn V eq_rgn.
Definition textend {V : Type} := @extend string V (fun s1 s2 =>
                                                     if string_dec s1 s2 then true else false).
Definition tremove {V : Type} := @remove string V (fun s1 s2 =>
                                                     if string_dec s1 s2 then true else false).

Definition textend_lst {V : Type} (m : map string V) (kvs : list (string * V)) :=
  List.fold_left (fun acc pair => @textend V acc (fst pair) (snd pair)) kvs m.

Definition eq_immpath (p1 : immpath) (p2 : immpath) : bool :=
  match (p1, p2) with
  | (Field x, Field y) => if string_dec x y then true else false
  | (Proj n1, Proj n2) => Nat.eqb n1 n2
  | (Index n1, Index n2) => Nat.eqb n1 n2
  | (_, _) => false
  end.
Definition ps_extend (ps : list (immpath * rgn)) (Pi : immpath) (rn : rgn) :=
  cons (Pi, rn) (List.filter (fun pair => eq_immpath (fst pair) Pi) ps).

Inductive rgnalongpath :
  renv -> muta -> path -> rgn -> ty -> rgn -> Prop :=
| PEpsilonPath : forall (rho : renv) (mu : muta) (rg : rgn) (tau : ty) (f : frac),
    (mu = Imm -> f <> none) -> (mu = Mut -> f = whole) ->
    rgnalongpath (rextend rho rg (tau, f, PSImmediate tau)) mu (Path nil) rg tau rg
| PAliasPath : forall (rho : renv) (mu : muta) (pi : path) (r1 : rgn) (tau : ty) (f : frac)
                 (r2 : rgn) (r3 : rgn),
    (mu = Imm -> f <> none) -> (mu = Mut -> f = whole) ->
    rgnalongpath (rextend rho r1 (tau, f, PSAlias r2)) mu pi r2 tau r3 ->
    rgnalongpath (rextend rho r1 (tau, f, PSAlias r2)) mu pi r1 tau r3
| PFieldPath : forall (rho : renv) (mu : muta) (Pi : immpath) (pi : path) (r1 : rgn) (tau : ty) (f : frac)
                 (r2 : rgn) (r3 : rgn) (pathrgns : list (immpath * rgn)),
    (mu = Imm -> f <> none) -> (mu = Mut -> f = whole) ->
    List.In (Pi, r2) pathrgns -> 
    rgnalongpath (rextend rho r1 (tau, f, PSNested pathrgns)) mu pi r2 tau r3 ->
    rgnalongpath (rextend rho r1 (tau, f, PSNested pathrgns)) mu (path_cons Pi pi) r1 tau r3.

Inductive rgn_wf :
  renv -> muta -> rgn -> Prop :=
| WF_ImmEpsilonRegion : forall (rho : renv) (f : frac) (r : rgn) (tau : ty),
    f <> none -> 
    rgn_wf (rextend rho r (tau, f, PSImmediate tau)) Imm r
| WF_MutEpsilonRegion : forall (rho : renv) (r : rgn) (tau : ty),
    rgn_wf (rextend rho r (tau, whole, PSImmediate tau)) Mut r
| WF_ImmAliasRegion : forall (rho : renv) (r1 : rgn) (r2 : rgn) (tau : ty) (f : frac),
    f <> none ->
    rgn_wf (rextend rho r1 (tau, f, PSAlias r2)) Imm r2 ->
    rgn_wf (rextend rho r1 (tau, f, PSAlias r2)) Imm r1
| WF_MutAliasRegion : forall (rho : renv) (r1 : rgn) (r2 : rgn) (tau : ty),
    rgn_wf (rextend rho r1 (tau, whole, PSAlias r2)) Imm r2 ->
    rgn_wf (rextend rho r1 (tau, whole, PSAlias r2)) Imm r1
| WF_ImmNestedRegion : forall (rho : renv) (r : rgn) (tau : ty) (f : frac)
                         (pathrgns : list (immpath * rgn)),
    f <> none ->
    (forall (rPrime : rgn),
        mem rho rPrime = true -> rgn_wf (rextend rho r (tau, f, PSNested pathrgns)) Imm rPrime) ->
    rgn_wf (rextend rho r (tau, f, PSNested pathrgns)) Imm r
| WF_MutNestedRegion : forall (rho : renv) (r : rgn) (tau : ty) (pathrgns : list (immpath * rgn)),
    (forall (rPrime : rgn),
        mem rho rPrime = true -> rgn_wf (rextend rho r (tau, whole, PSNested pathrgns)) Mut rPrime) ->
    rgn_wf (rextend rho r (tau, whole, PSNested pathrgns)) Mut r.

(* kind derivation *)
Inductive kindev :
  denv -> kenv -> renv -> tenv -> gty -> kind -> Prop :=
(* TODO: K-TyVar *)
| K_ConcreteRegion : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (n : nat),
    mem rho (RConcrete n) = true ->
    kindev sigma delta rho gamma (GRgn (RConcrete n)) KRgn
| K_ConcreteFrac : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (f : frac),
    kindev sigma delta rho gamma (GFrac f) KFrac
| K_RgnOf : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident) (rx : rgn)
              (pi : path) (tau : ty) (r : rgn),
    rgnalongpath rho Imm pi rx tau r ->
    kindev sigma delta rho (textend gamma id rx) (GRgnOf (id, pi)) KRgn
| K_CapOf : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident) (rx : rgn)
              (pi : path) (tau : ty) (r : rgn),
    rgnalongpath rho Imm pi rx tau r ->
    kindev sigma delta rho (textend gamma id rx) (GCapOf (id, pi)) KFrac
| K_BaseType : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (bt : basety),
    kindev sigma delta rho gamma (GType (TBase bt)) KStar
| K_Ref : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
            (r : rgn) (f : frac) (tau : ty),
    kindev sigma delta rho gamma (GRgn r) KRgn ->
    kindev sigma delta rho gamma (GFrac f) KFrac ->
    kindev sigma delta rho gamma (GType tau) KStar ->
    kindev sigma delta rho gamma (GType (TRef r f tau)) KStar
(* TODO: K-Closure, K-MoveClosure, K-Universal, K-Tuple, K-Struct *).

(* NOTE(dbp 2018-04-24): We keep the initial and final rho/gamma -- the list of
exprs transforms the former _into_ the latter as it typechecks.  *)
Inductive WTList : denv -> kenv -> renv -> tenv -> list expr -> list ty -> renv -> tenv -> Prop :=
| WTEmpty : forall (sigma : denv) (delt : kenv) (rho : renv) (gamma : tenv),
    WTList sigma delt rho gamma nil nil rho gamma
| WTCons : forall (sigma : denv) (delta : kenv)
             (es : list expr) (ts : list ty)
             (rho1 : renv) (gamma1 : tenv)
             (rho2 : renv) (gamma2 : tenv)
             (rho3 : renv) (gamma3 : tenv)
             (e : expr) (t : ty)
             (wt : WTList sigma delta rho2 gamma2 es ts rho3 gamma3),
    tydev sigma delta rho1 gamma1 e t rho2 gamma2 ->
    WTList sigma delta rho1 gamma1 (e::es) (t::ts) rho3 gamma3
              
(* typing derivation *)
with tydev :
  denv -> kenv -> renv -> tenv -> expr -> ty -> renv -> tenv -> Prop :=
| T_AllocPrim : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                  (tau : ty) (r : rgn) (p : prim),
    mem rho r = false ->
    tydev sigma delta rho gamma (EPrim p) tau rho gamma ->
    tydev sigma delta rho gamma (EAlloc (EPrim p)) (TRef r whole tau)
          (rextend rho r (tau, whole, PSImmediate tau)) gamma
| T_AllocTup : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                 (rhoN : renv) (gammaN : tenv)
                 (r : rgn) (exps : list expr) (rgns : list rgn) (tys : list ty),
    mem rho r = false ->
    WTList sigma delta rho gamma exps
           (List.map ref (zip3 rgns (List.repeat whole (List.length tys)) tys))
           rhoN gammaN ->
    tydev sigma delta rho gamma (EProd exps) (TProd tys)
          (rextend rhoN r (TProd tys, whole,
                           PSNested (zip (List.map Proj (List.seq 0 (List.length rgns)))
                                         rgns)))
          gammaN
| T_AllocArray : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                   (rhoN : renv) (gammaN : tenv)
                   (r : rgn) (exps : list expr) (rgns : list rgn) (tau : ty),
    mem rho r = false ->
    WTList sigma delta rho gamma exps
           (List.map ref (zip3 rgns
                               (List.repeat whole (List.length rgns))
                               (List.repeat tau (List.length rgns))))
           rhoN gammaN ->
    tydev sigma delta rho gamma (EArray exps) (TArray tau (List.length exps))
          (rextend rhoN r (TArray tau (List.length exps), whole,
                           PSNested (zip (List.map Index (List.seq 0 (List.length rgns)))
                                         rgns)))
          gammaN
| T_AllocStructTup : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                       (rhoN : renv) (gammaN : tenv)
                       (r : rgn) (exps : list expr) (rgns : list rgn) (tys : list ty)
                       (s : struct) (gtys : list gty),
    mem rho r = false ->
    WTList sigma delta rho gamma exps
           (List.map ref (zip3 rgns (List.repeat whole (List.length tys)) tys))
           rhoN gammaN ->
    (* TODO: check struct type validity *)
    tydev sigma delta rho gamma (EStructTup s gtys exps) (TStruct s gtys)
          (rextend rhoN r (TStruct s gtys, whole,
                           PSNested (zip (List.map Proj (List.seq 0 (List.length rgns)))
                                         rgns)))
          gammaN
| T_AllocStructRec : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                       (rhoN : renv) (gammaN : tenv)
                       (r : rgn) (exps : list expr) (rgns : list rgn) (tys : list ty)
                       (s : struct) (gtys : list gty) (fields : list ident),
    mem rho r = false ->
    WTList sigma delta rho gamma exps
           (List.map ref (zip3 rgns (List.repeat whole (List.length tys)) tys))
           rhoN gammaN ->
    (* TODO: check struct type validity *)
    tydev sigma delta rho gamma (EStructRec s gtys (zip fields exps)) (TStruct s gtys)
          (rextend rhoN r (TStruct s gtys, whole,
                           PSNested (zip (List.map Field fields)
                                         rgns)))
          gammaN
| T_AllocEnumTup : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                       (rhoN : renv) (gammaN : tenv)
                       (r : rgn) (exps : list expr) (rgns : list rgn) (tys : list ty)
                       (s : struct) (variant : ident) (gtys : list gty),
    mem rho r = false ->
    WTList sigma delta rho gamma exps
           (List.map ref (zip3 rgns (List.repeat whole (List.length tys)) tys))
           rhoN gammaN ->
    (* TODO: check struct type validity *)
    tydev sigma delta rho gamma (EEnumTup (EVar s variant) gtys exps) (TStruct s gtys)
          (rextend rhoN r (TStruct s gtys, whole,
                           PSNested (zip (List.map Proj (List.seq 0 (List.length rgns)))
                                         rgns)))
          gammaN
| T_AllocEnumRec : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                       (rhoN : renv) (gammaN : tenv)
                       (r : rgn) (exps : list expr) (rgns : list rgn) (tys : list ty)
                       (s : struct) (variant : ident) (gtys : list gty) (fields : list ident),
    mem rho r = false ->
    WTList sigma delta rho gamma exps
           (List.map ref (zip3 rgns (List.repeat whole (List.length tys)) tys))
           rhoN gammaN ->
    (* TODO: check struct type validity *)
    tydev sigma delta rho gamma (EEnumRec (EVar s variant) gtys (zip fields exps)) (TStruct s gtys)
          (rextend rhoN r (TStruct s gtys, whole,
                           PSNested (zip (List.map Field fields)
                                         rgns)))
          gammaN
| T_Copy : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
             (id : ident) (pi : path) (r : rgn) (tau : ty) (f : frac) (ps : pathset) (rx : rgn),
    rgnalongpath rho Imm pi rx tau r ->
    lookup rho r = Some (tau, f, ps) ->
    f <> none ->
    (exists (bt : basety), tau = TBase bt) ->
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) (ECopy (id, pi)) (TRef r whole tau)
          (rextend rho r (tau, whole, ps)) (textend gamma id rx)
| T_BorrowImm : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                  (id : ident) (pi : path) (rpi : rgn) (tau : ty) (f : frac) (ps : pathset)
                  (rx : rgn) (fn : frac) (r : rgn),
    rgnalongpath rho Imm pi rx tau rpi ->
    lookup rho rpi = Some (tau, f, ps) ->
    rgn_wf rho Imm rpi ->
    FDiv f (FNat 2) = fn -> (* FIXME(awe 2018-04-19): actual fraction evaluation? *)
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) (EBorrow Imm (id, pi)) (TRef r fn tau)
          (rextend (rextend rho rpi (tau, fn, ps))
                   r (tau, fn, PSAlias rpi)) (textend gamma id rx)
| T_BorrowMut : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident) (pi : path)
                  (rpi : rgn) (tau : ty) (ps : pathset) (rx : rgn) (r : rgn),
    rgnalongpath rho Mut pi rx tau rpi ->
    lookup rho rpi = Some (tau, whole, ps) ->
    rgn_wf rho Mut rpi ->
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) (EBorrow Mut (id, pi)) (TRef r whole tau)
          (rextend (rextend rho rpi (tau, none, ps))
                   r (tau, whole, PSAlias rpi)) (textend gamma id rx)
| T_SliceImm : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident) (rx : rgn)
                 (pi : path) (e1 : expr) (e2 : expr) (r : rgn) (fn : frac) (tau : ty) (rpi : rgn)
                 (f : frac) (ps : pathset) (n : nat) (rho1 : renv) (rho2 : renv) (gamma1 : tenv)
                 (gamma2 : tenv) (r1 : rgn) (r2 : rgn) (f1 : frac) (f2 : frac),
    rgnalongpath rho Imm pi rx (TArray tau n) rpi ->
    lookup rho rpi = Some (TArray tau n, f, ps) ->
    FDiv f (FNat 2) = fn -> (* FIXME(awe 2018-04-19): actual fraction evaluation? *)
    rgn_wf rho Imm rpi ->
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) e1 (TRef r1 f1 (TBase Tu32)) rho1 gamma1 ->
    tydev sigma delta rho1 gamma1 e2 (TRef r2 f2 (TBase Tu32)) rho2 gamma2 ->
    tydev sigma delta rho (textend gamma id rx) (ESlice Imm (id, pi) e1 e2) (TRef r fn (TSlice tau))
          (rextend (rextend rho2 rpi (TSlice tau, fn, ps))
                   r (TSlice tau, fn, PSAlias rpi)) (textend gamma2 id rx)
| T_SliceMut : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident) (rx : rgn)
                 (pi : path) (e1 : expr) (e2 : expr) (r : rgn) (tau : ty) (rpi : rgn) (ps : pathset)
                 (n : nat) (rho1 : renv) (rho2 : renv) (gamma1 : tenv) (gamma2 : tenv) (r1 : rgn)
                 (r2 : rgn) (f1 : frac) (f2 : frac),
    rgnalongpath rho Mut pi rx (TArray tau n) rpi ->
    lookup rho rpi = Some (TArray tau n, whole, ps) ->
    rgn_wf rho Mut rpi ->
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) e1 (TRef r1 f1 (TBase Tu32)) rho1 gamma1 ->
    tydev sigma delta rho1 gamma1 e2 (TRef r2 f2 (TBase Tu32)) rho2 gamma2 ->
    tydev sigma delta rho (textend gamma id rx) (ESlice Mut (id, pi) e1 e2)
          (TRef r whole (TSlice tau))
          (rextend (rextend rho2 rpi (TSlice tau, none, ps))
                   r (TSlice tau, whole, PSAlias rpi)) (textend gamma2 id rx)
| T_Drop : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident) (pi : path)
             (rx : rgn) (r : rgn) (fx : frac) (fr : frac) (fn : frac) (tx : ty) (tr : ty)
             (ps : pathset),
    pi = Path nil -> (* TODO(awe 2018-04-19): fix drop rules for paths, this is also a problem in
                       LaTeX *)
    lookup rho rx = Some (tx, fx, PSAlias r) ->
    lookup rho r = Some (tr, fr, ps) ->
    FAdd fx fr = fn -> (* FIXME(awe 2018-04-19): actual fraction evaluation? *)
    tydev sigma delta rho gamma (EDrop (id, pi)) (TBase TUnit)
          (rextend rho r (tr, fn, ps)) gamma
| T_FreeImmediate : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident)
                      (pi : path) (rx : rgn) (tau : ty),
    pi = Path nil -> (* TODO(awe 2018-04-19): fix drop rules for paths, this is also a problem in
                       LaTeX *)
    lookup rho rx = Some (tau, whole, PSImmediate tau) ->
    tydev sigma delta rho gamma (EDrop (id, pi)) (TBase TUnit) (rremove rho rx) gamma
| T_Free : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (id : ident)
                      (pi : path) (rx : rgn) (tau : ty) (pathrgns : list (immpath * rgn)),
    pi = Path nil -> (* TODO(awe 2018-04-19): fix drop rules for paths, this is also a problem in
                       LaTeX *)
    lookup rho rx = Some (tau, whole, PSNested pathrgns) ->
    (forall (rPrime : rgn),
        List.In rPrime (List.map snd pathrgns) -> mem rho rPrime = false) ->
    tydev sigma delta rho gamma (EDrop (id, pi)) (TBase TUnit) (rremove rho rx) gamma
| T_True : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv),
    tydev sigma delta rho gamma (EPrim (EBool true)) (TBase TBool) rho gamma
| T_False : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv),
    tydev sigma delta rho gamma (EPrim (EBool false)) (TBase TBool) rho gamma
| T_u32 : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (n : nat),
    (n < 256) -> (* FIXME(awe 2018-04-18): lol, we should use bit vectors or something *)
    tydev sigma delta rho gamma (EPrim (ENum n)) (TBase TBool) rho gamma
| T_unit : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv),
    tydev sigma delta rho gamma (EPrim (EUnit)) (TBase TUnit) rho gamma
| T_abort : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
              (msg : string) (tau : ty),
    tydev sigma delta rho gamma (EAbort msg) tau rho gamma
| T_LetImm : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
               (e1 : expr) (e2 : expr) (rho1 : renv) (rho2 : renv) (id : ident)
               (gamma1 : tenv) (gamma2 : tenv) (r1 : rgn) (f1 : frac)
               (tau1 : ty) (tau2 : ty),
    tydev sigma delta rho gamma e1 (TRef r1 f1 tau1) rho1 gamma1 ->
    f1 <> none ->
    tydev sigma delta rho1 gamma1 e2 tau2 rho2 gamma2 ->
    mem rho2 r1 = false ->
    tydev sigma delta rho gamma (ELet Imm id e1 e2) tau2 rho2 gamma2
| T_LetMut : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
               (e1 : expr) (e2 : expr) (rho1 : renv) (rho2 : renv) (id : ident)
               (gamma1 : tenv) (gamma2 : tenv) (r1 : rgn) (tau1 : ty) (tau2 : ty),
    tydev sigma delta rho gamma e1 (TRef r1 whole tau1) rho1 gamma1 ->
    tydev sigma delta rho1 gamma1 e2 tau2 rho2 gamma2 ->
    mem rho2 r1 = false ->
    tydev sigma delta rho gamma (ELet Mut id e1 e2) tau2 rho2 gamma2
| T_Assign : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
               (id : ident) (Pis : list immpath) (e : expr) (rhoPrime : renv) (gammaPrime : tenv)
               (rx : rgn) (tau : ty) (r : rgn) (ps : list (immpath * rgn)) (rn : rgn) (Pi : immpath),
    rgnalongpath rho Mut (Path Pis) rx tau r ->
    lookup rho r = Some (tau, whole, PSNested ps) ->
    rgn_wf rho Mut r ->
    tydev sigma delta rho (textend gamma id rx) e (TRef rn whole tau) rhoPrime gammaPrime ->
    tydev sigma delta rho (textend gamma id rx)
          (EAssign (id, Path (Pis ++ (cons Pi nil))) e) (TBase TUnit)
          (rextend rhoPrime r (tau, whole, PSNested (ps_extend ps Pi rn))) gammaPrime
| T_AssignEpsilon : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                      (id : ident) (e : expr) (rhoPrime : renv) (gammaPrime : tenv)
                      (rx : rgn) (rn : rgn) (tau : ty) (ps : pathset),
    rgn_wf rho Mut rx ->
    lookup rho rx = Some (tau, whole, ps) ->
    tydev sigma delta rho (textend gamma id rx) e (TRef rn whole tau) rhoPrime gammaPrime ->
    tydev sigma delta rho (textend gamma id rx) (EAssign (id, Path nil) e) (TBase TUnit)
          rhoPrime (textend gamma id rn)
| T_Closure : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                (rhoPrime : renv) (gammaPrime : tenv)
                (args : list ident) (rgns : list rgn) (fracs : list frac) (tys : list ty)
                (body : expr) (tau : ty),
    tydev sigma delta rho (textend_lst gamma (zip args rgns)) body tau rhoPrime gammaPrime ->
    tydev sigma delta rho gamma (EFn (zip4 args rgns fracs tys) body)
          (TFn (zip3 rgns fracs tys) tau) rhoPrime gammaPrime
(* TODO: T-MoveClosure *)
| T_App : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (e1 : expr) (e2 : expr)
            (fnargs : list (rgn * frac * ty)) (tr : ty) (rho1 : renv) (gamma1 : tenv) (rho2 : renv)
            (gamma2 : tenv),
    tydev sigma delta rho gamma e1 (TFn fnargs tr) rho1 gamma1 ->
    tydev sigma delta rho gamma e2 (TProd (List.map ref fnargs)) rho2 gamma2 ->
    tydev sigma delta rho gamma (EApp e1 e2) tr rho2 gamma2
| T_MvApp : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (e1 : expr) (e2 : expr)
            (fnargs : list (rgn * frac * ty)) (tr : ty) (rho1 : renv) (gamma1 : tenv) (rho2 : renv)
            (gamma2 : tenv),
    tydev sigma delta rho gamma e1 (TMvFn fnargs tr) rho1 gamma1 ->
    tydev sigma delta rho gamma e2 (TProd (List.map ref fnargs)) rho2 gamma2 ->
    tydev sigma delta rho gamma (EApp e1 e2) tr rho2 gamma2
| T_Seq : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (e1 : expr) (e2 : expr)
            (t2 : ty) (rho1 : renv) (gamma1 : tenv) (rho2 : renv) (gamma2 : tenv),
    tydev sigma delta rho gamma e1 (TBase TUnit) rho1 gamma1 ->
    tydev sigma delta rho1 gamma1 e2 t2 rho2 gamma2 ->
    tydev sigma delta rho gamma (ESeq e1 e2) t2 rho2 gamma2
| T_If : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (e1 : expr) (e2 : expr)
           (e3 : expr) (r1 : rgn) (f1 : frac) (t : ty) (rho1 : renv) (gamma1 : tenv) (rho2 : renv)
           (rho3 : renv) (rhoPrime : renv),
    tydev sigma delta rho gamma e1 (TRef r1 f1 (TBase TBool)) rho1 gamma1 ->
    f1 <> none ->
    tydev sigma delta rho1 gamma1 e2 t rho2 gamma1 ->
    tydev sigma delta rho1 gamma1 e3 t rho3 gamma1 ->
    (* FIXME(awe 2018-04-20): rho2 and rho3 should be unified into rhoPrime, but I still dunno how
       yet. *)
    tydev sigma delta rho gamma (EIf e1 e2 e3) t rhoPrime gamma1
(* TODO: T-Match *)
| T_ForImm : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (e1 : expr) (r1 : rgn)
               (f1 : frac) (t1 : ty) (rho1 : renv) (gamma1 : tenv) (tau : ty) (ps1 : pathset)
               (r : rgn) (fn : frac) (e2 : expr) (id : ident) (rhoPrime : renv) (rv : rgn),
    tydev sigma delta rho gamma e1 (TRef r1 f1 t1) rho1 gamma1 ->
    (match t1 with TArray te _ | TSlice te => te = tau | _ => False end) ->
    rgn_wf rho1 Imm r1 ->
    f1 <> none ->
    lookup rho1 r1 = Some (t1, f1, ps1) ->
    mem rho1 r = false ->
    (* FIXME(awe 2018-04-25): rv has to be fresh in delta, but we haven't got a def of kenv yet *)
    (* mem delta rv = false -> *)
    FDiv f1 (FNat 2) = fn -> (* FIXME(awe 2018-04-20): actual fraction evaluation? *)
    rhoPrime = (rextend (rextend rho1 r1 (t1, fn, ps1)) r (tau, fn, PSAlias rv)) -> 
    (* FIXME(awe 2018-04-25): we need to add rv to delta here with kind RGN *)
    tydev sigma delta rhoPrime (textend gamma1 id r) e2 (TBase TUnit) rhoPrime gamma1 ->
    tydev sigma delta rho gamma (EFor Imm id e1 e2) (TBase TUnit)
          rhoPrime gamma1
| T_ForMut : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (e1 : expr) (r1 : rgn)
               (t1 : ty) (rho1 : renv) (gamma1 : tenv) (tau : ty) (ps1 : pathset) (r : rgn)
               (fn : frac) (e2 : expr) (id : ident) (rhoPrime : renv) (rv : rgn),
    tydev sigma delta rho gamma e1 (TRef r1 whole t1) rho1 gamma1 ->
    (match t1 with TArray te _ | TSlice te => te = tau | _ => False end) ->
    rgn_wf rho1 Mut r1 ->
    lookup rho1 r1 = Some (t1, whole, ps1) ->
    mem rho1 r = false ->
    (* FIXME(awe 2018-04-25): rv has to be fresh in delta, but we haven't got a def of kenv yet *)
    (* mem delta rv = false -> *)
    rhoPrime = (rextend (rextend rho1 r1 (t1, none, ps1)) r (tau, whole, PSAlias rv)) -> 
    (* FIXME(awe 2018-04-25): we need to add rv to delta here with kind RGN *)
    tydev sigma delta rhoPrime (textend gamma1 id r) e2 (TBase TUnit) rhoPrime gamma1 ->
    tydev sigma delta rho gamma (EFor Mut id e1 e2) (TBase TUnit)
          rhoPrime gamma1
(* TODO: T-TAbs, T-TApp *).