Require Import String.

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
| EAssign : qual_ident -> expr
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
Definition lookup {K : Type} {V : Type} (m : map K V) (x : K) := m x.
Definition mem {K : Type} {V : Type} (m : map K V) (x : K) :=
  if m x then true else false.

Definition denv := unit.
Definition kenv := list (unit * kind).
Definition renv := map rgn (ty * frac * pathset).
Definition tenv := map ident rgn.

Definition none := FNat 0.
Definition whole := FNat 1.

Definition eq_rgn (a : rgn) (b : rgn) : bool :=
  match (a, b) with
  | (RConcrete n1, RConcrete n2) => Nat.eqb n1 n2
  end.
Definition rextend {V : Type} := @extend rgn V eq_rgn.
Definition textend {V : Type} := @extend string V (fun s1 s2 =>
                                                     if string_dec s1 s2 then true else false).

(* List.fold_left (fun (acc : Prop * renv * tenv) (pkg : expr * rgn * ty * renv * tenv) =>
                             match (acc, pkg) with
                             | ((prop, rho, gamma), (exp, rgn, tau, rhoPrime, gammaPrime)) =>
                               (prop -> tydev sigma delta rho gamma exp
                                             (TRef rgn whole tau) rhoPrime gammaPrime,
                                rhoPrime, gammaPrime)
                             end) exps (mem rho r = false, rho, gamma)
*)

Definition pkg : Type := expr * rgn * ty * renv * tenv.
Definition proj_exp (pk : pkg) : expr :=
  match pk with
  | (exp, _, _, _, _) => exp
  end.
Definition proj_rgn (pk : pkg) : rgn :=
  match pk with
  | (_, rgn, _, _, _) => rgn
  end.
Definition proj_ty (pk : pkg) : ty :=
  match pk with
  | (_, _, ty, _, _) => ty
  end.

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
    rgn_wf (rextend rho r (tau, whole, PSImmediate tau)) Mut r.

(* typing derivation *)
Inductive tydev :
  denv -> kenv -> renv -> tenv -> expr -> ty -> renv -> tenv -> Prop :=
| T_AllocPrim : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                  (tau : ty) (r : rgn) (p : prim),
    mem rho r = false ->
    tydev sigma delta rho gamma (EPrim p) tau rho gamma ->
    tydev sigma delta rho gamma (EAlloc (EPrim p)) (TRef r whole tau)
          (rextend rho r (tau, whole, PSImmediate tau)) gamma
(* FIXME: I cannot for the life of me figure out how to do n-ary things *)
(* | T_AllocTup : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) *)
(*                  (r : rgn) (pkgs : list pkg), *)
(*     match (List.fold_left (fun (acc : Prop) (pk : pkg) => *)
(*                           acc -> tydev sigma delta rho gamma (proj_exp pk) (proj_ty pk) rho gamma) *)
(*                           pkgs (mem rho r = false)) with *)
(*     | (prop) => *)
(*       prop -> tydev sigma delta rho gamma *)
(*                    (EProd (List.map proj_exp pkgs)) *)
(*                    (TProd (List.map proj_ty pkgs)) *)
(*                    (rextend rho r (TBase TUnit, whole, PSImmediate (TBase TUnit))) *)
(*                    gamma *)
(*     end *)
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
    FDiv f (FNat 2) = fn -> (* FIXME: actual fraction evaluation? *)
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) (EBorrow Imm (id, pi)) (TRef r fn tau)
          (rextend (rextend rho rpi (tau, fn, ps))
                            r (tau, fn, PSAlias rpi)) (textend gamma id rx)
| T_BorrowMut : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
                  (id : ident) (pi : path) (rpi : rgn) (tau : ty) (ps : pathset) (rx : rgn) (r : rgn),
    rgnalongpath rho Mut pi rx tau rpi ->
    lookup rho rpi = Some (tau, whole, ps) ->
    rgn_wf rho Mut rpi ->
    mem rho r = false ->
    tydev sigma delta rho (textend gamma id rx) (EBorrow Mut (id, pi)) (TRef r whole tau)
          (rextend (rextend rho rpi (tau, none, ps))
                            r (tau, whole, PSAlias rpi)) (textend gamma id rx)
| T_True : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv),
    tydev sigma delta rho gamma (EPrim (EBool true)) (TBase TBool) rho gamma
| T_False : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv),
    tydev sigma delta rho gamma (EPrim (EBool false)) (TBase TBool) rho gamma
| T_u32 : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv) (n : nat),
    (n < 256) -> (* FIXME: lol, we should use bit vectors or something *)
    tydev sigma delta rho gamma (EPrim (ENum n)) (TBase TBool) rho gamma
| T_unit : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv),
    tydev sigma delta rho gamma (EPrim (EUnit)) (TBase TUnit) rho gamma
| T_abort : forall (sigma : denv) (delta : kenv) (rho : renv) (gamma : tenv)
              (msg : string) (tau : ty),
    tydev sigma delta rho gamma (EAbort msg) tau rho gamma.