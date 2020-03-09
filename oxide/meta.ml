open Syntax
open Util

(* checks that omega_prime is at least omega *)
let is_at_least (omega : owned) (omega_prime : owned) : bool =
  match (omega, omega_prime) with
  | (Shared, _) -> true
  | (Unique, Unique) -> true
  | (Unique, Shared) -> false

(* use the path to decompose a type into a context and an inner type *)
let rec decompose_by (path : path) (ty : ty) : (ty_ctx * ty) tc =
  let (loc, ty) = ty
  in match (ty, path) with
  | (ty, []) -> Succ ((inferred, Hole), (loc, ty))
  | (Rec pairs, (Field f) :: path) ->
    let* (inner_ctx, inner_ty) = List.assoc f pairs |> decompose_by path
    in let replace (pair : field * ty) : field * ty_ctx =
      if fst pair = f then (f, inner_ctx) else (fst pair, (pair |> snd |> fst, Ty (snd pair)))
    in let ctx : ty_ctx = (loc, Rec (List.map replace pairs))
    in Succ (ctx, inner_ty)
  | (Tup tys, (Index n) :: path) ->
    let* (inner_ctx, ty) = List.nth tys n |> decompose_by path
    in let replace (idx : int) (ty : ty) : ty_ctx =
      if idx = n then inner_ctx else (fst ty, Ty ty)
    in let ctx : ty_ctx = (loc, Tup (List.mapi replace tys))
    in Succ (ctx, ty)
  | (Struct (name, provs, tys, Some ty), path) ->
    let* (inner_ctx, ty) = decompose ty path
    in let ctx : ty_ctx = (loc, Tagged (name, provs, tys, inner_ctx))
    in Succ (ctx, ty)
  | (Uninit ty, path) -> PartiallyMovedPath (ty, path) |> fail
  | (ty, path) -> InvalidOperationOnType (path, (loc, ty)) |> fail
and decompose (ty : ty) (path : path) : (ty_ctx * ty) tc = decompose_by path ty

let rec plug (fill : ty) (ctx : ty_ctx) : ty =
  let (loc, ctx) = ctx
  in match ctx with
  | Hole -> fill
  | Ty ty -> ty
  | Tagged (tag, provs, tys, ctx) -> (loc, Struct (tag, provs, tys, Option.some $ plug fill ctx))
  | Rec pair -> (loc, Rec (List.map (fun (f, ctx) -> (f, plug fill ctx)) pair))
  | Tup ctx -> (loc, Tup (List.map (plug fill) ctx))

(* var env operations *)

let var_env_lookup (gamma : var_env) (pi : place) : ty tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty ->
    let* (_, ty) = decompose ty path
    in Succ ty
  | None -> UnboundPlace pi |> fail

let var_env_lookup_root (gamma : var_env) (pi : place) : ty tc =
  let (root, _) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty -> Succ ty
  | None -> UnboundPlace pi |> fail

let var_env_lookup_expr_root (gamma : var_env) (phi : place_expr) : ty tc =
  let (root, _) = snd phi
  in match List.assoc_opt root gamma with
  | Some ty -> Succ ty
  | None -> UnboundPlaceExpr phi |> fail

let var_env_lookup_many (gamma : var_env) (pis : place list) : ty list tc =
  let lookup_seq (pi : place) (tys : ty list) : ty list tc =
    let* ty = var_env_lookup gamma pi
    in List.cons ty tys |> succ
  in foldr lookup_seq pis []

let var_env_lookup_opt (gamma : var_env) (pi : place) : (ty option) tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty ->
    let* (_, ty) = decompose ty path
    in Some ty |> succ
  | None -> Succ None

let var_env_lookup_place_expr (gamma : var_env) (pi : place_expr) : ty tc =
  match place_expr_to_place pi with
  | Some pi -> var_env_lookup gamma pi
  | None -> PlaceExprNotAPlace pi |> fail

let var_env_contains_place_expr (gamma : var_env) (pi : place_expr) : bool =
  let (root, _) = snd pi
  in match List.assoc_opt root gamma with
  | Some _ -> true
  | None -> false

let var_env_type_update (gamma : var_env) (pi : place) (ty : ty) : var_env tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some root_ty ->
    let* (ctx, _) = decompose root_ty path
    in plug ty ctx |> replace_assoc gamma root |> succ
  | None -> UnboundPlace pi |> fail

let var_env_uninit_many (gamma : var_env) (vars : var list) : var_env =
  let work (entry : var * ty) : var * ty =
    if List.mem (fst entry) vars then (fst entry, (inferred, Uninit (snd entry))) else entry
  in List.map work gamma

let var_env_include (gamma : var_env) (x : var) (typ : ty) = List.cons (x, typ) gamma
let var_env_append (gamma1 : var_env) (gamma2 : var_env) = List.append gamma1 gamma2
let var_env_exclude (gamma : var_env) (x : var) = List.remove_assoc x gamma

let var_env_diff (gam1 : var_env) (gam2 : var_env) : var_env =
  let not_in_gam2 (entry1 : var * ty) : bool =
    not $ List.exists (fun entry2 -> fst entry2 = fst entry1) gam2
  in List.filter not_in_gam2 gam1

(* looks up var in gamma, and if the type is a closure, returns its closed over environment *)
let env_of (var : var) (gamma : var_env) : env tc =
  match List.assoc_opt var gamma with
  | Some (_, Fun (_, _, _, _, gamma_c, _, _)) -> Succ gamma_c
  | Some ty -> TypeMismatchFunction ty |> fail
  | None -> UnboundPlace ((dummy, (var, []))) |> fail

(* returns whether or not the given gamma contains the provenance in any types *)
let rec contains_prov (gamma : var_env) (prov : prov) : bool =
  let rec ty_contains (ty : ty) : bool =
    match snd ty with
    | Any | Infer | BaseTy _ | TyVar _ -> false
    | Ref (pv, _, ty) -> snd pv = snd prov || ty_contains ty
    | Fun (_, pvs, _, tys, gam, ret_ty, bounds) ->
      if not $ contains prov pvs then
        ty_contains ret_ty || tys_contains tys ||
        bounds |> List.map fst |> contains prov ||
        bounds |> List.map snd |> contains prov ||
        match gam with
        | Env gam -> contains_prov gam prov
        | Unboxed | EnvVar _ | EnvOf _ -> false
      else false
    | Uninit ty | Array (ty, _) | Slice ty -> ty_contains ty
    | Rec pairs -> List.map snd pairs |> tys_contains
    | Tup tys -> tys_contains tys
    | Struct (_, pvs, _, _) -> List.mem prov pvs
  and tys_contains (tys : ty list) : bool = List.exists ty_contains tys
  in List.exists (ty_contains >> snd) gamma


(* is path2 a prefix of path1? *)
let rec is_prefix_of (path1 : path) (path2 : path) : bool =
  match (path1, path2) with
  | (_, []) -> true
  | ([], _) -> false
  | (Field f1 :: path1, Field f2 :: path2) -> if f1 = f2 then is_prefix_of path1 path2 else false
  | (Index i1 :: path1, Index i2 :: path2) -> if i1 = i2 then is_prefix_of path1 path2 else false
  | (_, _) -> false

let prefix_of (pi1 : place) (pi2 : place) : bool =
  root_of pi1 = root_of pi2 && is_prefix_of (path_of pi1) (path_of pi2)

(* is path2 a prefix of path1? *)
let rec is_expr_prefix_of (path1 : expr_path) (path2 : expr_path) : bool =
  match (path1, path2) with
  | (_, []) -> true
  | ([], _) -> false
  | (Field f1 :: path1, Field f2 :: path2) ->
    if f1 = f2 then is_expr_prefix_of path1 path2 else false
  | (Index i1 :: path1, Index i2 :: path2) ->
    if i1 = i2 then is_expr_prefix_of path1 path2 else false
  | (Deref :: path1, Deref :: path2) -> is_expr_prefix_of path1 path2
  | (_, _) -> false

let expr_prefix_of (phi1 : place_expr) (phi2 : place_expr) : bool =
  expr_root_of phi1 = expr_root_of phi2 && is_expr_prefix_of (expr_path_of phi1) (expr_path_of phi2)

let tyvar_env_add_abs_sub (delta : tyvar_env) (v1 : prov) (v2 : prov) : tyvar_env tc =
  let into_prov (var : prov_var) : prov = delta |> provs_of |> List.find ((=) var >> snd)
  in let is_abs (var : prov_var) : bool = tyvar_env_prov_mem delta (dummy, var)
  in let both_abs ((lhs, rhs) : prov_var * prov_var) : bool = is_abs lhs && is_abs rhs
  in let already_sub ((lhs, rhs) : prov_var * prov_var) : bool =
    tyvar_env_abs_sub delta (dummy, lhs) (dummy, rhs)
  in let trans_extend (cs : subty list) (lhs : prov_var) (rhs : prov_var) : subty list tc =
    let cs = List.cons (lhs, rhs) cs
    in let into_lhs = List.filter (fun cx -> snd cx = lhs) cs
    in let from_rhs = List.filter (fun cx -> fst cx = rhs) cs
    in let new_cs = List.append (List.map (fun cx -> (fst cx, rhs)) into_lhs)
                                (List.map (fun cx -> (lhs, snd cx)) from_rhs)
    in let bad_pairs = new_cs |> List.filter both_abs |> List.filter (not >> already_sub)
    in if is_empty bad_pairs then List.append new_cs cs |> succ
    else let (lhs, rhs) = List.hd bad_pairs
    in AbsProvsNotSubtype (into_prov lhs, into_prov rhs) |> fail
  in let* constraints = trans_extend (bounds_of delta) (snd v1) (snd v2)
  in delta |> tyvar_env_add_bounds constraints |> succ

(* substitutes this for that in ty *)
let subst_env_var (ty : ty) (this : env) (that : env_var) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | Infer | BaseTy _ | TyVar _ -> ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (prov, omega, ty) -> (loc, Ref (prov, omega, sub ty))
    | Fun (evs, pvs, tvs, tys, gamma, ret_ty, bounds) ->
      if not $ List.mem that evs then
        let gammaPrime =
          match gamma with
          | EnvVar ev -> if ev = that then this else gamma
          | Unboxed | Env _ | EnvOf _ -> gamma
        in (loc, Fun (evs, pvs, tvs, sub_many tys, gammaPrime, sub ret_ty, bounds))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      (loc, Struct (name, provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many_env_var (pairs : (env * env_var) list) (ty : ty) : ty =
  List.fold_right (fun pair ty -> subst_env_var ty (fst pair) (snd pair)) pairs ty

(* substitutes this for that in ty *)
let subst_prov (ty : ty) (this : prov) (that : prov) : ty =
  let sub_prov (prov : prov) =  if snd prov = snd that then this else prov
  in let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | Infer | BaseTy _ | TyVar _ -> ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (pv, omega, ty) -> (loc, Ref (sub_prov pv, omega, sub ty))
    | Fun (evs, pvs, tvs, tys, gamma, ret_ty, bounds) ->
      if not $ List.mem that pvs then
        (loc, Fun (evs, pvs, tvs, sub_many tys, gamma, sub ret_ty, sub_bounds bounds))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      let sub_next (pv : prov) (provs : provs) =
        List.cons (if snd pv = snd that then this else pv) provs
      in let new_provs = List.fold_right sub_next provs []
      in (loc, Struct (name, new_provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_bounds (bounds : bounds) : bounds =
    bounds |> List.map (fun (pv1, pv2) -> (sub_prov pv1, sub_prov pv2))
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many_prov (pairs : (prov * prov) list) (ty : ty) : ty =
  List.fold_right (fun pair ty -> subst_prov ty (fst pair) (snd pair)) pairs ty

let subst_many_prov_in_bounds (pairs : (prov * prov) list) (bounds : bounds) : bounds =
  let replace_bounds (bounds : bounds) (this : prov) (that : prov) =
    let replace (prov : prov) = if snd prov = snd that then this else prov
    in bounds |> List.map (fun (pv1, pv2) -> (replace pv1, replace pv2))
  in List.fold_right (fun (this, that) bounds -> replace_bounds bounds this that) pairs bounds

let subst (ty : ty) (this : ty)  (that : ty_var) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | Infer | BaseTy _ -> ty
    | TyVar tv -> if tv = that then this else ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (pv, omega, ty) -> (loc, Ref (pv, omega, sub ty))
    | Fun (evs, pvs, tvs, tys, gamma, ret_ty, bounds) ->
      if not $ List.mem that tvs then
        (loc, Fun (evs, pvs, tvs, sub_many tys, gamma, sub ret_ty, bounds))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      (loc, Struct (name, provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many (pairs : (ty * ty_var) list) (ty : ty) : ty =
  List.fold_right (fun pair ty -> subst ty (fst pair) (snd pair)) pairs ty

let subtype_prov (mode : subtype_modality) (delta : tyvar_env) (ell : loan_env)
    (prov1 : prov) (prov2 : prov) : loan_env tc =
  match (mode, loan_env_lookup_opt ell prov1, loan_env_lookup_opt ell prov2) with
  | (Combine, Some rep1, Some rep2) ->
    (* UP-CombineLocalProvenances*)
    let ellPrime = ell |> loan_env_exclude_all [prov1; prov2]
    in ellPrime |> loan_env_include_all [prov1; prov2] (list_union rep1 rep2) |> succ
  | (Override, Some rep1, Some _) ->
    (* UP-OverrideLocalProvenances *)
    let ellPrime = ell |> loan_env_exclude prov2
    in ellPrime |> loan_env_include prov2 rep1 |> succ
  | (_, None, Some _) ->
    (* UP-AbstractProvLocalProv *)
    if not $ tyvar_env_prov_mem delta prov1 then InvalidProv prov1 |> fail
    else AbsProvsNotSubtype (prov1, prov2) |> fail
  | (_, Some _, None) ->
    (* UP-LocalProvAbstractProv *)
    if not $ tyvar_env_prov_mem delta prov2 then InvalidProv prov2 |> fail
    else CannotPromoteLocalProvToAbstract (prov1, prov2) |> fail
  | (_, None, None) ->
    (* UP-AbstractProvenances *)
    if not $ tyvar_env_prov_mem delta prov1 then InvalidProv prov1 |> fail
    else if not $ tyvar_env_prov_mem delta prov2 then InvalidProv prov2 |> fail
    else if not $ tyvar_env_abs_sub delta prov1 prov2 then AbsProvsNotSubtype (prov1, prov2) |> fail
    else Succ ell

let subtype_prov_many (mode : subtype_modality) (delta : tyvar_env) (ell : loan_env)
    (provs1 : provs) (provs2 : provs) : loan_env tc =
  let* provs = combine_prov "subtype_prov_many" provs1 provs2
  in foldl (fun ell (prov1, prov2) -> subtype_prov mode delta ell prov1 prov2) ell provs

let subtype (mode : subtype_modality) (delta : tyvar_env) (ell : loan_env)
            (ty1 : ty) (ty2 : ty) : loan_env tc =
  let rec sub (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
    match (snd ty1, snd ty2) with
    (* UT-Refl for base types *)
    | (BaseTy bt1, BaseTy bt2) ->
      if bt1 = bt2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Refl for type variables *)
    | (TyVar v1, TyVar v2) ->
      if v1 = v2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Array *)
    | (Array (t1, m), Array (t2, n)) ->
      if m = n then sub ell t1 t2
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Slice *)
    | (Slice t1, Slice t2) -> sub ell t1 t2
    (* UT-SharedRef *)
    | (Ref (v1, Shared, t1), Ref (v2, Shared, t2)) ->
      let* ellPrime = subtype_prov mode delta ell v1 v2
      in sub ellPrime t1 t2
    (* UT-UniqueRef *)
    | (Ref (v1, Unique, t1), Ref (v2, _, t2)) ->
      let* ellPrime = subtype_prov mode delta ell v1 v2
      in let* ell1 = sub ellPrime t1 t2
      in let* ell2 = sub ellPrime t2 t1
      in if canonize ell1 = canonize ell2 then Succ ell2
      else Fail (UnificationFailed (t1, t2))
    (* UT-Tuple *)
    | (Tup tys1, Tup tys2) -> sub_many ell tys1 tys2
    (* UT-Record *)
    | (Rec fields1, Rec fields2) ->
      let fields1 = List.sort (fun x y -> compare (fst x) (fst y)) fields1
      in let fields2 = List.sort (fun x y -> compare (fst x) (fst y)) fields2
      in sub_many ell (List.map snd fields1) (List.map snd fields2)
    (* UT-Struct *)
    | (Struct (name1, provs1, tys1, tagged_ty1), Struct (name2, provs2, tys2, tagged_ty2)) ->
      if name1 = name2 then
        let* ell_provs = subtype_prov_many mode delta ell provs1 provs2
        in let* ell_tys = sub_many ell_provs tys1 tys2
        in sub_opt ell_tys tagged_ty1 tagged_ty2
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Function *)
    | (Fun (evs1, prov1, tyvar1, tys1, _, ret_ty1, bounds1),
       Fun (evs2, prov2, tyvar2, tys2, _, ret_ty2, bounds2)) ->
      let tyvar_for_sub = List.map (fun x -> (inferred, TyVar x)) tyvar1
      in let* ev_sub = combine_evs "UT-Function" (List.map (fun ev -> EnvVar ev) evs1) evs2
      in let* prov_sub = combine_prov "UT-Function" prov1 prov2
      in let* ty_sub = combine_ty "UT-Function" tyvar_for_sub tyvar2
      in let do_sub : ty -> ty =
         subst_many_prov prov_sub >> subst_many ty_sub >> subst_many_env_var ev_sub
      in let alpharenamed_tys2 = List.map do_sub tys2
      in let* ell_prime = sub_many ell alpharenamed_tys2 tys1
      in let alpharenamed_bounds2 = subst_many_prov_in_bounds prov_sub bounds2
      in if eq_bounds bounds1 alpharenamed_bounds2 then sub ell_prime ret_ty1 ret_ty2
      else UnificationFailed (ty1, ty2) |> fail
    (* UT-Bottom *)
    | (Any, _) -> Succ ell
    (* UT-Uninit *)
    | (Uninit ty1, Uninit ty2) -> sub ell ty1 ty2
    (* UT-InitUninit *)
    | (_, Uninit inner_ty) -> sub ell ty1 inner_ty
    (* UT-UninitInit *)
    | (Uninit inner_ty, _) ->
       (match sub ell inner_ty ty2 with
        | Succ _ -> Fail (PartiallyMovedTypes (ty1, ty2))
        | Fail err -> Fail err)
    | (_, _) -> Fail (UnificationFailed (ty1, ty2))
  and sub_many (ell : loan_env) (tys1 : ty list) (tys2 : ty list) : loan_env tc =
    let* tys = combine_tys "subtype_many" tys1 tys2
    in foldl (fun ell (ty1, ty2) -> sub ell ty1 ty2) ell tys
  and sub_opt (ell : loan_env) (ty1 : ty option) (ty2 : ty option) : loan_env tc =
    match (ty1, ty2) with
    | (Some ty1, Some ty2) -> sub ell ty1 ty2
    | (Some _, None) | (None, Some _) | (None, None) -> Succ ell
  in sub ell ty1 ty2

(* invariant subtyping *)
let unify (loc : source_loc) (delta : tyvar_env) (ell : loan_env)
          (ty1 : ty) (ty2 : ty) : (loan_env * ty) tc =
  let* ell1 = subtype Combine delta ell ty1 ty2
  in let* ell2 = subtype Combine delta ell ty2 ty1
  in if loan_env_eq ell1 ell2 then Succ (ell2, ty2)
  else LoanEnvMismatch (loc, ell1, ell2) |> fail

(* invariant subtyping for a sequence of types *)
let unify_many (loc : source_loc) (delta :tyvar_env) (ell : loan_env)
               (tys : ty list) : (loan_env * ty) tc =
  match tys with
  | [] -> Succ (ell, (loc, Any))
  | [ty] -> Succ (ell, ty)
  | ty :: tys ->
    foldl (fun (curr_ell, curr_ty) new_ty -> unify loc delta curr_ell curr_ty new_ty) (ell, ty) tys

(* checks that prov2 outlives prov1, erroring otherwise *)
let rec outlives (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                 (prov1: prov) (prov2 : prov) : loan_env tc =
  match (loan_env_lookup_opt ell prov1, loan_env_lookup_opt ell prov2) with
  | (Some rep1, Some rep2) ->
    let ellPrime = ell |> loan_env_exclude_all [prov1; prov2]
    in ellPrime |> loan_env_include_all [prov1; prov2] (list_union rep1 rep2) |> succ
  | (None, Some loans) ->
    (* true if all the loans are reborrow loans from things that outlive the abstract provenance *)
    if not $ tyvar_env_prov_mem delta prov1 then InvalidProv prov1 |> fail
    else loans |> List.map snd |> map (passed_provs delta ell gamma)
               >>= (succ >> List.flatten)
               >>= foldl (fun ell pv2 ->
                            if snd pv2 <> snd prov2 then outlives delta ell gamma prov1 pv2
                            else ProvDoesNotOutlive (prov1, prov2) |> fail) ell
  | (Some _, None) ->
    if not $ tyvar_env_prov_mem delta prov2 then InvalidProv prov2 |> fail
    else Succ ell
  | (None, None) ->
    (* UP-AbstractProvenances *)
    if not $ tyvar_env_prov_mem delta prov1 then InvalidProv prov1 |> fail
    else if not $ tyvar_env_prov_mem delta prov2 then InvalidProv prov2 |> fail
    else if not $ tyvar_env_abs_sub delta prov1 prov2 then AbsProvsNotSubtype (prov1, prov2) |> fail
    else Succ ell
(* find the type of the expr path based on the original type in a context *)
(* this will error if the context doesn't allow the operation,
   e.g. dereferencing a shared reference in a unique context *)
and compute_with_passed (ctx : owned) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                        (phi : place_expr) : (provs * ty) tc =
  let rec compute (passed : provs) (path : expr_path) (ty : ty)  : (provs * ty) tc =
    match (snd ty, path) with
    | (_, []) -> Succ (passed, ty)
    | (Ref (prov, omega, ty), Deref :: path) ->
      if is_at_least ctx omega then
        let* _ = foldr (fun pv ell -> outlives delta ell gamma pv prov) passed ell
        in compute (List.cons prov passed) path ty
      else Fail (PermissionErr (ty, path, ctx))
    | (Rec pairs, (Field f) :: path) -> List.assoc f pairs |> compute passed path
    | (Tup tys, (Index n) :: path) -> List.nth tys n |> compute passed path
    | (Struct (_, _, _, Some ty), path) -> compute passed path ty
    | (Uninit ty, path) ->
      let* _ = compute passed path ty
      in Fail (PartiallyMovedExprPath (ty, path))
    | (_, path) -> Fail (InvalidOperationOnTypeEP (path, ty))
  in let* root_ty = var_env_lookup_expr_root gamma phi
  in compute [] (expr_path_of phi) root_ty
and passed_provs (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                 (phi : place_expr) : provs tc =
  let* (passed, _) = compute_with_passed Shared delta ell gamma phi
  in Succ passed

let compute_ty_in (ctx : owned) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                  (phi : place_expr) : ty tc =
  let* (_, ty) = compute_with_passed ctx delta ell gamma phi
  in Succ ty

(* find the type of the place expression, assuming a shared use context*)
let compute_ty (delta : tyvar_env) (ell : loan_env) (gamma :var_env) (phi : place_expr) : ty tc =
  compute_ty_in Shared delta ell gamma phi

(* checks that all the outlives bounds are satisfied in delta and ell *)
let check_bounds (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                 (bounds : bounds) : loan_env tc =
  foldl (fun ell (prov1, prov2) -> outlives delta ell gamma prov1 prov2) ell bounds

let envs_minus (keep_provs : provs) (ell : loan_env) (gamma : var_env)
               (pi : place) : (loan_env * var_env) tc =
  let rec loop (envs : loan_env * var_env) (ty : ty option) : (loan_env * var_env) tc =
    match ty with
    | Some (_, Ref (prov, _, ty)) ->
      let* (ell, gamma) = Some ty |> loop envs
      in let new_gamma = pi |> root_of |> var_env_exclude gamma
      in if not $ contains_prov new_gamma prov && not $ contains prov keep_provs then
        Succ (loan_env_exclude prov ell, new_gamma)
      else Succ (ell, new_gamma)
    | Some (_, Any) | Some (_, Infer) | Some (_, BaseTy _) | Some (_, TyVar _) | Some (_, Fun _)
    | Some (_, Struct _) -> Succ envs
    | Some (_, Uninit ty)
    | Some (_, Array (ty, _))
    | Some (_, Slice ty) -> Some ty |> loop envs
    | Some (_, Rec pairs) -> List.map snd pairs |> loops envs
    | Some (_, Tup tys) -> loops envs tys
    | None -> Succ envs
  and loops (envs : loan_env * var_env) = foldl loop envs >> List.map Option.some
  in let pi_as_phi = place_to_place_expr pi
  in let remove_provs (ell : loan_env) : loan_env =
    ell |> List.filter (not >> List.exists (expr_prefix_of |> flip $ pi_as_phi)
                            >> List.map snd >> snd)
  in let* opt = var_env_lookup_opt gamma pi
  in let* (ell_out, gamma_out) = loop (ell, pi |> root_of |> var_env_exclude gamma) opt
  in Succ (remove_provs ell_out, gamma_out)

(* is the given type non-copyable? *)
(* note: this can only error if the type features a struct not defined in sigma *)
let rec noncopyable (sigma : global_env) (typ : ty) : bool tc =
  match snd typ with
  | Any | Infer -> Succ true (* arbitrary types are always _not_ copyable *)
  | BaseTy _ -> Succ false
  | TyVar _ -> Succ true
  | Uninit _ -> Succ true (* probably never ask this question anyway *)
  | Ref (_, Unique, _) -> Succ true
  | Ref (_, Shared, _) -> Succ false
  | Fun (_, _, _, _, env, _, _) -> noncopyable_env sigma env
  | Array (typPrime, _) -> noncopyable sigma typPrime
  | Slice typPrime -> noncopyable sigma typPrime
  | Rec pairs -> any (noncopyable sigma >> snd) pairs
  | Tup typs -> any (noncopyable sigma) typs
  | Struct (name, _, _, _) ->
    match  global_env_find_struct sigma name with
    | Some (Rec (copyable, _, _, _, _)) | Some (Tup (copyable, _, _, _, _)) -> not copyable |> succ
    | None -> Fail (UnknownStruct (fst typ, name))
and noncopyable_env (sigma : global_env) (env : env) : bool tc =
  match env with
  | Unboxed -> Succ true
  | EnvVar _ -> Succ true
  | Env gamma_c -> gamma_c |> List.map snd |> any (noncopyable sigma)
  | EnvOf _ -> Succ true

let copyable (sigma : global_env) (typ : ty) : bool tc =
  let* res = noncopyable sigma typ
  in Succ (not res)

let copyable_env (sigma : global_env) (env : env) : bool tc =
  let* res = noncopyable_env sigma env
  in Succ (not res)

let check_qualifiers (sigma : global_env) (subst : (env * env_var) list) : unit tc =
  let check_qualifier ((env, ev) : env * env_var) : unit tc =
    match ev with
    | (Shared, _) ->
      let* copyable = copyable_env sigma env
      in if copyable then Succ ()
      else UnsatisfiedEnvQualifier (Shared, env) |> fail
    | (Unique, _) -> Succ () (* everything should be good to treat as if it mutates *)
  in for_each subst check_qualifier

let valid_copy_impl (sigma : global_env) (def : struct_def) : unit tc =
  let next_copyable (res : ty option) (typ : ty) : (ty option) tc =
    let* ty_copyable = copyable sigma typ
    in if res == None then
      if ty_copyable then Succ None
      else Succ res
    else Succ (Some typ)
  in match def with
  | Rec (true, name, _, _, fields) ->
    (match List.map snd fields |> foldl next_copyable None with
     | Succ None -> Succ ()
     | Succ (Some ty) -> InvalidCopyImpl (name, ty) |> fail
     | Fail err -> Fail err)
  | Tup (true, name, _, _, tys) ->
    (match foldl next_copyable None tys with
     | Succ None -> Succ ()
     | Succ (Some ty) -> InvalidCopyImpl (name, ty) |> fail
     | Fail err -> Fail err)
  | Rec (false, _, _, _, _) | Tup (false, _, _, _, _) -> Succ ()

let rec free_provs_ty (ty : ty) : provs =
  match snd ty with
  | Any | Infer | BaseTy _ | TyVar _ -> []
  | Uninit ty -> free_provs_ty ty
  | Ref (prov, _, ty) -> free_provs_ty ty |> List.cons prov
  | Fun (_, provs, _, tys, _, ty, bounds) ->
    [tys |> List.map free_provs_ty |> List.flatten;
     free_provs_ty ty;
     bounds |> List.map fst;
     bounds |> List.map snd] |>
    List.concat |> List.filter (fun pv -> provs |> List.map snd |> List.mem (snd pv) |> not)
  | Array (ty, _) | Slice ty -> free_provs_ty ty
  | Rec tys -> tys |> List.map (free_provs_ty >> snd) |> List.flatten
  | Tup tys -> tys |> List.map free_provs_ty |> List.flatten
  | Struct (_, provs, tys, _) -> tys |> List.map free_provs_ty |> List.cons provs |> List.flatten
and free_provs (expr : expr) : provs =
  match snd expr with
  | Prim _ | Move _ | Drop _ | Fn _ | Abort _ | Ptr _ -> []
  | BinOp (_, e1, e2) -> free_provs_many [e1; e2]
  | Borrow (prov, _, _) -> [prov]
  | BorrowIdx (prov, _, _, e) -> free_provs e |> List.cons prov
  | BorrowSlice (prov, _, _, e1, e2) ->
    [e1; e2] |> free_provs_many |> List.cons prov
  | LetProv (provs, e) ->
    free_provs e |> List.filter (fun prov -> provs |> List.map snd |> List.mem (snd prov) |> not)
  | Let (_, ty, e1, e2) ->
    [e1; e2] |> List.map free_provs |> List.cons (free_provs_ty ty) |> List.flatten
  | Assign (_, e) -> free_provs e
  | Seq (e1, e2) -> free_provs_many [e1; e2]
  | Fun (provs, _, params, ret_ty, body) ->
    let free_in_params = params |> List.map (free_provs_ty >> snd) |> List.flatten
    in let free_in_ret =
      match ret_ty with
      | Some ty -> free_provs_ty ty
      | None -> []
    in let free_in_body = free_provs body
    in List.filter (fun prov -> provs |> List.map snd |> List.mem (snd prov) |> not)
                   (List.concat [free_in_params; free_in_ret; free_in_body])
  | App (e1, _, provs, tys, es) ->
    List.concat [free_provs e1; provs;
                 List.map free_provs_ty tys |> List.flatten;
                 free_provs_many es]
  | Idx (_, e) -> free_provs e
  | Branch (e1, e2, e3) ->
    List.concat [free_provs e1; free_provs e2; free_provs e3]
  | While (e1, e2) | For (_, e1, e2) -> free_provs_many [e1; e2]
  | Tup es | Array es -> free_provs_many es
  | RecStruct (_, provs, _, es) ->
    es |> List.map (free_provs >> snd) |> List.cons provs |> List.flatten
  | TupStruct (_, provs, _, es) -> free_provs_many es |> List.append provs
and free_provs_many (exprs : expr list) : provs = exprs |> List.map free_provs |> List.flatten

let free_vars_helper (expr : expr) (should_include : var -> bool tc) : vars tc =
   let rec free (expr : expr) : vars tc =
     match snd expr with
     | Prim _ | Fn _ | Abort _ -> Succ []
     | BinOp (_, e1, e2)
     | While (e1, e2)
     | Seq (e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in List.append free1 free2 |> succ
     | Move (_, (root, _))
     | Drop (_, (root, _))
     | Borrow (_, _, (_, (root, _)))
     | Ptr (_, (_, (root, _))) ->
       let* should_include = should_include root
       in if should_include then Succ [root] else Succ []
     | BorrowIdx (_, _, (_, (root, _)), e1)
     | Idx ((_, (root, _)), e1)
     | Assign ((_, (root, _)), e1) ->
       let* free1 = free e1
       in List.cons root free1 |> succ
     | BorrowSlice (_, _, (_, (root, _)), e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in let* should_include = should_include root
       in List.concat [if should_include then [root] else []; free1; free2] |> succ
     | LetProv (_, e) -> free e
     | Let (x, _, e1, e2)
     | For (x, e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in free2 |> List.filter ((<>) x) |> List.append free1 |> succ
     | Fun (_, _, params, _, body) ->
       let* free = free body
       in free |> List.filter (fun var -> params |> List.map fst |> List.mem var |> not) |> succ
     | App (e1, _, _, _, exprs) ->
       let* frees = free_many exprs
       in let* free1 = free e1
       in List.append free1 frees |> succ
     | Branch (e1, e2, e3) ->
       let* free1 = free e1
       in let* free2 = free e2
       in let* free3 = free e3
       in List.concat [free1; free2; free3] |> succ
     | Tup exprs | Array exprs -> free_many exprs
     | RecStruct _ | TupStruct _ -> Succ [] (* FIXME: implement *)
   and free_many (exprs : expr list) : vars tc =
     let next_free (expr : expr) (free_vars : var list) : vars tc =
       let* free = free expr
       in List.append free free_vars |> succ
     in foldr next_free exprs []
   in free expr

(* all the free variables in expr that are at non-copyable types in gamma *)
(* note: this function can only error if gamma contains struct types not defined in sigma *)
let free_nc_vars (sigma : global_env) (gamma : var_env) (expr : expr) : vars tc =
  free_vars_helper expr
  (fun var ->
     match List.assoc_opt var gamma with
     | Some ty -> noncopyable sigma ty
     (* if it's not in gamma, that means it's local to the expression, thus isn't free *)
     | None -> Succ false)

let free_vars (expr : expr) : vars tc = free_vars_helper expr (fun _ -> Succ true)

let free_provs_var_env : var_env -> provs = List.flatten >> List.map (free_provs_ty >> snd)

(* produces an error if the loans in the given type are found in the parameter list *)
let find_refs_to_params (delta : tyvar_env) (ell : loan_env)
                        (ty : ty) (params : (var * ty) list) : unit tc =
  let place_in_params (pi : place) : bool = List.mem_assoc (root_of pi) params
  in let rec impl (ty : ty) : unit tc =
    match snd ty with
    | Any | Infer | BaseTy _ | TyVar _ -> Succ ()
    | Ref (prov, _, ty) ->
      let loans_opt = loan_env_lookup_opt ell prov
      in (match loans_opt with
      | Some loans ->
        let borrow_loans = loans |> List.map snd |> List.filter_map place_expr_to_place
        in let param_loans = borrow_loans |> List.filter place_in_params
        in if is_empty param_loans then impl ty
        else NoReferenceToParameter (List.hd param_loans) |> fail
      | None ->
        if tyvar_env_prov_mem delta prov then Succ ()
        else InvalidProv prov |> fail)
    | Fun _ -> Succ ()
    | Array (ty, _) | Slice ty -> impl ty
    | Rec fields -> fields |> List.map snd |> for_each_rev impl
    | Tup tys -> for_each_rev impl tys
    | Struct (_, _, _, Some ty) -> impl ty
    | Struct _ | Uninit _ -> Succ ()
  in impl ty

let find_refs_to_captured (delta : tyvar_env) (ell : loan_env)
                          (ty : ty) (gamma_c : var_env) : unit tc =
  match find_refs_to_params delta ell ty gamma_c with
  | Fail (NoReferenceToParameter pi) -> NoReferenceToCaptured pi |> fail
  | res -> res

(* type equality, ignoring the source locations *)
let rec ty_eq (ty1 : ty) (ty2 : ty) : bool =
  match (snd ty1, snd ty2) with
  | (Any, Any) | (Infer, Infer) -> true
  | (BaseTy b1, BaseTy b2) -> b1 = b2
  | (TyVar a1, TyVar a2) -> a1 = a2
  | (Ref (p1, o1, ty1), Ref (p2, o2, ty2)) -> snd p1 = snd p2 && o1 = o2 && ty_eq ty1 ty2
  | (Fun (evs1, pvs1, tyvs1, tys1, env1, ty1, bs1), Fun (evs2, pvs2, tyvs2, tys2, env2, ty2, bs2)) ->
    evs1 = evs2 && List.map snd pvs1 = List.map snd pvs2 && tyvs1 = tyvs2 &&
    List.for_all2 ty_eq tys1 tys2 && env1 = env2 && ty_eq ty1 ty2 &&
    List.map (snd >> fst) bs1 = List.map (snd >> fst) bs2 &&
    List.map (snd >> snd) bs1 = List.map (snd >> snd) bs2
  | (Array (ty1, len1), Array (ty2, len2)) -> len1 = len2 && ty_eq ty1 ty2
  | (Slice ty1, Slice ty2) -> ty_eq ty1 ty2
  | (Rec fields1, Rec fields2) ->
    List.for_all2 ty_eq (fields1 |> List.sort compare_keys |> List.map snd)
                        (fields2 |> List.sort compare_keys |> List.map snd)
  | (Tup tys1, Tup tys2) -> List.for_all2 ty_eq tys1 tys2
  | (Struct (sn1, pvs1, tys1, opt_ty1), Struct (sn2, pvs2, tys2, opt_ty2)) ->
    sn1 = sn2 && List.map snd pvs1 = List.map snd pvs2 &&
    List.for_all2 ty_eq tys1 tys2 && Option.equal ty_eq opt_ty1 opt_ty2
  | (Uninit ty1, Uninit ty2) -> ty_eq ty1 ty2
  | _ -> false

let union (ell1 : loan_env) (ell2 : loan_env) : loan_env =
  let combine (acc : loan_env) (entry : prov * loans) : loan_env =
    let (prov, loans) = entry
    in match loan_env_lookup_opt acc prov with
    | Some curr_loans -> acc |> loan_env_exclude prov
                             |> loan_env_include prov (list_union loans curr_loans)
    | None -> acc |> loan_env_include prov loans
  in List.fold_left combine ell1 ell2

(* return only the common entries, taking uninit types over init types *)
let merge (gamma1: var_env) (gamma2 : var_env) : var_env =
  let merge_entry (name, ty1) =
    match (ty1 |> snd, List.assoc_opt name gamma2) with
    | (Uninit _ , Some ((_, Uninit _) as ty2)) -> if ty_eq ty1 ty2 then Some (name, ty1) else None
    | (Uninit inner, Some ty2) -> if ty_eq inner ty2 then Some (name, ty1) else None
    | (_, Some ty2) -> if ty_eq ty1 ty2 then Some (name, ty1) else None
    | (_, None) -> None
  in gamma1 |> List.map merge_entry |> List.filter Option.is_some |> List.map Option.get

let intersect (envs1 : loan_env * var_env) (envs2 : loan_env * var_env) : loan_env * var_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in let ell = union ell1 ell2
  in (ell, merge gamma1 gamma2)

(* populate the tagged section of struct types based on the global environment *)
let struct_to_tagged (sigma : global_env) : global_env tc =
  let rec do_expr (ctx : struct_var list) (expr : expr) : expr tc =
    let (loc, expr) = expr
    in match expr with
    | Prim _ | Move _ | Drop _ | Borrow _ | Fn _ | Abort _ | Ptr _ -> Succ (loc, expr)
    | BinOp (op, e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, BinOp (op, e1, e2))
    | BorrowIdx (prov, omega, p, e) ->
      let* e = do_expr ctx e
      in Succ (loc, BorrowIdx (prov, omega, p, e))
    | BorrowSlice (prov, omega, p, e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, BorrowSlice (prov, omega, p, e1, e2))
    | LetProv (provs, e) ->
      let* e = do_expr ctx e
      in Succ (loc, LetProv (provs, e))
    | Let (x, ty, e1, e2) ->
      let* ty = do_ty ctx ty
      in let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, Let (x, ty, e1, e2))
    | Assign (p, e) ->
      let* e = do_expr ctx e
      in Succ (loc, Assign (p, e))
    | Seq (e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, Seq (e1, e2))
    | Fun (provs, tyvars, params, res, body) ->
      let* params = do_params ctx params
      in let* res = do_opt_ty ctx res
      in let* body = do_expr ctx body
      in let fn : preexpr = Fun (provs, tyvars, params, res, body)
      in Succ (loc, fn)
    | App (fn, envs, provs, tys, args) ->
      let* fn = do_expr ctx fn
      in let* tys = do_tys ctx tys
      in let* args = do_exprs ctx args
      in Succ (loc, App (fn, envs, provs, tys, args))
    | Idx (p, e) ->
      let* e = do_expr ctx e
      in Succ (loc, Idx (p, e))
    | Branch (e1, e2, e3) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in let* e3 = do_expr ctx e3
      in Succ (loc, Branch (e1, e2, e3))
    | While (e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, While (e1, e2))
    | For (x, e1, e2) ->
      let* e1 = do_expr ctx e1
      in let* e2 = do_expr ctx e2
      in Succ (loc, For (x, e1, e2))
    | Tup exprs ->
      let* exprs = do_exprs ctx exprs
      in let tup : preexpr = Tup exprs
      in Succ (loc, tup)
    | Array exprs ->
      let* exprs = do_exprs ctx exprs
      in let array : preexpr = Array exprs
      in Succ (loc, array)
    | RecStruct (sn, provs, tys, args) ->
      let* tys = do_tys ctx tys
      in let* args = do_args ctx args
      in Succ (loc, RecStruct (sn, provs, tys, args))
    | TupStruct (sn, provs, tys, exprs) ->
      let* tys = do_tys ctx tys
      in let* exprs = do_exprs ctx exprs
      in Succ (loc, TupStruct (sn, provs, tys, exprs))
  and do_ty (ctx : struct_var list) (ty : ty) : ty tc =
    let (loc, ty) = ty
    in match ty with
    (* the interesting case: encountering a struct type *)
    | Struct (sn, provs, tys, None) ->
      let* tys = do_tys ctx tys
      in if List.mem sn ctx then Succ (loc, Struct (sn, provs, tys, None))
      else (match global_env_find_struct sigma sn with
      | Some (Rec (_, _, dfn_provs, tyvars, fields)) ->
        let fields_sorted = List.sort compare_keys fields
        in let* prov_sub = combine_prov "T-RecStruct" provs dfn_provs
        in let* ty_sub = combine_ty "T-RecStruct" tys tyvars
        in let do_sub : ty -> ty = subst_many ty_sub >> subst_many_prov prov_sub
        in let fields_fixed = List.map (fun (f, ty) -> (f, do_sub ty)) fields_sorted
        in let* fields = do_params (List.cons sn ctx) fields_fixed
        in let ty : ty = (inferred, Rec fields)
        in Succ (loc, Struct (sn, provs, tys, Some ty))
      | Some (Tup (_, _, dfn_provs, tyvars, tup_tys)) ->
        let* prov_sub = combine_prov "T-TupStruct" provs dfn_provs
        in let* ty_sub = combine_ty "T-TupStruct" tys tyvars
        in let do_sub : ty -> ty = subst_many ty_sub >> subst_many_prov prov_sub
        in let tup_tys = List.map do_sub tup_tys
        in let* tup_tys = do_tys ctx tup_tys
        in let ty : ty = (inferred, Tup tup_tys)
        in Succ (loc, Struct (sn, provs, tys, Some ty))
      | None -> UnknownStruct (loc, sn) |> fail)
    (* structural cases *)
    | Any | Infer | BaseTy _ | TyVar _ -> Succ (loc, ty)
    | Ref (prov, omega, ty) ->
      let* ty = do_ty ctx ty
      in Succ (loc, Ref (prov, omega, ty))
    | Fun (evs, provs, tyvars, tys, gamma, ty, bounds) ->
      (* should we transform gamma here? maybe not necessary *)
      let* tys = do_tys ctx tys
      in let* ty = do_ty ctx ty
      in let fn : prety = Fun (evs, provs, tyvars, tys, gamma, ty, bounds)
      in Succ (loc, fn)
    | Array (ty, n) ->
      let* ty = do_ty ctx ty
      in let array : prety = Array (ty, n)
      in Succ (loc, array)
    | Slice ty ->
      let* ty = do_ty ctx ty
      in let slice : prety = Slice ty
      in Succ (loc, slice)
    | Rec fields ->
      let* fields = do_params ctx fields
      in let record : prety = Rec fields
      in Succ (loc, record)
    | Tup tys ->
      let* tys = do_tys ctx tys
      in let tup : prety = Tup tys
      in Succ (loc, tup)
    | Struct (sn, provs, tys, Some tagged_ty) ->
      let* tys = do_tys ctx tys
      in let* tagged_ty = do_ty ctx tagged_ty
      in Succ (loc, Struct (sn, provs, tys, Some tagged_ty))
    | Uninit ty ->
      let* ty = do_ty ctx ty
      in let uninit : prety = Uninit ty
      in Succ (loc, uninit)
  and do_exprs (ctx : struct_var list) (exprs : expr list) : expr list tc =
    let do_lifted (expr : expr) (exprs : expr list) : expr list tc =
      let* expr = do_expr ctx expr
      in Succ (List.cons expr exprs)
    in foldr do_lifted exprs []
  and do_args (ctx : struct_var list) (args : (field * expr) list) : (field * expr) list tc =
    let do_lifted (arg : field * expr) (so_far : (field * expr) list) : (field * expr) list tc =
      let* expr = do_expr ctx (snd arg)
      in List.cons (fst arg, expr) so_far |> succ
    in foldr do_lifted args []
  and do_tys (ctx : struct_var list) (tys : ty list) : ty list tc =
    let do_lifted (ty : ty) (tys : ty list) : ty list tc =
      let* ty = do_ty ctx ty
      in List.cons ty tys |> succ
    in foldr do_lifted tys []
  and do_opt_ty (ctx : struct_var list) (ty : ty option) : ty option tc =
    match ty with
    | Some ty -> let* ty = do_ty ctx ty in Some ty |> succ
    | None -> Succ None
  and do_params (ctx : struct_var list) (params : (var * ty) list) : (var * ty) list tc =
    let do_lifted (param : var * ty) (so_far : (var * ty) list) : (var * ty) list tc =
      let* ty = do_ty ctx (snd param)
      in List.cons (fst param, ty) so_far |> succ
    in foldr do_lifted params []
  and do_global_entry (ctx : struct_var list) (entry : global_entry) : global_entry tc =
    match entry with
    | FnDef (fn, evs, provs, tyvars, params, ret_ty, bounds, body) ->
      let* params = do_params ctx params
      in let* ret_ty = do_ty ctx ret_ty
      in let* body = do_expr ctx body
      in Succ (FnDef (fn, evs, provs, tyvars, params, ret_ty, bounds, body))
    | RecStructDef (copyable, sn, provs, tyvars, fields) ->
      let* fields = do_params ctx fields
      in Succ (RecStructDef (copyable, sn, provs, tyvars, fields))
    | TupStructDef (copyable, sn, provs, tyvars, tys) ->
      let* tys = do_tys ctx tys
      in Succ (TupStructDef (copyable, sn, provs, tyvars, tys))
  and do_global_entries (ctx : struct_var list) (entries : global_env) : global_env tc =
    let do_lifted (entry : global_entry) (entries : global_env) : global_env tc =
      let* entry = do_global_entry ctx entry
      in List.cons entry entries |> succ
    in foldr do_lifted entries []
  in do_global_entries [] sigma
