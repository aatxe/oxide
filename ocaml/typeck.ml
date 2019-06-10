open Syntax
open Meta

let omega_safe (ell : loan_env) (gamma : place_env) (omega : owned) (pi : place_expr) : (ty * loans) option =
  failwith "unimplemented"
  (* if is_safe ell gamma omega pi then Some (List.assoc pi gamma)
   * else None *)

let unify_prov (ell : loan_env) (prov1 : prov) (prov2 : prov) : loan_env * prov =
  match (prov1, prov2) with
  | (ProvVar v1, ProvVar v2) ->
    let (rep1, rep2) = (loan_env_lookup ell v1, loan_env_lookup ell v2)
    in (loan_env_include ell v1 (List.append rep1 rep2), prov1)
  | (ProvSet loans1, ProvSet loans2) -> (ell, ProvSet (List.append loans1 loans2))
  | _ ->  failwith "unreachable?"

let unify (loc : source_loc) (ell : loan_env) (ty1 : ty) (ty2 : ty) : (loan_env * ty) tc =
  let rec uni (ell : loan_env) (ty1 : ty) (ty2 : ty) (swapped : bool) : (loan_env * ty) tc =
    match (ty1, ty2, swapped) with
    | (BaseTy bt1, BaseTy bt2, _) ->
      if bt1 = bt2 then Succ (ell, BaseTy bt1)
      else Fail (UnificationFailed (loc, ty1, ty2))
    | (TyVar v1, TyVar v2, _) ->
      if v1 = v2 then Succ (ell, TyVar v1)
      else Fail (UnificationFailed (loc, ty1, ty2))
    | (Array (t1, m), Array (t2, n), _) ->
      if m = n then
        match uni ell t1 t2 false with
        | Succ (ellPrime, ty) -> Succ (ellPrime, Array (ty, n))
        | Fail err -> Fail err
      else Fail (UnificationFailed (loc, ty1, ty2))
    | (Slice t1, Slice t2, _) ->
      (match uni ell t1 t2 false with
       | Succ (ellPrime, ty) -> Succ (ellPrime, Slice ty)
       | Fail err -> Fail err)
    | (Tup tys1, Tup tys2, _) ->
      (let work (acc : (loan_env * ty list) tc) (tys : ty * ty) =
         match acc with
         | Fail err -> Fail err 
         | Succ (ell, tylst) ->
           (let (ty1, ty2) = tys
            in match uni ell ty1 ty2 false with
            | Succ (ellPrime, ty) -> Succ (ellPrime, List.append tylst [ty])
            | Fail err -> Fail err)
       in match List.fold_left work (Succ (ell, [])) (List.combine tys1 tys2) with
       | Succ (ellPrime, tys) -> Succ (ellPrime, Tup tys)
       | Fail err -> Fail err)
    | (Ref (v1, o1, t1), Ref (v2, o2, t2), _) ->
      if o1 = o2 then
        match unify_prov ell (ProvVar v1) (ProvVar v2) with
        | (_, ProvSet _) -> failwith "unreachable"
        | (ellPrime, ProvVar prov) ->
          match uni ellPrime t1 t2 false with
          | Succ (ellFinal, ty) -> Succ (ellFinal, Ref (prov, o1, ty))
          | Fail err -> Fail err 
      else Fail (UnificationFailed (loc, ty1, ty2))
    | (Any, ty, _) -> Succ (ell, ty)
    | (ty1, ty2, false) -> uni ell ty2 ty1 true
    | (_, _, true) -> Fail (UnificationFailed (loc, ty1, ty2))
  in uni ell ty1 ty2 false

let unify_many (loc : source_loc) (ell : loan_env) (tys : ty list) : (loan_env * ty) tc =
  match tys with
  | [] -> Succ (ell, Any)
  | [ty] -> Succ (ell, ty)
  | ty :: tys ->
    let work (acc : (loan_env * ty) tc) (new_ty : ty) =
      match acc with
      | Succ (curr_ell, curr_ty) -> unify loc curr_ell curr_ty new_ty
      | Fail err -> Fail err
    in List.fold_left work (Succ (ell, ty)) tys

let intersect (envs1 : loan_env * place_env) (envs2 : loan_env * place_env) : loan_env * place_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in failwith "unimplemented"

let place_env_diff (gam1 : place_env) (gam2 : place_env) : place_env =
  let not_in_gam2 (entry1 : place * ty) = not (List.exists (fun entry2 -> fst entry2 = fst entry1) gam2)
  in List.filter not_in_gam2 gam1

let valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env) (ty : ty) : unit tc =
  failwith "unimplemented"

let type_of (prim : prim) : ty =
  match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
               (expr : expr) : (ty * loan_env * place_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
             (expr : expr) : (ty * loan_env * place_env) tc =
    match snd expr with
    | Prim prim -> Succ (type_of prim, ell, gamma)
    | Move pi ->
      (match omega_safe ell gamma Unique pi with
       | Some (ty, [(Unique, pi)]) -> Succ (ty, ell, if noncopyable ty then place_env_subtract gamma pi else gamma)
       | Some _ -> failwith "unreachable"
       | None -> Fail (SafetyErr (fst expr, Unique, pi)))
    | Borrow (prov, omega, pi) ->
      (match omega_safe ell gamma omega pi with
       | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
       | None -> Fail (SafetyErr (fst expr, omega, pi)))
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e with
       | Succ (BaseTy U32, ell1, gamma1) ->
         (match omega_safe ell1 gamma1 omega pi with
          | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
          | None -> Fail (SafetyErr (fst expr, omega, pi)))
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e, BaseTy U32, found))
       | Fail err -> Fail err)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (BaseTy U32, ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ (BaseTy U32, ell2, gamma2) ->
            (match omega_safe ell2 gamma2 omega pi with
             | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
             | None -> Fail (SafetyErr (fst expr, omega, pi)))
          | Succ (found, _, _) -> Fail (TypeMismatch (fst e2, BaseTy U32, found))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e1, BaseTy U32, found))
       | Fail err -> Fail err)
    | Idx (pi, e) ->
      (match tc delta ell gamma e with
       | Succ (BaseTy U32, ell1, gamma1) ->
         (match omega_safe ell1 gamma1 Shared pi with
          | Some (Array (ty, _), _) ->
            if copyable ty then Succ (ty, ell1, gamma1)
            else Fail (CannotMove (fst expr, pi))
          | Some (found, _) -> Fail (TypeMismatch (fst expr, Array (Any, -1), found))
          | None -> Fail (SafetyErr (fst expr, Shared, pi)))
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e, BaseTy U32, found))
       | Fail err -> Fail err)
    | Seq (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (_, ell1, gamma1) -> tc delta ell1 gamma1 e2
       | Fail err -> Fail err)
    | Branch (e1, e2, e3) ->
      (match tc delta ell gamma e1 with
       | Succ (BaseTy Bool, ell1, gamma1) ->
         (match (tc delta ell1 gamma1 e2, tc delta ell1 gamma1 e3) with
          | (Succ (ty2, ell2, gamma2), Succ (ty3, ell3, gamma3)) ->
            (let (ellPrime, gammaPrime) = intersect (ell2, gamma2) (ell3, gamma3)
             in match unify (fst expr) ellPrime ty2 ty3 with
             | Fail err -> Fail err
             | Succ (ellFinal, tyFinal) ->
               match valid_type sigma delta ellFinal gammaPrime tyFinal with
               | Succ () -> Succ (tyFinal, ellFinal, gammaPrime)
               | Fail err -> Fail err)
          | (Fail err, _) | (_, Fail err) -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e1, BaseTy Bool, found))
       | Fail err -> Fail err)
    | LetProv (new_provars, e) ->
      let (provars, tyvars) = delta
      in let to_loan_entry (var : prov_var) : prov_var * loans = (var, [])
      in let deltaPrime = (List.append new_provars provars, tyvars)
      in let ellPrime = List.append (List.map to_loan_entry provars) ell
      in tc deltaPrime ellPrime gamma e
    | Let (var, ann_ty, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (ty1, ell1, gamma1) ->
         (match unify (fst expr) ell1 ty1 (snd ann_ty) with
          | Succ (ell1Prime, ty) ->
            let gam_ext = places_typ (Var var) ty
            in (match tc delta ell1Prime (List.append gam_ext gamma1) e2 with
                | Succ (ty2, ell2, gamma2) -> Succ (ty2, ell2, place_env_exclude gamma2 (Var var))
                | Fail err -> Fail err)
          | Fail err -> Fail err)
       | Fail err -> Fail err)
    | Assign (pi, e) ->
      (match omega_safe ell gamma Unique pi with
       | Some (ty_old, loans) ->
         (match tc delta ell gamma e with
          | Succ (ty_update, ell1, gamma1) ->
            (match unify (fst expr) ell1 ty_old ty_update with
             | Succ (ellPrime, ty_new) ->
               let places = List.map snd loans
               in let work (acc : place_env) (pi : place) =
                    List.append (places_typ pi ty_new) acc
               in let gammaPrime = List.fold_left work gamma1 places
               in Succ (BaseTy Unit, ellPrime, gammaPrime)
             | Fail err -> Fail err)
          | Fail err -> Fail err)
       | None -> Fail (SafetyErr (fst expr, Unique, pi)))
    | Abort _ -> failwith "unimplemented abort"
    | For (var, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (Array (elem_ty, _), ell1, gamma1) ->
         let gam_ext = places_typ (Var var) elem_ty
         in (match tc delta ell1 (List.append gam_ext gamma1) e2 with
             | Succ (_, ell2, gamma2) ->
               let gamma2Prime = place_env_exclude gamma2 (Var var)
               in if gamma2Prime = gamma1 then
                 if ell1 = ell2 then Succ (BaseTy Unit, ell2, gamma2)
                 else Fail (LoanEnvMismatch (fst e2, ell1, ell2))
               else Fail (PlaceEnvMismatch (fst e2, gamma1, gamma2Prime))
             | Fail err -> Fail err)
       | Succ (Ref (prov, omega, Slice elem_ty), ell1, gamma1) ->
         let gam_ext = places_typ (Var var) (Ref (prov, omega, elem_ty))
         in (match tc delta ell1 (List.append gam_ext gamma1) e2 with
             | Succ (_, ell2, gamma2) ->
               let gamma2Prime = place_env_exclude gamma2 (Var var)
               in if gamma2Prime = gamma1 then
                 if ell1 = ell2 then Succ (BaseTy Unit, ell2, gamma2)
                 else Fail (LoanEnvMismatch (fst e2, ell1, ell2))
               else Fail (PlaceEnvMismatch (fst e2, gamma1, gamma2Prime))
             | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatchIterable (fst e1, found))
       | Fail err -> Fail err)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, provs, tyvars, params, ret_ty, _) ->
         let fn_ty : ty = Fun (provs, tyvars, List.map snd params, [], ret_ty)
         in Succ (fn_ty, ell, gamma)
       | None -> Fail (UnknownFunction (fst expr, fn)))
    | Fun (provs, tyvars, params, body) ->
      let sndsnd (p : 'a * ('b * 'c)) : 'c = snd (snd p)
      in let places_typ_u (pair : var * ann_ty) = places_typ (Var (fst pair)) (sndsnd pair)
      in let gam_ext = List.fold_right List.append (List.map places_typ_u params) []
      in let deltaPrime = (List.append provs (fst delta), List.append tyvars (snd delta))
      in (match tc deltaPrime ell (List.append gam_ext gamma) body with
          | Succ (ret_ty, ellPrime, gammaPrime) ->
            let gamma_c = place_env_diff gamma gammaPrime
            in let fn_ty : ty = Fun (provs, tyvars, List.map sndsnd params, gamma_c, ret_ty)
            in Succ (fn_ty, ellPrime, gammaPrime)
          | Fail err -> Fail err)
    | App (fn, provs, tys, args) ->
      (match tc delta ell gamma fn with
       | Succ (Fun (provars, tyvars, params, _, ret_ty), ellF, gammaF) ->
         (match tc_many delta ellF gammaF args with
          | Succ (arg_tys, ellN, gammaN) ->
            let ty_pairs = List.combine params arg_tys (* TODO: substitution on params *)
            in let types_match (tys : ty * ty) : bool =
                 let (expected, found) = tys
                 in expected = found
            in (match List.find_opt types_match ty_pairs with
                | None -> Succ (ret_ty, ellN, gammaN) (* TODO: substitution on ret_ty *)
                | Some (expected, found) -> Fail (TypeMismatch (fst expr, expected, found)))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatchFunction (fst fn, found))
       | Fail err -> Fail err)
    | Tup exprs ->
      (match tc_many delta ell gamma exprs with
       | Succ (tys, ellPrime, gammaPrime) -> Succ (Tup tys, ellPrime, gammaPrime)
       | Fail err -> Fail err)
    | Array exprs ->
      (match tc_many delta ell gamma exprs with
       | Succ (tys, ellPrime, gammaPrime) ->
         (match unify_many (fst expr) ellPrime tys with
          | Succ (ellFinal, unified_ty) ->
            Succ (Array (unified_ty, List.length tys), ellFinal, gammaPrime)
          | Fail err -> Fail err)
       | Fail err -> Fail err)
    | _ -> failwith "unimplemented"
  and tc_many (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
      (exprs : expr list) : (ty list * loan_env * place_env) tc =
    let work (acc : (ty list * loan_env * place_env) tc) (e : expr) =
      match acc with
      | Fail err -> Fail err
      | Succ (curr_tys, curr_ell, curr_gamma) ->
        match tc delta curr_ell curr_gamma e with
        | Succ (ty, ellPrime, gammaPrime) -> Succ (List.cons ty curr_tys, ellPrime, gammaPrime)
        | Fail err -> Fail err
    in List.fold_left work (Succ ([], ell, gamma)) exprs
  in tc delta ell gamma expr
