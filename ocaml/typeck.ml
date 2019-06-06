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

let unify (ell : loan_env) (ty1 : ty) (ty2 : ty) : (loan_env * ty) option =
  let rec uni (ell : loan_env) (ty1 : ty) (ty2 : ty) (swapped : bool) : (loan_env * ty) option =
    match (ty1, ty2, swapped) with
    | (BaseTy bt1, BaseTy bt2, _) -> if bt1 = bt2 then Some (ell, BaseTy bt1) else None
    | (TyVar v1, TyVar v2, _) -> if v1 = v2 then Some (ell, TyVar v1) else None
    | (Array (t1, m), Array (t2, n), _) ->
      if m = n then
        match uni ell t1 t2 false with
        | Some (ellPrime, ty) -> Some (ellPrime, Array (ty, n))
        | None -> None
      else None
    | (Slice t1, Slice t2, _) ->
      (match uni ell t1 t2 false with
       | Some (ellPrime, ty) -> Some (ellPrime, Slice ty)
       | None -> None)
    | (Tup tys1, Tup tys2, _) ->
      (let work (acc : (loan_env * ty list) option) (tys : ty * ty) =
         match acc with
         | None -> None
         | Some (ell, tylst) ->
           (let (ty1, ty2) = tys
            in match uni ell ty1 ty2 false with
            | Some (ellPrime, ty) -> Some (ellPrime, List.append tylst [ty])
            | None -> None)
       in match List.fold_left work (Some (ell, [])) (List.combine tys1 tys2) with
       | Some (ellPrime, tys) -> Some (ellPrime, Tup tys)
       | None -> None)
    | (Ref (v1, o1, t1), Ref (v2, o2, t2), _) ->
      if o1 = o2 then
        match unify_prov ell (ProvVar v1) (ProvVar v2) with
        | (_, ProvSet _) -> failwith "unreachable"
        | (ellPrime, ProvVar prov) ->
          match uni ellPrime t1 t2 false with
          | Some (ellFinal, ty) -> Some (ellFinal, Ref (prov, o1, ty))
          | None -> None
      else None
    | (ty1, ty2, false) -> uni ell ty2 ty1 true
    | (_, _, true) -> None
  in uni ell ty1 ty2 false

let intersect (envs1 : loan_env * place_env) (envs2 : loan_env * place_env) : loan_env * place_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in failwith "unimplemented"

let valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env) (ty : ty) : () tc =
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
    | Prim prim -> (type_of prim, ell, gamma)
    | Move pi ->
      (match omega_safe ell gamma Unique pi with
       | Some (ty, _) -> Succ (ty, ell, if noncopyable ty then place_env_subtract gamma pi else gamma)
       | None -> Fail (SafetyErr (fst expr, Unique, pi)))
    | Borrow (prov, omega, pi) ->
      (match omega_safe ell gamma omega pi with
       | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
       | None -> Fail (SafetyErr (fst expr, omega, pi)))
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e1 with
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
         (match omega_safe ell1 gamma1 Shrd pi with
          | Some (Array (ty, _), loans) ->
            if copyable ty then Succ (ty, loan_env_include ell prov loans, gamma)
            else Fail (CannotMove (fst expr, pi))
          | Succ (found, _, _) -> Fail (TypeMisMatch (fst expr, Array (TyVar -1, -1), found))
          | None -> Fail (SafetyErr (fst expr, omega, pi)))
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
            (let (ellPrime, gammaPrime) = intersect (ell2, gamma2) (ell3, gamm3)
             in let (ellFinal, tyFinal) = unify ellPrime ty2 ty3
             in match valid_type sigma delta ellFinal gammaPrime tyFinal with
             | Succ () -> (tyFinal, ellFinal, gammaPrime)
             | Fail err -> Fail err)
          | (Fail err, _) | (_, Fail err) -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e1, BaseTy Bool, found))
       | Fail err -> Fail err)
    | LetProv (new_provars, e) ->
      let (provars, tyvars) = delta
      in let to_loan_entry (var : provar) : provar * loans = (var, [])
      in let deltaPrime = (List.append new_provars provars, tyvars)
      in let ellPrime = List.append (List.map to_loan_entry provars) ell
      in tc deltaPrime ellPrime gamma e
    | Let (var, ann_ty, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (ty1, ell1, gamma1) ->
         (match unify ell1 ty1 ann_ty with
          | Some (ell1Prime, ty) ->
            let gam_ext = places_typ (Var var) ty
            in (match tc delta ell1 (List.append gam_ext gamma1) with
                | Succ (ty2, ell2, gamma2) -> (ty2, ell2, place_enc_exclude gamma (Var var))
                | Fail err -> Fail err)
          | None -> Fail (UnificationFailed (ty1, ann_ty)))
       | Fail err -> Fail err)
    | Assign (pi, e) ->
      (match omega_safe ell gamma Uniq pi with
       | Some (ty_old, loans) ->
         (match tc delta ell gamma e with
          | Succ (ty_update, ell1, gamma1) ->
            (match unify ell1 ty_old ty_update with
             | Some (ellPrime, ty_new) ->
               let places = List.map snd loans
               in let work (acc : place_env) (pi : place) =
                    List.append (places_typ pi ty_new) acc
               in let gammaPrime = List.fold_left work gamma1 places
               in Succ (BaseTy Unit, ellPrime, gammaPrime)
             | None -> Fail (UnificationFailed (ty_old, ty_update)))
          | Fail err -> Fail err)
       | None -> Fail (SafetyErr (fst expr, Uniq, pi)))
  | _ -> failwith "unimplemented"
  in tc delta ell gamma expr
