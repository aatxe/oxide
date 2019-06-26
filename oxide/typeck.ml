open Syntax
open Meta
open Util

(* substitutes this for that in ty *)
let subst_prov (ty : ty) (this : prov) (that : prov) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ | TyVar _ -> ty
    | Ref (pv, omega, ty) ->
      let prov = if (snd pv) = (snd that) then this else pv
      in (loc, Ref (prov, omega, sub ty))
    | Fun (pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that pvs) then (loc, Fun (pvs, tvs, sub_many tys, gamma, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Tup tys -> (loc, Tup (sub_many tys))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  in sub ty

let subst_many_prov (ty : ty) (pairs : (prov * prov) list) : ty =
  List.fold_right (fun pair ty -> subst_prov ty (fst pair) (snd pair)) pairs ty

let subst (ty : ty) (this : ty)  (that : ty_var) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ -> ty
    | TyVar tv -> if tv = that then this else ty
    | Ref (pv, omega, ty) -> (loc, Ref (pv, omega, sub ty))
    | Fun (pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that tvs) then (loc, Fun (pvs, tvs, sub_many tys, gamma, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Tup tys -> (loc, Tup (sub_many tys))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  in sub ty

let subst_many (ty : ty) (pairs : (ty * ty_var) list) : ty =
  List.fold_right (fun pair ty -> subst ty (fst pair) (snd pair)) pairs ty

let subtype_prov (mode : subtype_modality) (ell : loan_env)
    (prov1 : prov) (prov2 : prov) : loan_env tc =
  match (mode, loan_env_lookup_opt ell prov1, loan_env_lookup_opt ell prov2) with
  | (Combine, Some rep1, Some rep2) ->
    (* U-CombineLocalProvenances*)
    let ellPrime = loan_env_exclude ell prov2
    in Succ (loan_env_include ellPrime prov2 (list_union rep1 rep2))
  | (Override, Some rep1, Some _) ->
    (* U-OverrideLocalProvenances *)
    let ellPrime = loan_env_exclude ell prov2
    in Succ (loan_env_include ellPrime prov2 rep1)
  | (_, None, Some _) ->
    (* U-AbstractProvLocalProv *)
    if loan_env_abs_sub ell prov1 prov2 then Succ ell
    else Fail (InvalidProv prov1)
  | (_, Some _, None) ->
    (* U-LocalProvAbstractProv *)
    let ellPrime = loan_env_add_abs_sub ell prov1 prov2
    in Succ ellPrime
  | (_, None, None) ->
    (* U-AbstractProvenances *)
    if not (loan_env_is_abs ell prov1) then
      Fail (InvalidProv prov1)
    else if not (loan_env_is_abs ell prov2) then
      Fail (InvalidProv prov2)
    else if not (loan_env_abs_sub ell prov1 prov2) then
      Fail (AbsProvsNotSubtype (prov1, prov2))
    else Succ ell

let subtype (mode : subtype_modality) (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
  let rec sub (ell : loan_env) (ty1 : ty) (ty2 : ty) (swapped : bool) : loan_env tc =
    match (snd ty1, snd ty2, swapped) with
    | (BaseTy bt1, BaseTy bt2, _) ->
      if bt1 = bt2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    | (TyVar v1, TyVar v2, _) ->
      if v1 = v2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    | (Array (t1, m), Array (t2, n), _) ->
      if m = n then sub ell t1 t2 false
      else Fail (UnificationFailed (ty1, ty2))
    | (Slice t1, Slice t2, _) -> sub ell t1 t2 false
    | (Tup tys1, Tup tys2, _) ->
      let work (acc : loan_env tc) (tys : ty * ty) =
        match acc with
        | Fail err -> Fail err
        | Succ ell ->
          let (ty1, ty2) = tys
          in sub ell ty1 ty2 false
      in List.fold_left work (Succ ell) (List.combine tys1 tys2)
    | (Ref (v1, o1, t1), Ref (v2, o2, t2), _) ->
      if o1 = o2 then
        match subtype_prov mode ell v1 v2 with
        | Succ ellPrime -> sub ellPrime t1 t2 false
        | Fail err -> Fail err
      else Fail (UnificationFailed (ty1, ty2))
    | (Any, _, _) -> Succ ell
    | (_, _, false) -> sub ell ty2 ty1 true
    | (_, _, true) -> Fail (UnificationFailed (ty1, ty2))
  in sub ell ty1 ty2 false

let unify (loc : source_loc) (ell : loan_env) (ty1 : ty) (ty2 : ty) : (loan_env * ty) tc =
  match (subtype Combine ell ty1 ty2, subtype Combine ell ty2 ty1) with
  | (Fail err, _) -> Fail err
  | (_, Fail err) -> Fail err
  | (Succ ell1, Succ ell2) ->
    if ell1 = ell2 then Succ (ell2, ty2)
    else Fail (LoanEnvMismatch (loc, ell1, ell2))

let unify_many (loc : source_loc) (ell : loan_env) (tys : ty list) : (loan_env * ty) tc =
  match tys with
  | [] -> Succ (ell, (loc, Any))
  | [ty] -> Succ (ell, ty)
  | ty :: tys ->
    let work (acc : (loan_env * ty) tc) (new_ty : ty) =
      match acc with
      | Succ (curr_ell, curr_ty) -> unify loc curr_ell curr_ty new_ty
      | Fail err -> Fail err
    in List.fold_left work (Succ (ell, ty)) tys

let union (ell1 : loan_env) (ell2 : loan_env) : loan_env =
  let work (acc : loan_env) (pair : prov_var * loans) : loan_env =
    let (prov, loans) = pair
    in match loan_env_lookup_opt acc (dummy, prov) with
    | Some curr_loans ->
      loan_env_include (loan_env_exclude acc (dummy, prov))
        (dummy, prov) (list_union loans curr_loans)
    | None -> loan_env_include acc (dummy, prov) loans
  in let (prt1, (prt2, prt3)) = List.fold_left work ell1 (fst ell2)
  in (prt1, (list_union prt2 (sndfst ell2), list_union prt3 (sndsnd ell2)))

let intersect (envs1 : loan_env * place_env) (envs2 : loan_env * place_env) : loan_env * place_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in let ell = union ell1 ell2
  in let also_in_gamma2 (pair : place * ty) =
       let (pi, ty) = pair
       in match place_env_lookup_opt gamma2 pi with
       | Some ty2 -> ty == ty2 (* TODO: maybe unify, but then were changing ell *)
       | None -> false
  in (ell, List.find_all also_in_gamma2 gamma1)

let place_env_diff (gam1 : place_env) (gam2 : place_env) : place_env =
  let not_in_gam2 (entry1 : place * ty) = not (List.exists (fun entry2 -> fst entry2 = fst entry1) gam2)
  in List.filter not_in_gam2 gam1

let valid_prov (_ : tyvar_env) (ell : loan_env) (gamma : place_env) (prov : prov) : unit tc =
  (* FIXME: check tyvar_env_prov_mem, but then we need to add letprovs to programs in codegen *)
  if loan_env_mem ell prov then
    match loan_env_lookup_opt ell prov with
    | Some loans ->
      let invalid_loans = List.filter (fun p -> place_env_contains_spec gamma (snd p)) loans
      in (match invalid_loans with
      | [] -> Succ ()
      | (omega, pi) :: _ -> Fail (InvalidLoan (fst prov, omega, pi)))
    | None -> Fail (InvalidProv prov)
  else if loan_env_is_abs ell prov then Succ ()
  else Fail (InvalidProv prov)

let valid_type (_ : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env) (ty : ty) : unit tc =
  let rec valid (ty : ty) : unit tc =
    match snd ty with
    | Any -> Succ ()
    | BaseTy _ -> Succ ()
    | TyVar tyvar ->
      if List.mem tyvar (snd delta) then Succ ()
      else Fail (InvalidType ty)
    | Ref (prov, _, ty) ->
      (match valid_prov delta ell gamma prov with
       | Succ () ->
         (match valid ty with
          | Succ () ->
            let mismatched_tys =
              List.find_all (fun (_, pi) -> place_env_lookup_spec gamma pi != ty)
                (loan_env_lookup ell prov)
            in (match mismatched_tys with
                | [] -> Succ ()
                | (_, pi) :: _ -> Fail (TypeMismatch (ty, place_env_lookup_spec gamma pi)))
          | Fail err -> Fail err)
       | Fail err -> Fail err)
    | Fun _ -> failwith "unimplemented"
    | Array (typ, n) -> if n >= 0 then valid typ else Fail (InvalidArrayLen (ty, n))
    | Slice typ -> valid typ
    | Tup tys -> valid_many tys
  and valid_many (tys : ty list) =
    let work (ty : ty) (acc : unit tc) =
      match acc with
      | Succ () -> valid ty
      | Fail err -> Fail err
    in List.fold_right work tys (Succ ())
  in valid ty

let type_of (prim : prim) : ty =
  (inferred, match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool)

let omega_safe (ell : loan_env) (gamma : place_env) (omega : owned)
    (pi : source_loc * place_expr) : (ty * loans) tc =
  match eval_place_expr (fst pi) ell gamma omega (snd pi) with
  | Succ loans ->
    let safe_then_ty (loan : loan) : ty option * loan =
      match is_safe ell gamma omega (snd loan) with
      | None ->
        (Some (place_env_lookup_spec gamma (snd loan)), loan)
      | Some possible_conflicts ->
        (* the reason these are only _possible_ conflicts is essentially reborrows *)
        match List.find_opt (fun loan -> not (List.mem loan loans)) possible_conflicts with
        | Some loan -> (None, loan) (* in this case, we've found a _real_ conflict *)
        | None -> (* but here, the only conflict are precisely loans being reborrowed *)
          let hd = List.hd possible_conflicts
          in if is_at_least omega (fst hd) then (Some (place_env_lookup_spec gamma (snd hd)), loan)
          else (None, loan)
    in let opt_tys = List.map safe_then_ty loans
    in (match List.assoc_opt None opt_tys with
        | Some (o, place) -> Fail (SafetyErr (fst pi, (omega, snd pi), (o, place)))
        | None ->
          let tys = List.map (fun pair -> unwrap (fst pair)) opt_tys
          in match unify_many (fst pi) ell tys with
          | Succ (ellPrime, ty) ->
            if ellPrime = ell then Succ (ty, uniq_cons (omega, snd pi) loans)
            else Fail (LoanEnvMismatch (fst pi, ell, ellPrime))
          | Fail err -> Fail err)
  | Fail err -> Fail err

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
               (expr : expr) : (ty * loan_env * place_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
             (expr : expr) : (ty * loan_env * place_env) tc =
    match snd expr with
    | Prim prim -> Succ (type_of prim, ell, gamma)
    | BinOp (op, e1, e2) ->
      (match binop_to_types op with
       | (Some lhs_ty, Some rhs_ty, out_ty) ->
         (match tc delta ell gamma e1 with
          | Succ (t1, ell1, gamma1) ->
            if t1 = lhs_ty then match tc delta ell1 gamma1 e2 with
             | Succ (t2, ell2, gamma2) ->
               if t2 = rhs_ty then match unify (fst expr) ell2 t1 t2 with
                | Succ (ellFinal, _) -> Succ (out_ty, ellFinal, gamma2)
                | Fail err -> Fail err
               else Fail (TypeMismatch (rhs_ty, t2))
             | Fail err -> Fail err
            else Fail (TypeMismatch (lhs_ty, t1))
          | Fail err -> Fail err)
       | (None, None, out_ty) ->
         (match tc delta ell gamma e1 with
          | Succ (t1, ell1, gamma1) ->
            (match tc delta ell1 gamma1 e2 with
             | Succ (t2, ell2, gamma2) ->
               (match unify (fst expr) ell2 t1 t2 with
                | Succ (ellFinal, _) -> Succ (out_ty, ellFinal, gamma2)
                | Fail err -> Fail err)
             | Fail err -> Fail err)
          | Fail err -> Fail err)
       | _ -> failwith "unreachable")
    | Move pi ->
      (match omega_safe ell gamma Unique (fst expr, pi) with
       | Succ (ty, [(Unique, pi)]) ->
         let (ellPrime, gammaPrime) =
           match place_expr_to_place pi with
           | Some pi ->
             if noncopyable ty then envs_minus ell gamma pi
             else (ell, gamma)
           | None -> failwith "unreachable"
         in Succ (ty, ellPrime, gammaPrime)
       | Succ (_, loans) ->
         Format.printf "%a@." pp_loans loans;
         failwith "unreachable"
       | Fail err -> Fail err)
    | Borrow (prov, omega, pi) ->
      (match omega_safe ell gamma omega (fst expr, pi) with
       | Succ (ty, loans) ->
         Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
       | Fail err -> Fail err)
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match omega_safe ell1 gamma1 omega (fst expr, pi) with
          | Succ (ty, loans) ->
            Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ ((_, BaseTy U32), ell2, gamma2) ->
            (match omega_safe ell2 gamma2 omega (fst expr, pi) with
             | Succ (ty, loans) ->
               Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
             | Fail err -> Fail err)
          | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    | Idx (pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match omega_safe ell1 gamma1 Shared (fst expr, pi) with
          | Succ ((_, Array (ty, _)), _) ->
            if copyable ty then Succ (ty, ell1, gamma1)
            else Fail (CannotMove (fst expr, pi))
          | Succ (found, _) -> Fail (TypeMismatch ((dummy, Array ((dummy, Any), -1)), found))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    | Seq (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (_, ell1, gamma1) -> tc delta ell1 gamma1 e2
       | Fail err -> Fail err)
    | Branch (e1, e2, e3) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
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
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    | LetProv (new_provs, e) ->
      let (provs, tyvars) = delta
      in let to_loan_entry (var : prov) : prov_var * loans = (snd var, [])
      in let deltaPrime = (list_union new_provs provs, tyvars)
      in let ellPrime = loan_env_append (List.map to_loan_entry provs, ([], [])) ell
      in tc deltaPrime ellPrime gamma e
    | Let (var, ann_ty, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (ty1, ell1, gamma1) ->
         (match subtype Combine ell1 ty1 ann_ty with
          | Succ ell1Prime ->
            let gam_ext = places_typ (Var var) ann_ty
            in (match tc delta ell1Prime (place_env_append gam_ext gamma1) e2 with
                | Succ (ty2, ell2, gamma2) ->
                  let (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (Var var)
                  in Succ (ty2, ell2Prime, gamma2Prime)
                | Fail err -> Fail err)
          | Fail err -> Fail err)
       | Fail err -> Fail err)
    | Assign (pi, e) ->
      (match omega_safe ell gamma Unique (fst expr, pi) with
       | Succ (ty_old, loans) ->
         (match tc delta ell gamma e with
          | Succ (ty_update, ell1, gamma1) ->
            (match subtype Override ell1 ty_update ty_old with
             | Succ ellPrime ->
               let place_opts = List.map (fun loan -> place_expr_to_place (snd loan)) loans
               in let places = List.map unwrap (List.filter (fun opt -> opt != None) place_opts)
               in let work (acc : place_env) (pi : place) =
                    place_env_append (places_typ pi ty_old) acc
               in let gammaPrime = List.fold_left work gamma1 places
               in Succ ((inferred, BaseTy Unit), ellPrime, gammaPrime)
             | Fail err -> Fail err)
          | Fail err -> Fail err)
       | Fail err -> Fail err)
    | Abort _ -> failwith "unimplemented abort"
    | While (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ (_, ell2, gamma2) -> tc delta ell2 gamma2 e2
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    | For (var, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, Array (elem_ty, _)), ell1, gamma1) ->
         let gam_ext = places_typ (Var var) elem_ty
         in (match tc delta ell1 (place_env_append gam_ext gamma1) e2 with
             | Succ (_, ell2, gamma2) ->
               let (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (Var var)
               in if gamma2Prime = gamma1 then
                 if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
                 else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
               else Fail (PlaceEnvMismatch (fst e2, gamma1, gamma2Prime))
             | Fail err -> Fail err)
       | Succ ((_, Ref (prov, omega, (_, Slice elem_ty))), ell1, gamma1) ->
         let gam_ext = places_typ (Var var) (inferred, Ref (prov, omega, elem_ty))
         in (match tc delta ell1 (place_env_append gam_ext gamma1) e2 with
             | Succ (_, ell2, gamma2) ->
               let (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (Var var)
               in if gamma2Prime = gamma1 then
                 if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
                 else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
               else Fail (PlaceEnvMismatch (fst e2, gamma1, gamma2Prime))
             | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatchIterable found)
       | Fail err -> Fail err)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, provs, tyvars, params, ret_ty, _) ->
         let fn_ty : ty = (inferred, Fun (provs, tyvars, List.map snd params, [], ret_ty))
         in Succ (fn_ty, ell, gamma)
       | None -> Fail (UnknownFunction (fst expr, fn)))
    | Fun (provs, tyvars, params, opt_ret_ty, body) ->
      let places_typ_u (pair : var * ty) = places_typ (Var (fst pair)) (snd pair)
      in let gam_ext = List.fold_right list_union (List.map places_typ_u params) []
      in let deltaPrime = (list_union provs (fst delta), list_union tyvars (snd delta))
      in let ellPrime = loan_env_bindall ell provs
      in (match tc deltaPrime ellPrime (place_env_append gam_ext gamma) body with
          | Succ (ret_ty, ellPrime, gammaPrime) ->
            let gamma_c = place_env_diff gamma gammaPrime
            in let fn_ty (ret_ty : ty) : ty =
                 (inferred, Fun (provs, tyvars, List.map snd params, gamma_c, ret_ty))
            in (match opt_ret_ty with
                | Some ann_ret_ty ->
                  (match subtype Combine ellPrime ret_ty ann_ret_ty with
                   | Succ ellFinal -> Succ (fn_ty ann_ret_ty, ellFinal, gammaPrime)
                   | Fail err -> Fail err)
                | None -> Succ (fn_ty ret_ty, ellPrime, gammaPrime))
          | Fail err -> Fail err)
    | App (fn, new_provs, new_tys, args) ->
      (match tc delta ell gamma fn with
       | Succ ((_, Fun (provs, tyvars, params, _, ret_ty)), ellF, gammaF) ->
         (match tc_many delta ellF gammaF args with
          | Succ (arg_tys, ellN, gammaN) ->
            let (prov_sub, ty_sub) = (List.combine new_provs provs,
                                      List.combine new_tys tyvars)
            in let do_sub (ty : ty) : ty = (subst_many (subst_many_prov ty prov_sub) ty_sub)
            in let new_params = List.map do_sub params
            in let ty_pairs = List.combine new_params arg_tys
            in let types_match (tys : ty * ty) : bool =
                 let (expected, found) = tys
                 in expected == found (* FIXME: why the heck is this ==? it works this way... *)
            in (match List.find_opt types_match ty_pairs with
                | None ->
                  let new_ret_ty = do_sub ret_ty
                  in (match valid_type sigma delta ellN gammaN new_ret_ty with
                    | Succ () -> Succ (new_ret_ty, ellN, gammaN)
                    | Fail err -> Fail err)
                | Some (expected, found) -> Fail (TypeMismatch (expected, found)))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatchFunction found)
       | Fail err -> Fail err)
    | Tup exprs ->
      (match tc_many delta ell gamma exprs with
       | Succ (tys, ellPrime, gammaPrime) -> Succ ((inferred, Tup tys), ellPrime, gammaPrime)
       | Fail err -> Fail err)
    | Array exprs ->
      (match tc_many delta ell gamma exprs with
       | Succ (tys, ellPrime, gammaPrime) ->
         (match unify_many (fst expr) ellPrime tys with
          | Succ (ellFinal, unified_ty) ->
            Succ ((inferred, Array (unified_ty, List.length tys)), ellFinal, gammaPrime)
          | Fail err -> Fail err)
       | Fail err -> Fail err)
    | Ptr _ -> failwith "unimplemented"
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

let wf_global_env (sigma : global_env) : unit tc =
  let valid_global_entry (acc : unit tc) (entry : global_entry) : unit tc =
    match (acc, entry) with
    | (Fail err, _) -> Fail err
    | (_, FnDef (_, provs, tyvars, params, ret_ty, body)) ->
      let delta = (provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let gamma = List.flatten
             (List.map (fun pair -> places_typ (Var (fst pair)) (snd pair)) params)
      in match type_check sigma delta ell gamma body with
      | Succ (output_ty, ellPrime, _) ->
        (match subtype Combine ellPrime output_ty ret_ty with
        | Succ _ -> Succ ()
        | Fail err -> Fail err)
      | Fail err -> Fail err
  in List.fold_left valid_global_entry (Succ ()) sigma
