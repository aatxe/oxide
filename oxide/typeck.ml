open Syntax
open Edsl
open Meta
open Util

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
    if not (loan_env_is_abs ell prov1) then Fail (InvalidProv prov1)
    else if loan_env_abs_sub ell prov1 prov2 then Succ ell
    else Fail (InvalidProv prov1)
  | (_, Some _, None) ->
    (* U-LocalProvAbstractProv *)
    if not (loan_env_is_abs ell prov2) then Fail (InvalidProv prov2)
    else let ellPrime = loan_env_add_abs_sub ell prov1 prov2
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

let subtype_prov_many (mode : subtype_modality) (ell : loan_env)
    (provs1 : provs) (provs2 : provs) : loan_env tc =
  let work (acc : loan_env tc) (provs : prov * prov) : loan_env tc =
    let* ell = acc
    in subtype_prov mode ell (fst provs) (snd provs)
  in List.fold_left work (Succ ell) (List.combine provs1 provs2)

let subtype (mode : subtype_modality) (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
  let rec sub (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
    match (snd ty1, snd ty2) with
    | (BaseTy bt1, BaseTy bt2) ->
      if bt1 = bt2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    | (TyVar v1, TyVar v2) ->
      if v1 = v2 then Succ ell
      else Fail (UnificationFailed (ty1, ty2))
    | (Array (t1, m), Array (t2, n)) ->
      if m = n then sub ell t1 t2
      else Fail (UnificationFailed (ty1, ty2))
    | (Slice t1, Slice t2) -> sub ell t1 t2
    | (Tup tys1, Tup tys2) ->
      let work (acc : loan_env tc) (tys : ty * ty) =
        let* ell = acc
        in let (ty1, ty2) = tys
        in sub ell ty1 ty2
      in List.fold_left work (Succ ell) (List.combine tys1 tys2)
    | (Ref (v1, o1, t1), Ref (v2, o2, t2)) ->
      if o1 = o2 then
        let* ellPrime = subtype_prov mode ell v1 v2
        in sub ellPrime t1 t2
      else Fail (UnificationFailed (ty1, ty2))
    | (Struct (name1, provs1, tys1), Struct (name2, provs2, tys2)) ->
      if name1 = name2 then
        let* ell_provs = subtype_prov_many mode ell provs1 provs2
        in sub_many ell_provs tys1 tys2
      else Fail (UnificationFailed (ty1, ty2))
    | (Any, _) -> Succ ell
    | (_, _) -> Fail (UnificationFailed (ty1, ty2))
  and sub_many (ell : loan_env) (tys1 : ty list) (tys2 : ty list) : loan_env tc =
    let work (acc : loan_env tc) (tys : ty * ty) : loan_env tc =
      let* ell = acc
      in sub ell (fst tys) (snd tys)
    in List.fold_left work (Succ ell) (List.combine tys1 tys2)
  in sub ell ty1 ty2

let unify (loc : source_loc) (ell : loan_env) (ty1 : ty) (ty2 : ty) : (loan_env * ty) tc =
  let* ell1 = subtype Combine ell ty1 ty2
  in let* ell2 = subtype Combine ell ty2 ty1
  in if ell1 = ell2 then Succ (ell2, ty2)
  else Fail (LoanEnvMismatch (loc, ell1, ell2))

let unify_many (loc : source_loc) (ell : loan_env) (tys : ty list) : (loan_env * ty) tc =
  match tys with
  | [] -> Succ (ell, (loc, Any))
  | [ty] -> Succ (ell, ty)
  | ty :: tys ->
    let work (acc : (loan_env * ty) tc) (new_ty : ty) =
      let* (curr_ell, curr_ty) = acc
      in unify loc curr_ell curr_ty new_ty
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
      let* () = valid_prov delta ell gamma prov
      in let* () = valid ty
      in let mismatched_tys =
           List.find_all (fun (_, pi) -> place_env_lookup_spec gamma pi != ty)
             (loan_env_lookup ell prov)
      in (match mismatched_tys with
          | [] -> Succ ()
          | (_, pi) :: _ -> Fail (TypeMismatch (ty, place_env_lookup_spec gamma pi)))
    | Fun _ -> failwith "unimplemented"
    | Array (typ, n) -> if n >= 0 then valid typ else Fail (InvalidArrayLen (ty, n))
    | Slice typ -> valid typ
    | Tup tys -> valid_many tys
    | Struct _ -> Succ () (* TODO: use sigma *)
  and valid_many (tys : ty list) =
    let work (ty : ty) (acc : unit tc) =
      let* () = acc in valid ty
    in List.fold_right work tys (Succ ())
  in valid ty

let valid_types (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
    (tys : ty list) : unit tc =
  let valid_ty (ty : ty) (acc : unit tc) =
    let* () = acc in valid_type sigma delta ell gamma ty
  in List.fold_right valid_ty tys (Succ ())

let type_of (prim : prim) : ty =
  (inferred, match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool)

let omega_safe (ell : loan_env) (gamma : place_env) (omega : owned)
    (pi : source_loc * place_expr) : (ty * loans) tc =
  let* loans = eval_place_expr (fst pi) ell gamma omega (snd pi)
  in let safe_then_ty (loan : loan) : (ty option * loan) tc =
       let* res = is_safe (fst pi) ell gamma omega (snd loan)
       in match res with
       | None ->
         Succ (Some (place_env_lookup_spec gamma (snd loan)), loan)
       | Some possible_conflicts ->
         (* the reason these are only _possible_ conflicts is essentially reborrows *)
         match List.find_opt (fun loan -> not (List.mem loan loans)) possible_conflicts with
         | Some loan -> Succ (None, loan) (* in this case, we've found a _real_ conflict *)
         | None -> (* but here, the only conflict are precisely loans being reborrowed *)
           let hd = List.hd possible_conflicts
           in if is_at_least omega (fst hd) then
             Succ (Some (place_env_lookup_spec gamma (snd hd)), loan)
           else Succ (None, loan)
  in let tmp = List.map safe_then_ty loans
  in let opt_tys =
       List.flatten (List.map (fun tc -> match tc with Succ x -> [x] | Fail _ -> []) tmp)
  in match List.find_opt (fun tc -> match tc with Succ _ -> false | Fail _ -> true) tmp with
  | Some (Fail err) -> Fail err
  | Some (Succ _) -> failwith "unreachable"
  | None ->
    match List.assoc_opt None opt_tys with
    | Some (o, place) -> Fail (SafetyErr (fst pi, (omega, snd pi), (o, place)))
    | None ->
      let tys = List.map (fun pair -> unwrap (fst pair)) opt_tys
      in let* (ellPrime, ty) = unify_many (fst pi) ell tys
      in if ellPrime = ell then Succ (ty, uniq_cons (omega, snd pi) loans)
      else Fail (LoanEnvMismatch (fst pi, ell, ellPrime))

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
               (expr : expr) : (ty * loan_env * place_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
             (expr : expr) : (ty * loan_env * place_env) tc =
    match snd expr with
    | Prim prim -> Succ (type_of prim, ell, gamma)
    | BinOp (op, e1, e2) ->
      (match binop_to_types op with
       | (Some lhs_ty, Some rhs_ty, out_ty) ->
         let* (t1, ell1, gamma1) = tc delta ell gamma e1
         in if t1 = lhs_ty then
           let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
           in if t2 = rhs_ty then
             let* (ellFinal, _) = unify (fst expr) ell2 t1 t2
             in Succ (out_ty, ellFinal, gamma2)
           else Fail (TypeMismatch (rhs_ty, t2))
         else Fail (TypeMismatch (lhs_ty, t1))
       | (None, None, out_ty) ->
         let* (t1, ell1, gamma1) = tc delta ell gamma e1
         in let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
         in let* (ellFinal, _) = unify (fst expr) ell2 t1 t2
         in Succ (out_ty, ellFinal, gamma2)
       | _ -> failwith "unreachable")
    | Move pi ->
      (match omega_safe ell gamma Unique (fst expr, pi) with
       | Succ (ty, [(Unique, pi)]) ->
         let* (ellPrime, gammaPrime) =
           match place_expr_to_place pi with
           | Some pi ->
             if noncopyable ty then
               let* (ellPrime, gammaPrime) = envs_minus sigma ell gamma pi
               in Succ (ellPrime, gammaPrime)
             else Succ (ell, gamma)
           | None -> failwith "unreachable"
         in Succ (ty, ellPrime, gammaPrime)
       | Succ (_, loans) ->
         Format.printf "%a@." pp_loans loans;
         failwith "unreachable"
       | Fail err -> Fail err)
    | Borrow (prov, omega, pi) ->
      let* (ty, loans) = omega_safe ell gamma omega (fst expr, pi)
      in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         let* (ty, loans) = omega_safe ell1 gamma1 omega (fst expr, pi)
         in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ ((_, BaseTy U32), ell2, gamma2) ->
            let* (ty, loans) = omega_safe ell2 gamma2 omega (fst expr, pi)
            in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
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
      let* (_, ell1, gamma1) = tc delta ell gamma e1
      in tc delta ell1 gamma1 e2
    | Branch (e1, e2, e3) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         let* (ty2, ell2, gamma2) = tc delta ell1 gamma1 e2
         in let* (ty3, ell3, gamma3) = tc delta ell1 gamma1 e3
         in let (ellPrime, gammaPrime) = intersect (ell2, gamma2) (ell3, gamma3)
         in let* (ellFinal, tyFinal) = unify (fst expr) ellPrime ty2 ty3
         in let* () = valid_type sigma delta ellFinal gammaPrime tyFinal
         in Succ (tyFinal, ellFinal, gammaPrime)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    | LetProv (new_provs, e) ->
      let (provs, tyvars) = delta
      in let to_loan_entry (var : prov) : prov_var * loans = (snd var, [])
      in let deltaPrime = (list_union new_provs provs, tyvars)
      in let ellPrime = loan_env_append (List.map to_loan_entry provs, ([], [])) ell
      in tc deltaPrime ellPrime gamma e
    | Let (var, ann_ty, e1, e2) ->
      let* (ty1, ell1, gamma1) = tc delta ell gamma e1
      in let* ell1Prime = subtype Combine ell1 ty1 ann_ty
      in let* gam_ext = places_typ sigma (Var var) ann_ty
      in let* (ty2, ell2, gamma2) = tc delta ell1Prime (place_env_append gam_ext gamma1) e2
      in let* (ell2Prime, gamma2Prime) = envs_minus sigma ell2 gamma2 (Var var)
      in Succ (ty2, ell2Prime, gamma2Prime)
    | Assign (pi, e) ->
      let* (ty_old, loans) = omega_safe ell gamma Unique (fst expr, pi)
      in let* (ty_update, ell1, gamma1) = tc delta ell gamma e
      in let* ellPrime = subtype Override ell1 ty_update ty_old
      in let place_opts = List.map (fun loan -> place_expr_to_place (snd loan)) loans
      in let places = List.map unwrap (List.filter (fun opt -> opt != None) place_opts)
      in let work (acc : place_env tc) (pi : place) : place_env tc =
          let* acc = acc
          in let* gam_ext = places_typ sigma pi ty_old
          in Succ (place_env_append gam_ext acc)
      in let* gammaPrime = List.fold_left work (Succ gamma1) places
      in Succ ((inferred, BaseTy Unit), ellPrime, gammaPrime)
    | Abort _ -> failwith "unimplemented abort"
    | While (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         let* (_, ell2, gamma2) =  tc delta ell1 gamma1 e2
         in tc delta ell2 gamma2 e2
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    | For (var, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, Array (elem_ty, _)), ell1, gamma1) ->
         let* gam_ext = places_typ sigma (Var var) elem_ty
         in let* (_, ell2, gamma2) = tc delta ell1 (place_env_append gam_ext gamma1) e2
         in let* (ell2Prime, gamma2Prime) = envs_minus sigma ell2 gamma2 (Var var)
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
           else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
         else Fail (PlaceEnvMismatch (fst e2, gamma1, gamma2Prime))
       | Succ ((_, Ref (prov, omega, (_, Slice elem_ty))), ell1, gamma1) ->
         let* gam_ext = places_typ sigma (Var var) (inferred, Ref (prov, omega, elem_ty))
         in let* (_, ell2, gamma2) = tc delta ell1 (place_env_append gam_ext gamma1) e2
         in let* (ell2Prime, gamma2Prime) = envs_minus sigma ell2 gamma2 (Var var)
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
           else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
         else Fail (PlaceEnvMismatch (fst e2, gamma1, gamma2Prime))
       | Succ (found, _, _) -> Fail (TypeMismatchIterable found)
       | Fail err -> Fail err)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, provs, tyvars, params, ret_ty, _) ->
         let fn_ty : ty = (inferred, Fun (provs, tyvars, List.map snd params, [], ret_ty))
         in Succ (fn_ty, ell, gamma)
       | None -> Fail (UnknownFunction (fst expr, fn)))
    | Fun (provs, tyvars, params, opt_ret_ty, body) ->
      let places_typ_u (pair : var * ty) = places_typ sigma (Var (fst pair)) (snd pair)
      in let* gam_ext =
        List.fold_right (fun x y -> let* x = x in let* y = y in Succ (list_union x y))
                        (List.map places_typ_u params) (Succ [])
      in let deltaPrime = (list_union provs (fst delta), list_union tyvars (snd delta))
      in let ellPrime = loan_env_bindall ell provs
      in let* (ret_ty, ellPrime, gammaPrime) =
           tc deltaPrime ellPrime (place_env_append gam_ext gamma) body
      in let gamma_c = place_env_diff gamma gammaPrime
      in let fn_ty (ret_ty : ty) : ty =
           (inferred, Fun (provs, tyvars, List.map snd params, gamma_c, ret_ty))
      in (match opt_ret_ty with
          | Some ann_ret_ty ->
            let* ellFinal = subtype Combine ellPrime ret_ty ann_ret_ty
            in Succ (fn_ty ann_ret_ty, ellFinal, gammaPrime)
          | None -> Succ (fn_ty ret_ty, ellPrime, gammaPrime))
    | App (fn, new_provs, new_tys, args) ->
      (match tc delta ell gamma fn with
       | Succ ((_, Fun (provs, tyvars, params, _, ret_ty)), ellF, gammaF) ->
         let* (arg_tys, ellN, gammaN) = tc_many delta ellF gammaF args
         in let (prov_sub, ty_sub) = (List.combine new_provs provs,
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
               in let* () = valid_type sigma delta ellN gammaN new_ret_ty
               in Succ (new_ret_ty, ellN, gammaN)
             | Some (expected, found) -> Fail (TypeMismatch (expected, found)))
       | Succ (found, _, _) -> Fail (TypeMismatchFunction found)
       | Fail err -> Fail err)
    | Tup exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let final_ty : ty = (inferred, Tup tys)
      in Succ (final_ty, ellPrime, gammaPrime)
    | Array exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let* (ellFinal, unified_ty) = unify_many (fst expr) ellPrime tys
      in let final_ty : ty = (inferred, Array (unified_ty, List.length tys))
      in Succ (final_ty, ellFinal, gammaPrime)
    | Struct (name, _, _) ->
      (match global_env_find_fn sigma name with
       | Some (_, provs, tyvars, params, ret_ty, _) ->
         let fn_ty : ty = (inferred, Fun (provs, tyvars, List.map snd params, [], ret_ty))
         in Succ (fn_ty, ell, gamma)
       | None -> Fail (UnknownStruct (fst expr, name)))
    | Ptr _ -> failwith "unimplemented"
  and tc_many (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
      (exprs : expr list) : (ty list * loan_env * place_env) tc =
    let work (acc : (ty list * loan_env * place_env) tc) (e : expr) =
      let* (curr_tys, curr_ell, curr_gamma) = acc
      in let* (ty, ellPrime, gammaPrime) = tc delta curr_ell curr_gamma e
      in Succ (List.cons ty curr_tys, ellPrime, gammaPrime)
    in List.fold_left work (Succ ([], ell, gamma)) exprs
  in tc delta ell gamma expr


let rec free_provs_ty (ty : ty) : provs =
  match snd ty with
  | Any | BaseTy _ | TyVar _ -> []
  | Ref (prov, _, ty) -> List.cons prov (free_provs_ty ty)
  | Fun _ -> [] (* FIXME: actually implement *)
  | Array (ty, _) | Slice ty -> free_provs_ty ty
  | Tup tys -> List.flatten (List.map free_provs_ty tys)
  | Struct (_, provs, tys) -> List.flatten (List.cons provs (List.map free_provs_ty tys))
and free_provs (expr : expr) : provs =
  match snd expr with
  | Prim _ | Move _ | Fn _ | Abort _ | Ptr _ -> []
  | BinOp (_, e1, e2) -> List.append (free_provs e1) (free_provs e2)
  | Borrow (prov, _, _) -> [prov]
  | BorrowIdx (prov, _, _, e) -> List.cons prov (free_provs e)
  | BorrowSlice (prov, _, _, e1, e2) ->
    List.cons prov (List.append (free_provs e1) (free_provs e2))
  | LetProv (provs, e) ->
    List.filter (fun prov -> not (List.mem prov provs)) (free_provs e)
  | Let (_, ty, e1, e2) ->
    List.append (free_provs_ty ty) (List.append (free_provs e1) (free_provs e2))
  | Assign (_, e) -> free_provs e
  | Seq (e1, e2) -> List.append (free_provs e1) (free_provs e2)
  | Fun _ -> [] (* FIXME: actually implement *)
  | App (e1, provs, tys, es) ->
    List.concat [free_provs e1; provs;
                 List.flatten (List.map free_provs_ty tys);
                 List.flatten (List.map free_provs es)]
  | Idx (_, e) -> free_provs e
  | Branch (e1, e2, e3) ->
    List.concat [free_provs e1; free_provs e2; free_provs e3]
  | While (e1, e2) | For (_, e1, e2) ->
    List.append (free_provs e1) (free_provs e2)
  | Tup es | Array es -> List.flatten (List.map free_provs es)
  | Struct (_, provs, _) -> provs

let wf_global_env (sigma : global_env) : unit tc =
  let valid_global_entry (acc : unit tc) (entry : global_entry) : unit tc =
    let* () = acc
    in match entry with
    | FnDef (_, provs, tyvars, params, ret_ty, body) ->
      let free_provs = (* this lets us get away without letprov *)
        List.filter (fun prov -> not (List.mem prov provs)) (free_provs body)
      in let delta = (List.append provs free_provs, tyvars)
      in let ell = (List.map (fun p -> (snd p, [])) free_provs, (List.map snd provs, []))
      in let places_include_fold (gamma : place_env tc) (pair : var * ty) : place_env tc =
        let* gamma = gamma
        in place_env_include sigma gamma (Var (fst pair)) (snd pair)
      in let* gamma = List.fold_left places_include_fold (Succ []) params
      in let* (output_ty, ellPrime, _) = type_check sigma delta ell gamma body
      in let* _ = subtype Combine ellPrime output_ty ret_ty
      in Succ ()
    | RecStructDef (name, provs, tyvars, fields) ->
      let delta = (provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let* () = valid_types sigma delta ell empty_gamma (List.map snd fields)
      in let find_dup (pair : field * ty)
                      (acc : (field * ty) list * ((field * ty) * (field * ty)) option) =
        let (acc_lst, acc_opt) = acc
        in if List.mem_assoc (fst pair) acc_lst then
          (acc_lst, Some (pair, (fst pair, List.assoc (fst pair) acc_lst)))
        else (List.cons pair acc_lst, acc_opt)
      in (match List.fold_right find_dup fields ([], None) with
          | (_, None) -> Succ ()
          | (_, Some (p1, p2)) -> Fail (DuplicateFieldsInStructDef (name, p1, p2)))
    | TupStructDef (_, provs, tyvars, tys) ->
      let delta = (provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let* () = valid_types sigma delta ell empty_gamma tys
      in Succ ()
  in List.fold_left valid_global_entry (Succ ()) (List.cons drop sigma)
