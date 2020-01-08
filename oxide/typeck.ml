open Syntax
open Edsl
open Meta
open Util

let subtype_prov (mode : subtype_modality) (ell : loan_env)
    (prov1 : prov) (prov2 : prov) : loan_env tc =
  match (mode, loan_env_lookup_opt ell prov1, loan_env_lookup_opt ell prov2) with
  | (Combine, Some rep1, Some rep2) ->
    (* UP-CombineLocalProvenances*)
    let ellPrime = loan_env_exclude ell prov2
    in Succ (loan_env_include ellPrime prov2 (list_union rep1 rep2))
  | (Override, Some rep1, Some _) ->
    (* UP-OverrideLocalProvenances *)
    let ellPrime = loan_env_exclude ell prov2
    in Succ (loan_env_include ellPrime prov2 rep1)
  | (_, None, Some _) ->
    (* UP-AbstractProvLocalProv *)
    if not (loan_env_is_abs ell prov1) then Fail (InvalidProv prov1)
    else if loan_env_abs_sub ell prov1 prov2 then Succ ell
    else Fail (InvalidProv prov1)
  | (_, Some _, None) ->
    (* UP-LocalProvAbstractProv *)
    if not (loan_env_is_abs ell prov2) then Fail (InvalidProv prov2)
    else let ellPrime = loan_env_add_abs_sub ell prov1 prov2
    in Succ ellPrime
  | (_, None, None) ->
    (* UP-AbstractProvenances *)
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
  in List.fold_left work (Succ ell) (combine "subtype_prov_many" provs1 provs2)

let subtype (mode : subtype_modality) (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env tc =
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
      let* ellPrime = subtype_prov mode ell v1 v2
      in sub ellPrime t1 t2
    (* UT-UniqueRef *)
    | (Ref (v1, Unique, t1), Ref (v2, Unique, t2)) ->
      let* ellPrime = subtype_prov mode ell v1 v2
      in let* ell1 = sub ellPrime t1 t2
      in let* ell2 = sub ellPrime t2 t1
      in if ell1 = ell2 then Succ ell1
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
        let* ell_provs = subtype_prov_many mode ell provs1 provs2
        in let* ell_tys = sub_many ell_provs tys1 tys2
        in sub_opt ell_tys tagged_ty1 tagged_ty2
      else Fail (UnificationFailed (ty1, ty2))
    (* UT-Function *)
    | (Fun (prov1, tyvar1, tys1, _, ret_ty1), Fun (prov2, tyvar2, tys2, _, ret_ty2)) ->
      let tyvar_for_sub = List.map (fun x -> (inferred, TyVar x)) tyvar1
      in let (prov_sub, ty_sub) = (combine "UT-Function: provs" prov1 prov2,
                                   combine "UT-Function: tyvars" tyvar_for_sub tyvar2)
      in let do_sub (ty : ty) : ty = (subst_many (subst_many_prov ty prov_sub) ty_sub)
      in let alpharenamed_tys2 = List.map do_sub tys2
      in let* ell_prime = sub_many ell alpharenamed_tys2 tys1
      in sub ell_prime ret_ty1 ret_ty2
    | (Any, _) -> Succ ell
    | (_, _) -> Fail (UnificationFailed (ty1, ty2))
  and sub_many (ell : loan_env) (tys1 : ty list) (tys2 : ty list) : loan_env tc =
    let work (acc : loan_env tc) (tys : ty * ty) : loan_env tc =
      let* ell = acc
      in sub ell (fst tys) (snd tys)
    in List.fold_left work (Succ ell) (combine "subtype_many: tys" tys1 tys2)
  and sub_opt (ell : loan_env) (ty1 : ty option) (ty2 : ty option) : loan_env tc =
    match (ty1, ty2) with
    | (Some ty1, Some ty2) -> sub ell ty1 ty2
    | (Some _, None) | (None, Some _) | (None, None) -> Succ ell
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

let intersect (envs1 : loan_env * var_env) (envs2 : loan_env * var_env) : loan_env * var_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in let ell = union ell1 ell2
  in let also_in_gamma2 (pair : var * ty) =
       let (x, ty) = pair
       in match List.assoc_opt x gamma2 with
       | Some ty2 -> ty == ty2 (* TODO: maybe unify, but then we're changing ell *)
       | None -> false
  in (ell, List.find_all also_in_gamma2 gamma1)

let var_env_diff (gam1 : var_env) (gam2 : var_env) : var_env =
  let not_in_gam2 (entry1 : var * ty) : bool =
    not (List.exists (fun entry2 -> fst entry2 = fst entry1) gam2)
  in List.filter not_in_gam2 gam1

let valid_prov (_ : tyvar_env) (ell : loan_env) (gamma : var_env) (prov : prov) : unit tc =
  (* FIXME: check tyvar_env_prov_mem, but then we need to add letprovs to programs in codegen *)
  if loan_env_mem ell prov then
    match loan_env_lookup_opt ell prov with
    | Some loans ->
      let invalid_loans = List.filter (fun p -> var_env_contains_place_expr gamma (snd p)) loans
      in (match invalid_loans with
      | [] -> Succ ()
      | (omega, pi) :: _ -> Fail (InvalidLoan (omega, pi)))
    | None -> Fail (InvalidProv prov)
  else if loan_env_is_abs ell prov then Succ ()
  else Fail (InvalidProv prov)

let valid_type (_ : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env) (ty : ty) : unit tc =
  let rec valid (ty : ty) : unit tc =
    match snd ty with
    | Any | BaseTy _ -> Succ ()
    | TyVar tyvar ->
      if List.mem tyvar (snd delta) then Succ ()
      else Fail (InvalidType ty)
    | Ref (prov, _, ty) ->
      let* () = valid_prov delta ell gamma prov
      in let* () = valid ty
      in let place_exprs = List.map snd (loan_env_lookup ell prov)
      in let work (pi : place_expr) (acc : unit tc) : unit tc =
        let* () = acc
        in let* ty_root = var_env_lookup gamma (fst pi, (sndfst pi, []))
        in let* ty_pi = compute_ty ty_root (sndsnd pi)
        in if snd ty_pi = snd ty then Succ ()
        else Fail (TypeMismatch (ty, ty_pi))
      in List.fold_right work place_exprs (Succ ())
    | Fun _ -> failwith "unimplemented: WF-Function"
    | Array (typ, n) -> if n >= 0 then valid typ else Fail (InvalidArrayLen (ty, n))
    | Uninit typ | Slice typ -> valid typ
    | Rec pairs -> valid_many (List.map snd pairs)
    | Tup tys -> valid_many tys
    | Struct _ -> Succ () (* TODO: use sigma *)
  and valid_many (tys : ty list) =
    let work (ty : ty) (acc : unit tc) =
      let* () = acc in valid ty
    in List.fold_right work tys (Succ ())
  in valid ty

let valid_types (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
    (tys : ty list) : unit tc =
  let valid_ty (ty : ty) (acc : unit tc) =
    let* () = acc in valid_type sigma delta ell gamma ty
  in List.fold_right valid_ty tys (Succ ())

let type_of (prim : prim) : ty =
  (inferred, match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool)

let omega_safe (sigma : global_env) (ell : loan_env) (gamma : var_env) (omega : owned)
    (pi : place_expr) : (ty * loans) tc =
  let* loans = eval_place_expr ell gamma omega pi
  in let safe_then_ty (loan : loan) : (ty option * loan) tc =
       let* res = is_safe ell gamma omega (snd loan)
       in match res with
       | None ->
         let* res_ty = var_env_lookup_place_expr gamma (snd loan)
         in Succ (Some res_ty, loan)
       | Some possible_conflicts ->
         (* the reason these are only _possible_ conflicts is essentially reborrows *)
         let is_in (loan : loan) (other_loan : loan) : bool = (snd other_loan) = (snd loan)
         in let is_real (loan : loan) : bool = not (List.exists (is_in loan) loans)
         in match List.find_opt is_real possible_conflicts with
         | Some loan -> Succ (None, loan) (* in this case, we've found a _real_ conflict *)
         | None -> (* but here, the only conflict are precisely loans being reborrowed *)
           let hd = List.hd possible_conflicts
           in if not (place_expr_is_place pi) && is_at_least omega (fst hd) then
             let* res_ty = var_env_lookup_place_expr gamma (snd hd)
             in Succ (Some res_ty, loan)
           else Succ (None, hd)
  in let tmp = List.map safe_then_ty loans
  in let opt_tys =
       List.flatten (List.map (fun tc -> match tc with Succ x -> [x] | Fail _ -> []) tmp)
  in match List.find_opt (fun tc -> match tc with Succ _ -> false | Fail _ -> true) tmp with
  | Some (Fail err) -> Fail err
  | Some (Succ _) -> failwith "unreachable"
  | None ->
    match List.assoc_opt None opt_tys with
    | Some (o, place) -> Fail (SafetyErr ((omega, pi), (o, place)))
    | None ->
      let tys = List.map (fun pair -> unwrap (fst pair)) opt_tys
      in let* (ellPrime, ty) = unify_many (fst pi) ell tys
      in let* _ =
        let* noncopy = noncopyable sigma ty
        in if noncopy then eval_place_expr ell gamma omega pi
        else Succ []
      in if ellPrime = ell then
        if (snd ty) = Any then
          let* init_ty = var_env_lookup_place_expr gamma (fst pi, (root_of pi, []))
          in let* computed_ty = compute_ty init_ty (sndsnd pi)
          in Succ (computed_ty, uniq_cons (omega, pi) loans)
        else Succ (ty, uniq_cons (omega, pi) loans)
      else Fail (LoanEnvMismatch (fst pi, ell, ellPrime))

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
               (expr : expr) : (ty * loan_env * var_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
             (expr : expr) : (ty * loan_env * var_env) tc =
    match snd expr with
    (* T-Unit, T-u32, T-True, T-False *)
    | Prim prim -> Succ (type_of prim, ell, gamma)
    (* binary operations *)
    | BinOp (op, e1, e2) ->
      (match binop_to_types op with
       | (Some lhs_ty, Some rhs_ty, out_ty) ->
         let* (t1, ell1, gamma1) = tc delta ell gamma e1
         in if (snd t1) = (snd lhs_ty) then
           let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
           in if (snd t2) = (snd rhs_ty) then
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
    (* T-Move and T-Copy *)
    | Move pi ->
      let* places = norm_place_expr ell gamma pi
      in let* tys = var_env_lookup_many gamma places
      in let* (ell_prime, unified_ty) = unify_many (fst expr) ell tys
      in let* copy = copyable sigma unified_ty
      in let omega = if copy then Shared else Unique
      in (match omega_safe sigma ell_prime gamma omega pi with
       | Succ (ty, [(Unique, pi)]) ->
         let* (ellPrime, gammaPrime) =
           match place_expr_to_place pi with
           | Some pi ->
             let* noncopy = noncopyable sigma ty
             in if noncopy then
               let* gammaPrime = var_env_type_update gamma pi (uninit ty)
               in Succ (ell, gammaPrime)
             else Succ (ell_prime, gamma)
           | None ->
             let* copy = copyable sigma ty
             in if copy then Succ (ell_prime, gamma) else failwith "unreachable"
         in Succ (ty, ellPrime, gammaPrime)
       | Succ (ty, _) ->
         if copy then Succ (ty, ell_prime, gamma)
         else failwith "unreachable"
       | Fail err -> Fail err)
    (* T-Borrow *)
    | Borrow (prov, omega, pi) ->
      let* (ty, loans) = omega_safe sigma ell gamma omega pi
      in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
    (* T-BorrowIndex *)
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         let* (ty, loans) = omega_safe sigma ell1 gamma1 omega pi
         in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    (* T-BorrowSlice *)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ ((_, BaseTy U32), ell2, gamma2) ->
            let* (ty, loans) = omega_safe sigma ell2 gamma2 omega pi
            in Succ ((inferred, Ref (prov, omega, ty)), loan_env_include ell prov loans, gamma)
          | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    (* T-IndexCopy *)
    | Idx (pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match omega_safe sigma ell1 gamma1 Shared pi with
          | Succ ((_, Array (ty, _)), _) ->
            let* copy = copyable sigma ty
            in if copy then Succ (ty, ell1, gamma1)
            else Fail (CannotMove pi)
          | Succ (found, _) -> Fail (TypeMismatchArray found)
          | Fail err -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy U32), found))
       | Fail err -> Fail err)
    (* T-Seq *)
    | Seq (e1, e2) ->
      let* (_, ell1, gamma1) = tc delta ell gamma e1
      in tc delta ell1 gamma1 e2
    (* T-Branch *)
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
    (* T-LetProv *)
    | LetProv (new_provs, e) ->
      let (provs, tyvars) = delta
      in let to_loan_entry (var : prov) : prov_var * loans = (snd var, [])
      in let deltaPrime = (list_union new_provs provs, tyvars)
      in let ellPrime = loan_env_append (List.map to_loan_entry provs, ([], [])) ell
      in tc deltaPrime ellPrime gamma e
    (* T-Let *)
    | Let (var, ann_ty, e1, e2) ->
      let* (ty1, ell1, gamma1) = tc delta ell gamma e1
      in let* ell1Prime = subtype Combine ell1 ty1 ann_ty
      in let gamma1Prime = var_env_include gamma1 var ann_ty
      in let* (ty2, ell2, gamma2) = tc delta ell1Prime gamma1Prime e2
      in let* (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (fst expr, (var, []))
      in Succ (ty2, ell2Prime, gamma2Prime)
    (* T-Assign *)
    | Assign (pi, e) -> (* FIXME: this case needs to be fixed when the typing rule is fixed *)
      let* (ty_old, loans) = omega_safe sigma ell gamma Unique pi
      in let* (ty_update, ell1, gamma1) = tc delta ell gamma e
      in let* ellPrime = subtype Override ell1 ty_update ty_old
      in let place_opts = List.map (fun loan -> place_expr_to_place (snd loan)) loans
      in let places = List.map unwrap (List.filter (fun opt -> opt != None) place_opts)
      in let work (acc : var_env tc) (_ : place) : var_env tc =
          let* acc = acc
          in let* gam_ext = failwith "fixme"
          in Succ (var_env_append gam_ext acc)
      in let* gammaPrime = List.fold_left work (Succ gamma1) places
      in Succ ((inferred, BaseTy Unit), ellPrime, gammaPrime)
    (* T-Abort *)
    | Abort _ -> Succ ((inferred, Any), ell, gamma)
    (* T-While *)
    | While (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         let* (_, ell2, gamma2) =  tc delta ell1 gamma1 e2
         in tc delta ell2 gamma2 e2
       | Succ (found, _, _) -> Fail (TypeMismatch ((dummy, BaseTy Bool), found))
       | Fail err -> Fail err)
    (* T-ForArray, T-ForSlice *)
    | For (var, e1, e2) ->
      (match tc delta ell gamma e1 with
       (* T-ForArray *)
       | Succ ((_, Array (elem_ty, _)), ell1, gamma1) ->
         let gamma1Prime = var_env_include gamma1 var elem_ty
         in let* (_, ell2, gamma2) = tc delta ell1 gamma1Prime e2
         in let* (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (fst expr, (var, []))
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
           else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
         else Fail (VarEnvMismatch (fst e2, gamma1, gamma2Prime))
       (* T-ForSlice *)
       | Succ ((_, Ref (prov, omega, (_, Slice elem_ty))), ell1, gamma1) ->
         let gamma1Prime = var_env_include gamma1 var (inferred, Ref (prov, omega, elem_ty))
         in let* (_, ell2, gamma2) = tc delta ell1 gamma1Prime e2
         in let* (ell2Prime, gamma2Prime) = envs_minus ell2 gamma2 (fst expr, (var, []))
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then Succ ((inferred, BaseTy Unit), ell1, gamma1)
           else Fail (LoanEnvMismatch (fst e2, ell1, ell2Prime))
         else Fail (VarEnvMismatch (fst e2, gamma1, gamma2Prime))
       | Succ (found, _, _) -> Fail (TypeMismatchIterable found)
       | Fail err -> Fail err)
    (* T-Function *)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, provs, tyvars, params, ret_ty, _) ->
         let fn_ty : ty = (inferred, Fun (provs, tyvars, List.map snd params, [], ret_ty))
         in Succ (fn_ty, ell, gamma)
       | None -> Fail (UnknownFunction (fst expr, fn)))
    (* T-Closure *)
    | Fun (provs, tyvars, params, opt_ret_ty, body) ->
      let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gammaPrime = List.fold_left var_include_fold [] params
      in let deltaPrime = (list_union provs (fst delta), list_union tyvars (snd delta))
      in let ellPrime = loan_env_bindall ell provs
      in let* (ret_ty, _, _) =
           tc deltaPrime ellPrime gammaPrime body
      in let* free_vars = free_nc_vars sigma gamma body
      in let gamma_c = List.map (fun var -> (var, List.assoc var gamma)) free_vars
      in let gammaPrime = var_env_uninit_many gamma free_vars
      in let fn_ty (ret_ty : ty) : ty =
           (inferred, Fun (provs, tyvars, List.map snd params, gamma_c, ret_ty))
      in (match opt_ret_ty with
          | Some ann_ret_ty ->
            let* ellFinal = subtype Combine ell ret_ty ann_ret_ty
            in Succ (fn_ty ann_ret_ty, ellFinal, gammaPrime)
          | None -> Succ (fn_ty ret_ty, ell, gammaPrime))
    (* T-App *)
    | App (fn, new_provs, new_tys, args) ->
      (match tc delta ell gamma fn with
       | Succ ((_, Fun (provs, tyvars, params, _, ret_ty)), ellF, gammaF) ->
         let* (arg_tys, ellN, gammaN) = tc_many delta ellF gammaF args
         in let (prov_sub, ty_sub) = (combine "T-App: provs" new_provs provs,
                                      combine "T-App: tys" new_tys tyvars)
         in let do_sub (ty : ty) : ty = (subst_many (subst_many_prov ty prov_sub) ty_sub)
         in let new_params = List.map do_sub params
         in let ty_pairs = combine "T-App: args" new_params arg_tys
         in let types_match (tys : ty * ty) : bool =
              let (expected, found) = tys
              in (snd expected) == (snd found)
         in (match List.find_opt types_match ty_pairs with
             | None ->
               let new_ret_ty = do_sub ret_ty
               in let* () = valid_type sigma delta ellN gammaN new_ret_ty
               in Succ (new_ret_ty, ellN, gammaN)
             | Some (expected, found) -> Fail (TypeMismatch (expected, found)))
       | Succ (found, _, _) -> Fail (TypeMismatchFunction found)
       | Fail err -> Fail err)
    (* T-Tuple *)
    | Tup exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let final_ty : ty = (inferred, Tup tys)
      in Succ (final_ty, ellPrime, gammaPrime)
    (* T-Array *)
    | Array exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let* (ellFinal, unified_ty) = unify_many (fst expr) ellPrime tys
      in let final_ty : ty = (inferred, Array (unified_ty, List.length tys))
      in Succ (final_ty, ellFinal, gammaPrime)
    (* T-RecordStruct *)
    | RecStruct (name, provs, tys, fields) ->
      (match global_env_find_struct sigma name with
       | Some (Rec (_, _, dfn_provs, tyvars, dfn_fields)) ->
         let fields_sorted = List.sort (fun x y -> compare (fst x) (fst y)) fields
         in let dfn_fields_sorted = List.sort (fun x y -> compare (fst x) (fst y)) dfn_fields
         in let exprs = List.map snd fields_sorted
         in let (prov_sub, ty_sub) = (combine "T-RecStruct: provs" provs dfn_provs,
                                      combine "T-RecStruct: tys" tys tyvars)
         in let do_sub (ty : ty) : ty = (subst_many (subst_many_prov ty prov_sub) ty_sub)
         in let expected_tys = List.map (fun x -> do_sub (snd x)) dfn_fields_sorted
         in let pairs = combine "T-RecStruct: fields" exprs expected_tys
         in let tc_exp (acc : (loan_env * var_env) tc) (p : expr * ty) =
           let* (ell, gamma) = acc
           in let (expr, expected_ty) = p
           in let* (found_ty, ell_prime, gamma_prime) = tc delta ell gamma expr
           in let* ell_final = subtype Combine ell_prime found_ty expected_ty
           in Succ (ell_final, gamma_prime)
         in let* (ell_prime, gamma_prime) = List.fold_left tc_exp (Succ (ell, gamma)) pairs
         in let tagged_ty : ty option = Some (inferred, Rec dfn_fields_sorted)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), ell_prime, gamma_prime)
       | Some (Tup _) -> Fail (WrongStructConstructor (fst expr, name, Rec))
       | None -> Fail (UnknownStruct (fst expr, name)))
    (* T-TupleStruct *)
    | TupStruct (name, provs, tys, exprs) ->
      (match global_env_find_struct sigma name with
       | Some (Tup (_, _, dfn_provs, tyvars, dfn_tys)) ->
         let (prov_sub, ty_sub) = (combine "T-TupStruct: provs" provs dfn_provs,
                                   combine "T-TupStruct: tys" tys tyvars)
         in let do_sub (ty : ty) : ty = (subst_many (subst_many_prov ty prov_sub) ty_sub)
         in let expected_tys = List.map (fun x -> do_sub x) dfn_tys
         in let pairs = combine "T-TupStruct: args" exprs expected_tys
         in let tc_exp (acc : (loan_env * var_env) tc) (p : expr * ty) =
           let* (ell, gamma) = acc
           in let (expr, expected_ty) = p
           in let* (found_ty, ell_prime, gamma_prime) = tc delta ell gamma expr
           in let* ell_final = subtype Combine ell_prime found_ty expected_ty
           in Succ (ell_final, gamma_prime)
         in let* (ell_prime, gamma_prime) = List.fold_left tc_exp (Succ (ell, gamma)) pairs
         in let tagged_ty : ty option = Some (inferred, Tup tys)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), ell_prime, gamma_prime)
       | Some (Rec _) -> Fail (WrongStructConstructor (fst expr, name, Tup))
       | None ->
         if global_env_find_struct sigma name == None then Fail (UnknownStruct (fst expr, name))
         else Fail (WrongStructConstructor (fst expr, name, Tup)))
    (* T-Pointer *)
    | Ptr _ -> failwith "unimplemented: T-Pointer"
  and tc_many (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
      (exprs : expr list) : (ty list * loan_env * var_env) tc =
    let work (e : expr) (acc : (ty list * loan_env * var_env) tc) =
      let* (curr_tys, curr_ell, curr_gamma) = acc
      in let* (ty, ellPrime, gammaPrime) = tc delta curr_ell curr_gamma e
      in Succ (List.cons ty curr_tys, ellPrime, gammaPrime)
    in List.fold_right work exprs (Succ ([], ell, gamma))
  in tc delta ell gamma expr

(* populate the tagged section of struct types based on the global environment *)
let struct_to_tagged (sigma : global_env) : global_env tc =
  let rec do_expr (expr : expr) : expr tc =
    let (loc, expr) = expr
    in match expr with
    | Prim _ | Move _ | Borrow _ | Fn _ | Abort _ | Ptr _ -> Succ (loc, expr)
    | BinOp (op, e1, e2) ->
      let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in Succ (loc, BinOp (op, e1, e2))
    | BorrowIdx (prov, omega, p, e) ->
      let* e = do_expr e
      in Succ (loc, BorrowIdx (prov, omega, p, e))
    | BorrowSlice (prov, omega, p, e1, e2) ->
      let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in Succ (loc, BorrowSlice (prov, omega, p, e1, e2))
    | LetProv (provs, e) ->
      let* e = do_expr e
      in Succ (loc, LetProv (provs, e))
    | Let (x, ty, e1, e2) ->
      let* ty = do_ty ty
      in let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in Succ (loc, Let (x, ty, e1, e2))
    | Assign (p, e) ->
      let* e = do_expr e
      in Succ (loc, Assign (p, e))
    | Seq (e1, e2) ->
      let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in Succ (loc, Seq (e1, e2))
    | Fun (provs, tyvars, params, res, body) ->
      let* params = do_params params
      in let* res = do_opt_ty res
      in let* body = do_expr body
      in let fn : preexpr = Fun (provs, tyvars, params, res, body)
      in Succ (loc, fn)
    | App (fn, provs, tys, args) ->
      let* fn = do_expr fn
      in let* tys = do_tys tys
      in let* args = do_exprs args
      in Succ (loc, App (fn, provs, tys, args))
    | Idx (p, e) ->
      let* e = do_expr e
      in Succ (loc, Idx (p, e))
    | Branch (e1, e2, e3) ->
      let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in let* e3 = do_expr e3
      in Succ (loc, Branch (e1, e2, e3))
    | While (e1, e2) ->
      let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in Succ (loc, While (e1, e2))
    | For (x, e1, e2) ->
      let* e1 = do_expr e1
      in let* e2 = do_expr e2
      in Succ (loc, For (x, e1, e2))
    | Tup exprs ->
      let* exprs = do_exprs exprs
      in let tup : preexpr = Tup exprs
      in Succ (loc, tup)
    | Array exprs ->
      let* exprs = do_exprs exprs
      in let array : preexpr = Tup exprs
      in Succ (loc, array)
    | RecStruct (sn, provs, tys, args) ->
      let* tys = do_tys tys
      in let* args = do_args args
      in Succ (loc, RecStruct (sn, provs, tys, args))
    | TupStruct (sn, provs, tys, exprs) ->
      let* tys = do_tys tys
      in let* exprs = do_exprs exprs
      in Succ (loc, TupStruct (sn, provs, tys, exprs))
  and do_ty (ty : ty) : ty tc =
    let (loc, ty) = ty
    in match ty with
    (* the interesting case: encountering a struct type *)
    | Struct (sn, provs, tys, None) ->
      let* tys = do_tys tys
      in (match global_env_find_struct sigma sn with
      | Some (Rec (_, _, _, _, fields)) ->
        let fields_sorted = List.sort (fun x y -> compare (fst x) (fst y)) fields
        in let* fields = do_params fields_sorted
        in let ty : ty = (inferred, Rec fields)
        in Succ (loc, Struct (sn, provs, tys, Some ty))
      | Some (Tup (_, _, _, _, tup_tys)) ->
        let* tup_tys = do_tys tup_tys
        in let ty : ty = (inferred, Tup tup_tys)
        in Succ (loc, Struct (sn, provs, tys, Some ty))
      | None -> Fail (UnknownStruct (loc, sn)))
    (* structural cases *)
    | Any | BaseTy _ | TyVar _ -> Succ (loc, ty)
    | Ref (prov, omega, ty) ->
      let* ty = do_ty ty
      in Succ (loc, Ref (prov, omega, ty))
    | Fun (provs, tyvars, tys, gamma, ty) ->
      (* should we transform gamma here? maybe not necessary *)
      let* tys = do_tys tys
      in let* ty = do_ty ty
      in let fn : prety = Fun (provs, tyvars, tys, gamma, ty)
      in Succ (loc, fn)
    | Array (ty, n) ->
      let* ty = do_ty ty
      in let array : prety = Array (ty, n)
      in Succ (loc, array)
    | Slice ty ->
      let* ty = do_ty ty
      in let slice : prety = Slice ty
      in Succ (loc, slice)
    | Rec fields ->
      let* fields = do_params fields
      in let record : prety = Rec fields
      in Succ (loc, record)
    | Tup tys ->
      let* tys = do_tys tys
      in let tup : prety = Tup tys
      in Succ (loc, tup)
    | Struct (sn, provs, tys, Some tagged_ty) ->
      let* tys = do_tys tys
      in let* tagged_ty = do_ty tagged_ty
      in Succ (loc, Struct (sn, provs, tys, Some tagged_ty))
    | Uninit ty ->
      let* ty = do_ty ty
      in let uninit : prety = Uninit ty
      in Succ (loc, uninit)
  and do_exprs (exprs : expr list) : expr list tc =
    let do_lifted (expr : expr) (acc : expr list tc) : expr list tc =
      let* so_far = acc
      in let* expr = do_expr expr
      in Succ (List.cons expr so_far)
    in List.fold_right do_lifted exprs (Succ [])
  and do_args (args : (field * expr) list) : (field * expr) list tc =
    let do_lifted (arg : field * expr) (acc : (field * expr) list tc) : (field * expr) list tc =
      let* so_far = acc
      in let* expr = do_expr (snd arg)
      in Succ (List.cons (fst arg, expr) so_far)
    in List.fold_right do_lifted args (Succ [])
  and do_tys (tys : ty list) : ty list tc =
    let do_lifted (ty : ty) (acc : ty list tc) : ty list tc =
      let* so_far = acc
      in let* ty = do_ty ty
      in Succ (List.cons ty so_far)
    in List.fold_right do_lifted tys (Succ [])
  and do_opt_ty (ty : ty option) : ty option tc =
    match ty with
    | Some ty -> let* ty = do_ty ty in Succ (Some ty)
    | None -> Succ None
  and do_params (params : (var * ty) list) : (var * ty) list tc =
    let do_lifted (param : var * ty) (acc : (var * ty) list tc) : (var * ty) list tc =
      let* so_far = acc
      in let* ty = do_ty (snd param)
      in Succ (List.cons (fst param, ty) so_far)
    in List.fold_right do_lifted params (Succ [])
  and do_global_entry (entry : global_entry) : global_entry tc =
    match entry with
    | FnDef (fn, provs, tyvars, params, ret_ty, body) ->
      let* params = do_params params
      in let* ret_ty = do_ty ret_ty
      in let* body = do_expr body
      in Succ (FnDef (fn, provs, tyvars, params, ret_ty, body))
    | RecStructDef (copyable, sn, provs, tyvars, fields) ->
      let* fields = do_params fields
      in Succ (RecStructDef (copyable, sn, provs, tyvars, fields))
    | TupStructDef (copyable, sn, provs, tyvars, tys) ->
      let* tys = do_tys tys
      in Succ (TupStructDef (copyable, sn, provs, tyvars, tys))
  and do_global_entries (entries : global_entry list) : global_entry list tc =
    let do_lifted (entry : global_entry) (acc : global_entry list tc) : global_entry list tc =
      let* so_far = acc
      in let* entry = do_global_entry entry
      in Succ (List.cons entry so_far)
    in List.fold_right do_lifted entries (Succ [])
  in do_global_entries sigma

let wf_global_env (sigma : global_env) : unit tc =
  let* sigma = struct_to_tagged (List.cons drop sigma)
  in let valid_global_entry (acc : unit tc) (entry : global_entry) : unit tc =
    let* () = acc
    in match entry with
    (* WF-FunctionDef*)
    | FnDef (_, provs, tyvars, params, ret_ty, body) ->
      let free_provs = (* this lets us get away without letprov *)
        List.filter (fun prov -> not (List.mem prov provs)) (free_provs body)
      in let delta = (List.append provs free_provs, tyvars)
      in let ell = (List.map (fun p -> (snd p, [])) free_provs, (List.map snd provs, []))
      in let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gamma = List.fold_left var_include_fold [] params
      in let* (output_ty, ellPrime, _) = type_check sigma delta ell gamma body
      in let* _ = subtype Combine ellPrime output_ty ret_ty
      in Succ ()
    (* T-RecordStructDef *)
    | RecStructDef (_, name, provs, tyvars, fields) ->
      let delta = (provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let* () = valid_copy_impl sigma (unwrap (global_env_find_struct sigma name))
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
    (* T-TupleStructDef *)
    | TupStructDef (_, name, provs, tyvars, tys) ->
      let delta = (provs, tyvars)
      in let ell = ([], (List.map snd provs, []))
      in let* () = valid_copy_impl sigma (unwrap (global_env_find_struct sigma name))
      in let* () = valid_types sigma delta ell empty_gamma tys
      in Succ ()
  in List.fold_left valid_global_entry (Succ ()) (List.cons drop sigma)
