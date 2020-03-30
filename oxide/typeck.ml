open Borrowck
open Edsl
open Meta
open Syntax
open Util

(* provenance validity judgment *)
let valid_prov (delta : tyvar_env) (ell : loan_env) (gamma : var_env) (prov : prov) : unit tc =
  match loan_env_lookup_opt ell prov with
  | None ->
    if tyvar_env_prov_mem delta prov then Succ ()
    else InvalidProv prov |> fail
  | Some loans ->
    let invalid_loans = List.filter (not >> var_env_contains_place_expr gamma >> snd) loans
    in match invalid_loans with
    | [] -> Succ ()
    | (omega, pi) :: _ -> InvalidLoan (omega, pi) |> fail

(* type validity judgment *)
let rec valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                   (ty : ty) : unit tc =
  let rec valid (ty : ty) : unit tc =
    match snd ty with
    | Any | Infer | BaseTy _ -> Succ ()
    | TyVar tyvar ->
      if tyvar_env_ty_mem delta tyvar then Succ ()
      else InvalidType ty |> fail
    | Ref (prov, _, ty) ->
      let* () = valid_prov delta ell gamma prov
      in let* () = valid ty
      in let place_exprs =
        loan_env_lookup_opt ell prov |> Option.to_list |> List.flatten |> List.map snd
      in let check_ty (pi : place_expr) : unit tc =
        let* ty_pi = compute_ty delta ell gamma pi
        in if ty_in ty_pi ty || ty_in ty ty_pi then Succ ()
        else UnrelatedTypes (ty_pi, ty) |> fail
      in for_each_rev check_ty place_exprs
    | Fun (evs, provs, tyvars, param_tys, gamma_c, ret_ty, bounds) ->
      let* () = valid_env gamma_c
      in let new_delta =
        delta |> tyvar_env_add_env_vars evs
              |> tyvar_env_add_provs provs
              |> tyvar_env_add_ty_vars tyvars
              |> tyvar_env_add_bounds (bounds |> List.map (fun (l, r) -> (snd l, snd r)))
      in let* () = for_each param_tys $ valid_type sigma new_delta ell gamma
      in valid_type sigma new_delta ell gamma ret_ty
    | Array (typ, n) ->
      if n >= 0 then valid typ
      else InvalidArrayLen (ty, n) |> fail
    (* every uninit type is valid since an uninit type can only be used by assigning to the binding
       at the inner type, and if that type is not valid, no expression exists at the inner type *)
    | Uninit _ -> Succ ()
    | Slice typ -> valid typ
    | Rec pairs -> valid_many $ List.map snd pairs
    | Tup tys -> valid_many tys
    | Struct _ -> Succ () (* TODO: use sigma *)
  and valid_many (tys : ty list) : unit tc = for_each_rev valid tys
  and valid_env (gamma : env) : unit tc =
    match gamma with
    | Unboxed -> Succ ()
    | EnvVar ev ->
      if tyvar_env_env_var_mem delta ev then Succ ()
      else InvalidEnvVar (ev, ty) |> fail
    | Env gamma -> for_each_rev (fun (_, ty) -> valid ty) gamma
    | EnvOf var -> UnevaluatedEnvOf var |> fail
  in valid ty
and valid_types (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
    (tys : ty list) : unit tc =
  for_each_rev (valid_type sigma delta ell gamma) tys
(* loan environment validity judgment *)
and valid_loan_env (gamma : var_env) (ell : loan_env) : unit tc =
  let missing_phis = ell |> places_of |> List.find_all (not >> var_env_contains_place_expr gamma)
  in if is_empty missing_phis then Succ ()
  else let (prov, _) = ell |> List.find (List.exists ((=) (List.hd missing_phis) >> snd) >> snd)
  in UnboundLoanInProv (List.hd missing_phis, prov) |> fail
(* variable environment validity judgment *)
and valid_var_env (sigma : global_env) (delta : tyvar_env) (ell : loan_env)
    (gamma : var_env) : unit tc =
  gamma |> List.map snd |> valid_types sigma delta ell gamma
(* environment validity judgment, assuming global environment is well-formed *)
and valid_envs (sigma : global_env) (delta : tyvar_env)
               (ell : loan_env) (gamma : var_env) : unit tc =
  (* note: delta is well-formed by construction since it splits type variables by kind *)
  let* () = valid_loan_env gamma ell
  in valid_var_env sigma delta ell gamma

(* shadow valid_type with a version that checks valid_envs first *)
let valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
               (ty : ty) : unit tc =
  (* checking valid_envs corresponds to the side condition on the type validity judgment *)
  let* () = valid_envs sigma delta ell gamma
  in valid_type sigma delta ell gamma ty

(* checks type validity in before and after environments for better error reporting *)
let ty_valid_before_after (sigma : global_env) (delta : tyvar_env) (ty : ty)
                          (ell_before : loan_env) (gamma_before : var_env)
                          (ell_after : loan_env) (gamma_after : var_env) : unit tc =
  match (valid_type sigma delta ell_before gamma_before ty,
         valid_type sigma delta ell_after gamma_after ty) with
  | (Succ (), Succ ()) -> Succ ()
  | (Succ (), Fail (InvalidProv prov as err)) ->
    (match loan_env_lookup_opt ell_before prov with
    | Some loans ->
      let missing = List.find_all (not >> var_env_contains_place_expr gamma_after >> snd) loans
      in if is_empty missing then Succ ()
      else UnboundLoanInProv (missing |> List.hd |> snd, prov) |> fail
    | None -> Fail err)
  | (Succ (), Fail err) -> Fail err
  | (Fail err, _) -> Fail err

(* flows closed environments forward in otherwise structurally the same types *)
let flow_closed_envs_forward (computed : ty) (annotated : ty) : ty tc =
  let rec flow (computed : ty) (annotated : ty) : ty tc =
    match (snd computed, snd annotated) with
    | (Any, Any)
    | (BaseTy _, BaseTy _)
    | (TyVar _, TyVar _) -> Succ annotated
    | (Ref (_, _, computed_inner), Ref (prov, omega, annotated_inner)) ->
      let* forward = flow computed_inner annotated_inner
      in Succ (fst annotated, Ref (prov, omega, forward))
    | (Fun (_, _, _, comp_tys, gamma_c, comp_ret, _),
       Fun (evs, provs, tyvars, ann_tys, _, ann_ret, bounds)) ->
      let* forward_tys = flow_many comp_tys ann_tys
      in let* forward_ret = flow comp_ret ann_ret
      in let fn_ty : prety = Fun (evs, provs, tyvars, forward_tys, gamma_c, forward_ret, bounds)
      in Succ (fst annotated, fn_ty)
    | (Array (computed_inner, _), Array (annotated_inner, len)) ->
      let* forward = flow computed_inner annotated_inner
      in let ty : prety = Array (forward, len)
      in Succ (fst annotated, ty)
    | (Slice computed_inner, Slice annotated_inner) ->
      let* forward = flow computed_inner annotated_inner
      in Succ (fst annotated, Slice forward)
    | (Rec comp_fields, Rec ann_fields) ->
      let flow_assoc (field, ann_ty) =
        let* forward = flow (List.assoc field comp_fields) ann_ty
        in Succ (field, forward)
      in let* forward_fields = map flow_assoc ann_fields
      in let ty : prety = Rec forward_fields
      in Succ (fst annotated, ty)
    | (Tup comp_tys, Tup ann_tys) ->
      let* forward_tys = flow_many comp_tys ann_tys
      in let ty : prety = Tup forward_tys
      in Succ (fst annotated, ty)
    | (Struct (_, _, comp_tys, comp_opt), Struct (name, provs, ann_tys, ann_opt)) ->
      let* forward_tys = flow_many comp_tys ann_tys
      in let* forward = flow (Option.get comp_opt) (Option.get ann_opt)
      in let ty : prety = Struct (name, provs, forward_tys, Some forward)
      in Succ (fst annotated, ty)
    | (Uninit computed_inner, Uninit annotated_inner) ->
      let* forward = flow computed_inner annotated_inner
      in Succ (fst annotated, Uninit forward)
    | _ -> TypeMismatch (annotated, computed) |> fail
  and flow_many (computed : ty list) (annotated : ty list) : ty list tc =
    let* combined_tys = combine_tys "flow_closed_envs_forward" computed annotated
    in map (fun (comp, ann) -> flow comp ann) combined_tys
  in flow computed annotated

(* evaluates EnfOf annotations away *)
let rec eval_env_of (gamma : var_env) (env : env) : env tc =
  match env with
  | Unboxed | EnvVar _ | Env _ -> Succ env
  | EnvOf var ->
    let* env = env_of var gamma
    in eval_env_of gamma env

(* type checking for primitives *)
let type_of (prim : prim) : ty =
  (inferred, match prim with
  | Unit -> BaseTy Unit
  | Num _ -> BaseTy U32
  | True | False -> BaseTy Bool)

(* full type-checking *)
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
         in if ty_eq t1 lhs_ty then
           let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
           in if ty_eq t2 rhs_ty then
             let* (ellFinal, _) = unify (fst expr) delta ell2 t1 t2
             in Succ (out_ty, ellFinal, gamma2)
           else TypeMismatch (rhs_ty, t2) |> fail
         else TypeMismatch (lhs_ty, t1) |> fail
       | (None, None, out_ty) ->
         let* (t1, ell1, gamma1) = tc delta ell gamma e1
         in let* (t2, ell2, gamma2) = tc delta ell1 gamma1 e2
         in let* (ellFinal, _) = unify (fst expr) delta ell2 t1 t2
         in Succ (out_ty, ellFinal, gamma2)
       | _ -> failwith "T-BinOp: unreachable")
    (* T-Move and T-Copy *)
    | Move phi ->
      let* computed_ty = compute_ty delta ell gamma phi
      in let* copy = copyable sigma computed_ty
      in let omega = if copy then Shared else Unique
      in (match ownership_safe sigma delta ell gamma omega phi with
       | Succ (ty, [(Unique, pi)]) ->
         let* (ellPrime, gammaPrime) =
           match place_expr_to_place pi with
           | Some pi ->
             let* noncopy = noncopyable sigma ty
             in if is_init ty then
               if noncopy then
                 let* gammaPrime = var_env_type_update gamma pi $ uninit ty
                 in Succ (ell, gammaPrime)
               else Succ (ell, gamma)
             else PartiallyMoved (pi, ty) |> fail
           | None ->
             let* copy = copyable sigma ty
             in if copy then Succ (ell, gamma)
             else failwith "T-Move: unreachable"
         in Succ (ty, ellPrime, gammaPrime)
       | Succ (ty, _) ->
         if copy then Succ (ty, ell, gamma)
         else failwith "T-Copy: unreachable"
       | Fail err -> Fail err)
    (* T-Drop made explicit to eliminate non-determinism *)
    | Drop phi ->
      (match place_expr_to_place phi with
       | Some pi ->
         let* ty = var_env_lookup gamma pi
         in if is_init ty then
           let* gammaPrime = var_env_type_update gamma pi $ uninit ty
           in let ellPrime = kill_loans_for phi ell
           in Succ ((inferred, BaseTy Unit), ellPrime, gammaPrime)
         else PartiallyMoved (pi, ty) |> fail
       | None -> CannotMove phi |> fail)
    (* T-Borrow *)
    | Borrow (prov, omega, pi) ->
      let* (ty, loans) = ownership_safe sigma delta ell gamma omega pi
      in if tyvar_env_prov_mem delta prov then
        let* passed = passed_provs delta ell gamma pi
        in let* _ = foldl (fun ell -> outlives delta ell gamma prov) ell passed
        in Succ ((inferred, Ref (prov, omega, ty)), ell, gamma)
      else Succ ((inferred, Ref (prov, omega, ty)), loan_env_include prov loans ell, gamma)
    (* T-BorrowIndex *)
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         let* (ty, loans) = ownership_safe sigma delta ell1 gamma1 omega pi
         in if tyvar_env_prov_mem delta prov then
           let* passed = passed_provs delta ell1 gamma1 pi
           in let* _ = foldl (fun _ -> outlives delta ell1 gamma1 prov) ell1 passed
           in Succ ((inferred, Ref (prov, omega, ty)), ell1, gamma1)
         else Succ ((inferred, Ref (prov, omega, ty)), loan_env_include prov loans ell1, gamma1)
       | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
       | Fail err -> Fail err)
    (* T-BorrowSlice *)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match tc delta ell1 gamma1 e2 with
          | Succ ((_, BaseTy U32), ell2, gamma2) ->
            let* (ty, loans) = ownership_safe sigma delta ell2 gamma2 omega pi
            in if tyvar_env_prov_mem delta prov then
              let* passed = passed_provs delta ell gamma pi
              in let* _ = foldl (fun _ -> outlives delta ell2 gamma2 prov) ell2 passed
              in Succ ((inferred, Ref (prov, omega, ty)), ell2, gamma2)
            else Succ ((inferred, Ref (prov, omega, ty)), loan_env_include prov loans ell2, gamma2)
          | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
          | Fail err -> Fail err)
       | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
       | Fail err -> Fail err)
    (* T-IndexCopy *)
    | Idx (pi, e) ->
      (match tc delta ell gamma e with
       | Succ ((_, BaseTy U32), ell1, gamma1) ->
         (match ownership_safe sigma delta ell1 gamma1 Shared pi with
          | Succ ((_, Array (ty, _)), _) ->
            let* copy = copyable sigma ty
            in if copy then (ty, ell1, gamma1) |> succ
            else CannotMove pi |> fail
          | Succ (found, _) -> TypeMismatchArray found |> fail
          | Fail err -> Fail err)
       | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
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
         in let* (ellFinal, tyFinal) = unify (fst expr) delta ellPrime ty2 ty3
         in let* () = valid_type sigma delta ellFinal gammaPrime tyFinal
         in Succ (tyFinal, ellFinal, gammaPrime)
       | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy Bool), found) |> fail
       | Fail err -> Fail err)
    (* T-LetProv *)
    | LetProv (new_provs, e) ->
      let to_loan_entry (var : prov) : prov * loans = (var, [])
      in let deltaPrime = tyvar_env_add_provs new_provs delta
      in let ellPrime = provs_of delta |> List.map to_loan_entry |> flip loan_env_append $ ell
      in let* (ty_out, ell_out, gamma_out) = tc deltaPrime ellPrime gamma e
      in Succ (ty_out, loan_env_exclude_all new_provs ell_out, gamma_out)
    (* T-LetInfer *)
    | Let (var, (_, Infer), e1, e2) ->
      let* (ty1, ell1, gamma1) = tc delta ell gamma e1
      in let* () = valid_type sigma delta ell1 gamma ty1
      in let gamma1Prime = var_env_include gamma1 var ty1
      in let* (ty2, ell2, gamma2) = tc delta ell1 gamma1Prime e2
      in let keep_provs = free_provs_ty ty2
      in let* (ell2Prime, gamma2Prime) = envs_minus keep_provs ell2 gamma2 (fst expr, (var, []))
      in let* () = ty_valid_before_after sigma delta ty2 ell2 gamma2 ell2Prime gamma2Prime
      in Succ (ty2, ell2Prime, gamma2Prime)
    (* T-Let *)
    | Let (var, ann_ty, e1, e2) ->
      let* (ty1, ell1, gamma1) = tc delta ell gamma e1
      in let* () = valid_type sigma delta ell1 gamma ty1
      in let* ell1Prime = subtype Combine delta ell1 ty1 ann_ty
      in let* ann_ty = flow_closed_envs_forward ty1 ann_ty
      in let gamma1Prime = var_env_include gamma1 var ann_ty
      in let* (ty2, ell2, gamma2) = tc delta ell1Prime gamma1Prime e2
      in let keep_provs = free_provs_ty ty2
      in let* (ell2Prime, gamma2Prime) = envs_minus keep_provs ell2 gamma2 (fst expr, (var, []))
      in let* () = ty_valid_before_after sigma delta ty2 ell2 gamma2 ell2Prime gamma2Prime
      in Succ (ty2, ell2Prime, gamma2Prime)
    (* T-Assign and T-AssignDeref *)
    | Assign (phi, e) ->
      let ell = kill_loans_for phi ell
      in let* (ty_old, _) = ownership_safe sigma delta ell gamma Unique phi
      in let* (ty_update, ell1, gamma1) = tc delta ell gamma e
      in let* ellPrime = subtype Override delta ell1 ty_update ty_old
      in (match place_expr_to_place phi with
       (* T-Assign *)
       | Some pi ->
         let* gammaPrime = var_env_type_update gamma1 pi ty_update
         in Succ ((inferred, BaseTy Unit), ellPrime, gammaPrime)
       (* T-AssignDeref *)
       | None -> Succ ((inferred, BaseTy Unit), ellPrime, gamma1))
    (* T-Abort *)
    | Abort _ -> Succ ((inferred, Any), ell, gamma)
    (* T-While *)
    | While (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ ((_, BaseTy Bool), ell1, gamma1) ->
         let* (_, ell2, gamma2) =  tc delta ell1 gamma1 e2
         in tc delta ell2 gamma2 e2
       | Succ (found, _, _) -> TypeMismatch ((dummy, BaseTy Bool), found) |> fail
       | Fail err -> Fail err)
    (* T-ForArray, T-ForSlice *)
    | For (var, e1, e2) ->
      (match tc delta ell gamma e1 with
       (* T-ForArray *)
       | Succ ((_, Array (elem_ty, _)), ell1, gamma1) ->
         let gamma1Prime = var_env_include gamma1 var elem_ty
         in let* (_, ell2, gamma2) = tc delta ell1 gamma1Prime e2
         in let* (ell2Prime, gamma2Prime) = envs_minus [] ell2 gamma2 (fst expr, (var, []))
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then ((inferred, BaseTy Unit), ell1, gamma1) |> succ
           else LoanEnvMismatch (fst e2, ell1, ell2Prime) |> fail
         else VarEnvMismatch (fst e2, gamma1, gamma2Prime) |> fail
       (* T-ForSlice *)
       | Succ ((_, Ref (prov, omega, (_, Slice elem_ty))), ell1, gamma1) ->
         let gamma1Prime = var_env_include gamma1 var (inferred, Ref (prov, omega, elem_ty))
         in let* (_, ell2, gamma2) = tc delta ell1 gamma1Prime e2
         in let* (ell2Prime, gamma2Prime) = envs_minus [] ell2 gamma2 (fst expr, (var, []))
         in if gamma2Prime = gamma1 then
           if ell2Prime = ell1 then ((inferred, BaseTy Unit), ell1, gamma1) |> succ
           else LoanEnvMismatch (fst e2, ell1, ell2Prime) |> fail
         else VarEnvMismatch (fst e2, gamma1, gamma2Prime) |> fail
       | Succ (found, _, _) -> TypeMismatchIterable found |> fail
       | Fail err -> Fail err)
    (* T-Function *)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, evs, provs, tyvars, params, ret_ty, bounds, _) ->
         let fn_ty : ty =
           (inferred, Fun (evs, provs, tyvars, List.map snd params, Env [], ret_ty, bounds))
         in Succ (fn_ty, ell, gamma)
       | None ->
         (match List.assoc_opt fn gamma with
          (* T-Move for a closure *)
          | Some (_, Fun _) ->
            (match ownership_safe sigma delta ell gamma Unique (fst expr, (fn, [])) with
            | Succ (ty, [(Unique, _)]) ->
              let* closure_copyable = copyable sigma ty
              in if closure_copyable then Succ (ty, ell, gamma)
              else let* gammaPrime = uninit ty |> var_env_type_update gamma (fst expr, (fn, []))
              in Succ (ty, ell, gammaPrime)
            | Succ _ -> failwith "T-Move as T-Function: unreachable"
            | Fail err -> Fail err)
          | Some ((_, Uninit (_, Fun _)) as uninit_fn_ty) ->
            MovedFunction (expr, uninit_fn_ty) |> fail
          | (Some (_, Ref (_, omega, ((_, Fun _))))) ->
            (match ownership_safe sigma delta ell gamma omega (fst expr, (fn, [Deref])) with
            | Succ (ty, _) -> Succ (ty, ell, gamma)
            | Fail err -> Fail err)
          | Some ty -> TypeMismatchFunction ty |> fail
          | None -> UnknownFunction (fst expr, fn) |> fail))
    (* T-Closure *)
    | Fun (provs, tyvars, params, opt_ret_ty, body) ->
      let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gammaPrime = List.fold_left var_include_fold gamma params
      in let deltaPrime = delta |> tyvar_env_add_provs provs |> tyvar_env_add_ty_vars tyvars
      in let* (ret_ty, ell_body, _) = tc deltaPrime ell gammaPrime body
      in let* free_vars =
        List.filter (fun var -> not $ List.mem_assoc var params) <$> free_vars body
      in let* moved_vars = free_nc_vars sigma gamma body
      in let gamma_c = List.map (fun var -> (var, List.assoc var gamma)) free_vars
      in let* () = find_refs_to_captured deltaPrime ell_body ret_ty gamma_c
      in let gammaPrime = var_env_uninit_many gamma moved_vars
      in let fn_ty (ret_ty : ty) : ty =
           (inferred, Fun ([], provs, tyvars, List.map snd params, Env gamma_c, ret_ty, []))
      in (match opt_ret_ty with
          | Some ann_ret_ty ->
            let* ellPrime = subtype Combine deltaPrime ell_body ret_ty ann_ret_ty
            in Succ (fn_ty ann_ret_ty, ellPrime, gammaPrime)
          | None -> Succ (fn_ty ret_ty, ell_body, gammaPrime))
    (* T-App *)
    | App (fn, envs, new_provs, new_tys, args) ->
      (match tc delta ell gamma fn with
       | Succ ((_, Fun (evs, provs, tyvars, params, _, ret_ty, bounds)), ellF, gammaF) ->
         let* (arg_tys, ellN, gammaN) = tc_many delta ellF gammaF args
         in let* evaled_envs = map (eval_env_of gammaF) envs
         in let* env_sub = combine_evs "T-App" evaled_envs evs
         in let* () = check_qualifiers sigma env_sub
         in let* prov_sub = combine_prov "T-App" new_provs provs
         in let* ty_sub = combine_ty "T-App" new_tys tyvars
         in let do_sub : ty -> ty =
           subst_many ty_sub >> subst_many_prov prov_sub >> subst_many_env_var env_sub
         in let new_params = List.map do_sub params
         in let* ty_pairs = combine_tys "T-App" new_params arg_tys
         in let instantiated_bounds = subst_many_prov_in_bounds prov_sub bounds
         in let* ellPrime = check_bounds delta ellN gammaN instantiated_bounds
         in let types_mismatch ((expected, found) : ty * ty) : bool tc =
           match subtype Combine delta ellPrime found expected with
           | Succ _ -> Succ false
           | Fail (UnificationFailed _) -> Succ true
           | Fail err -> Fail err
         in let* type_mismatches = find types_mismatch ty_pairs
         in (match type_mismatches with
             | None ->
               let new_ret_ty = do_sub ret_ty
               in let* () = valid_type sigma delta ellPrime gammaN new_ret_ty
               in Succ (new_ret_ty, ellPrime, gammaN)
             | Some (expected, found) -> TypeMismatch (expected, found) |> fail)
       | Succ ((_, Uninit (_, Fun _) as uninit_ty), _, _) -> MovedFunction (fn, uninit_ty) |> fail
       | Succ (found, _, _) -> TypeMismatchFunction found |> fail
       | Fail err -> Fail err)
    (* T-Tuple *)
    | Tup exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let final_ty : ty = (inferred, Tup tys)
      in Succ (final_ty, ellPrime, gammaPrime)
    (* T-Array *)
    | Array exprs ->
      let* (tys, ellPrime, gammaPrime) = tc_many delta ell gamma exprs
      in let* (ellFinal, unified_ty) = unify_many (fst expr) delta ellPrime tys
      in let final_ty : ty = (inferred, Array (unified_ty, List.length tys))
      in Succ (final_ty, ellFinal, gammaPrime)
    (* T-RecordStruct *)
    | RecStruct (name, provs, tys, fields) ->
      (match global_env_find_struct sigma name with
       | Some (Rec (_, _, dfn_provs, tyvars, dfn_fields)) ->
         let fields_sorted = List.sort compare_keys fields
         in let dfn_fields_sorted = List.sort compare_keys dfn_fields
         in let exprs = List.map snd fields_sorted
         in let* prov_sub = combine_prov "T-RecStruct" provs dfn_provs
         in let* ty_sub = combine_ty "T-RecStruct" tys tyvars
         in let do_sub : ty -> ty = subst_many ty_sub >> subst_many_prov prov_sub
         in let expected_fields = List.map (fun (f, ty) -> (f, do_sub ty)) dfn_fields_sorted
         in let expected_tys = List.map snd expected_fields
         in let* pairs = combine_expr "T-RecStruct" exprs expected_tys
         in let tc_exp ((ell, gamma) : loan_env * var_env) (p : expr * ty) =
           let (expr, expected_ty) = p
           in let* (found_ty, ell_prime, gamma_prime) = tc delta ell gamma expr
           in let* ell_final = subtype Combine delta ell_prime found_ty expected_ty
           in Succ (ell_final, gamma_prime)
         in let* (ell_prime, gamma_prime) = foldl tc_exp (ell, gamma) pairs
         in let tagged_ty : ty option = Some (inferred, Rec expected_fields)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), ell_prime, gamma_prime)
       | Some (Tup _) -> WrongStructConstructor (fst expr, name, Rec) |> fail
       | None -> UnknownStruct (fst expr, name) |> fail)
    (* T-TupleStruct *)
    | TupStruct (name, provs, tys, exprs) ->
      (match global_env_find_struct sigma name with
       | Some (Tup (_, _, dfn_provs, tyvars, dfn_tys)) ->
         let* prov_sub = combine_prov "T-TupStruct" provs dfn_provs
         in let* ty_sub = combine_ty "T-TupStruct" tys tyvars
         in let do_sub : ty -> ty = subst_many ty_sub >> subst_many_prov prov_sub
         in let expected_tys = List.map do_sub dfn_tys
         in let* pairs = combine_expr "T-TupStruct" exprs expected_tys
         in let tc_exp ((ell, gamma) : (loan_env * var_env)) (p : expr * ty) =
           let (expr, expected_ty) = p
           in let* (found_ty, ell_prime, gamma_prime) = tc delta ell gamma expr
           in let* ell_final = subtype Combine delta ell_prime found_ty expected_ty
           in Succ (ell_final, gamma_prime)
         in let* (ell_prime, gamma_prime) = foldl tc_exp (ell, gamma) pairs
         in let tagged_ty : ty option = Some (inferred, Tup expected_tys)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), ell_prime, gamma_prime)
       | Some (Rec _) -> WrongStructConstructor (fst expr, name, Tup) |> fail
       | None ->
         if global_env_find_struct sigma name == None then UnknownStruct (fst expr, name) |> fail
         else WrongStructConstructor (fst expr, name, Tup) |> fail)
    (* T-Pointer *)
    | Ptr _ -> failwith "unimplemented: T-Pointer"
  and tc_many (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
      (exprs : expr list) : (ty list * loan_env * var_env) tc =
    let tc_next (e : expr) ((curr_tys, curr_ell, curr_gamma) : ty list * loan_env * var_env) =
      let* (ty, ellPrime, gammaPrime) = tc delta curr_ell curr_gamma e
      in Succ (List.cons ty curr_tys, ellPrime, gammaPrime)
    in foldr tc_next exprs ([], ell, gamma)
  in tc delta ell gamma expr

(* global environment validity judgment *)
let wf_global_env (sigma : global_env) : unit tc =
  let* sigma = List.cons drop sigma |> struct_to_tagged
     (* global entry validity judgment *)
  in let valid_global_entry (entry : global_entry) : unit tc =
    match entry with
    (* WF-FunctionDef*)
    | FnDef (_, evs, provs, tyvars, params, ret_ty, bounds, body) ->
      let not_in_provs (prov : prov) : bool =
        provs |> List.map snd |> List.mem (snd prov) |> not
      in let free_provs = (* this lets us infer letprovs for unbound provenances *)
         free_provs body |> List.filter not_in_provs
      in let delta = empty_delta |> tyvar_env_add_env_vars evs
                                 |> tyvar_env_add_provs provs
                                 |> tyvar_env_add_ty_vars tyvars
      in let* delta = foldl (fun delta (prov1, prov2) -> tyvar_env_add_abs_sub delta prov1 prov2)
                            delta bounds
      in let ell = free_provs |> List.map (fun p -> (p, []))
      in let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gamma = List.fold_left var_include_fold [] params
      in let* (output_ty, ellPrime, gammaPrime) = type_check sigma delta ell gamma body
      in (match valid_type sigma delta ellPrime gammaPrime output_ty with
      | Succ () ->
        (* find_refs_to_params corresponds to return type validity: WF-ReturnRef *)
        let* () = find_refs_to_params delta ellPrime output_ty params
        in let* _ = subtype Combine delta ellPrime output_ty ret_ty
        in Succ ()
      (* this is caused by a provenance being killed by its loans dropping out of scope *)
      (* in other words: references to temporaries cause an InvalidReturnType *)
      | Fail (InvalidProv prov) -> InvalidReturnType (output_ty, prov) |> fail
      | Fail err -> Fail err)
    (* T-RecordStructDef *)
    | RecStructDef (_, name, provs, tyvars, fields) ->
      let delta = empty_delta |> tyvar_env_add_provs provs |> tyvar_env_add_ty_vars tyvars
      in let* () = name |> global_env_find_struct sigma |> Option.get |> valid_copy_impl sigma
      in let* () = List.map snd fields |> valid_types sigma delta empty_ell empty_gamma
      in let find_dup (pair : field * ty)
                      (acc : (field * ty) list * ((field * ty) * (field * ty)) option) =
        let (acc_lst, acc_opt) = acc
        in if List.mem_assoc (fst pair) acc_lst then
          (acc_lst, Some (pair, (fst pair, List.assoc (fst pair) acc_lst)))
        else (List.cons pair acc_lst, acc_opt)
      in (match List.fold_right find_dup fields ([], None) with
          | (_, None) -> Succ ()
          | (_, Some (p1, p2)) -> DuplicateFieldsInStructDef (name, p1, p2) |> fail)
    (* T-TupleStructDef *)
    | TupStructDef (_, name, provs, tyvars, tys) ->
      let delta = empty_delta |> tyvar_env_add_provs provs |> tyvar_env_add_ty_vars tyvars
      in let* () = name |> global_env_find_struct sigma |> Option.get |> valid_copy_impl sigma
      in let* () = valid_types sigma delta empty_ell empty_gamma tys
      in Succ ()
  in for_each sigma valid_global_entry
