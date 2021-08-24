open Borrowck
open Edsl
open Meta
open Syntax
open Util

(* provenance validity judgment *)
let valid_prov (delta : tyvar_env) (gamma : var_env) (prov : prov) : unit tc =
  match loan_env_lookup_opt gamma prov with
  | None ->
    if tyvar_env_prov_mem delta prov then Succ ()
    else InvalidProv prov |> fail
  | Some loans ->
    let* frames = drop_frames_until prov gamma
    in let invalid_loans = loans |> List.filter (not >> var_env_contains_place_expr frames >> snd)
    in match invalid_loans with
    | [] -> Succ ()
    | loan :: _ -> UnboundLoanInProv (loan, prov) |> fail

(* type validity judgment *)
let rec valid_type (sigma : global_env) (delta : tyvar_env) (gamma : var_env)
                   (ty : ty) : unit tc =
  let rec valid (ty : ty) : unit tc =
    match snd ty with
    | Any | Infer | BaseTy _ -> Succ ()
    | TyVar tyvar ->
      if tyvar_env_ty_mem delta tyvar then Succ ()
      else InvalidType ty |> fail
    | Ref (prov, _, ty) ->
      let* () = valid_prov delta gamma prov
      in let* () = valid ty
      in let place_exprs =
        loan_env_lookup_opt gamma prov |> Option.to_list |> List.flatten |> List.map snd
      in let check_ty (pi : place_expr) : unit tc =
        let* ty_pi = compute_ty delta gamma pi
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
      in let* () = for_each param_tys $ valid_type sigma new_delta gamma
      in valid_type sigma new_delta gamma ret_ty
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
    | Env frame -> frame |> to_bindings |> List.map snd |> valid_many
    | EnvOf var -> UnevaluatedEnvOf var |> fail
  in valid ty
and valid_types (sigma : global_env) (delta : tyvar_env) (gamma : var_env)
    (tys : ty list) : unit tc =
  for_each_rev (valid_type sigma delta gamma) tys
and valid_loan (_ : global_env) (delta : tyvar_env) (gamma : var_env)
    (prov : prov) (loan : loan) =
  let (omega, phi) = loan
  in match compute_ty_in omega delta gamma phi with
     | Succ _ -> Succ ()
     | Fail (UnboundPlaceExpr _) -> UnboundLoanInProv (loan, prov) |> fail
     | Fail err -> Fail err
and valid_prov_entry (sigma : global_env) (delta : tyvar_env) (gamma : var_env)
    (entry : prov * loans) : unit tc =
  let (prov, loans) = entry
  in for_each_rev (valid_loan sigma delta gamma prov) loans
and valid_prov_entries (sigma : global_env) (delta : tyvar_env) (gamma : var_env)
    (entries : (prov * loans) list) : unit tc =
  for_each_rev (valid_prov_entry sigma delta gamma) entries
(* variable environment validity judgment *)
and valid_var_env (sigma : global_env) (delta : tyvar_env)
    (gamma : var_env) : unit tc =
  let* () = gamma |> stack_to_bindings |> List.map snd |> valid_types sigma delta gamma
  in gamma |> to_loan_env |> valid_prov_entries sigma delta gamma
(* environment validity judgment, assuming global environment is well-formed *)
and valid_envs (sigma : global_env) (delta : tyvar_env) (gamma : var_env) : unit tc =
  (* note: delta is well-formed by construction since it splits type variables by kind *)
  valid_var_env sigma delta gamma

(* shadow valid_type with a version that checks valid_envs first *)
let valid_type (sigma : global_env) (delta : tyvar_env) (gamma : var_env)
               (ty : ty) : unit tc =
  (* checking valid_envs corresponds to the side condition on the type validity judgment *)
  let* () = valid_envs sigma delta gamma
  in valid_type sigma delta gamma ty

(* checks type validity in before and after environments for better error reporting *)
let ty_valid_before_after (sigma : global_env) (delta : tyvar_env) (ty : ty)
                          (gamma_before : var_env) (gamma_after : var_env) : unit tc =
  match (valid_type sigma delta gamma_before ty,
         valid_type sigma delta gamma_after ty) with
  | (Succ (), Succ ()) -> Succ ()
  | (Succ (), Fail (InvalidProv prov as err)) ->
    (match loan_env_lookup_opt gamma_before prov with
    | Some loans ->
      let missing = List.find_all (not >> var_env_contains_place_expr gamma_after >> snd) loans
      in if is_empty missing then Succ ()
      else UnboundLoanInProv (List.hd missing, prov) |> fail
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
let type_check (sigma : global_env) (delta : tyvar_env) (gamma : var_env)
               (expr : expr) : (ty * var_env) tc =
  let rec tc (delta : tyvar_env) (gamma : var_env) (expr : expr) : (ty * var_env) tc =
    match snd expr with
    (* T-Unit, T-u32, T-True, T-False *)
    | Prim prim -> Succ (type_of prim, gamma)
    (* binary operations *)
    | BinOp (op, e1, e2) ->
      (match binop_to_types op with
       | (Some lhs_ty, Some rhs_ty, out_ty) ->
         let* (t1, gamma1) = tc delta gamma e1
         in if ty_eq t1 lhs_ty then
           let* (t2, gamma2) = tc delta gamma1 e2
           in if ty_eq t2 rhs_ty then
             let* (gammaFinal, _) = unify (fst expr) delta gamma2 t1 t2
             in Succ (out_ty, gammaFinal)
           else TypeMismatch (rhs_ty, t2) |> fail
         else TypeMismatch (lhs_ty, t1) |> fail
       | (None, None, out_ty) ->
         let* (t1, gamma1) = tc delta gamma e1
         in let* (t2, gamma2) = tc delta gamma1 e2
         in let* (gammaFinal, _) = unify (fst expr) delta gamma2 t1 t2
         in Succ (out_ty, gammaFinal)
       | _ -> failwith "T-BinOp: unreachable")
    (* T-Move and T-Copy *)
    | Move phi ->
      (* we compute an initial type to determine whether we're in Move or Copy *)
      let* computed_ty = compute_ty delta gamma phi
      in let* copy = copyable sigma computed_ty
      in let omega = if copy then Shared else Unique
      (* but we recompute the type with the right context to do permissions checking *)
      in let* ty = compute_ty_in omega delta gamma phi
      in (match ownership_safe sigma delta gamma omega phi with
       | Succ [(Unique, pi)] ->
         let* gammaPrime =
           match place_expr_to_place pi with
           | Some pi ->
             let* noncopy = noncopyable sigma ty
             in if is_init ty then
               if noncopy then
                 let* gammaPrime = var_env_uninit gamma ty pi
                 in Succ gammaPrime
               else Succ gamma
             else PartiallyMoved (pi, ty) |> fail
           | None ->
             let* copy = copyable sigma ty
             in if copy then Succ gamma
             else failwith "T-Move: unreachable"
         in Succ (ty, gammaPrime)
       | Succ _ ->
         if copy then Succ (ty, gamma)
         else failwith "T-Copy: unreachable"
       | Fail err -> Fail err)
    (* T-Drop made explicit to eliminate non-determinism *)
    | Drop phi ->
      (match place_expr_to_place phi with
       | Some pi ->
         let* ty = var_env_lookup gamma pi
         in if is_init ty then
           let* gammaPrime = var_env_uninit gamma (inferred, BaseTy Unit) pi
           in Succ ((inferred, BaseTy Unit), gammaPrime)
         else PartiallyMoved (pi, ty) |> fail
       | None -> CannotMove phi |> fail)
    (* T-Borrow *)
    | Borrow (prov, omega, pi) ->
      let* loans = ownership_safe sigma delta gamma omega pi
      in let* () = prov_not_in_closure gamma prov
      in let* ty = compute_ty_in omega delta gamma pi
      in if tyvar_env_prov_mem delta prov then CannotBorrowIntoAbstractProvenance prov |> fail
      else if prov |> loan_env_lookup gamma |> non_empty then
        CannotBorrowIntoInUseProvenance prov |> fail
      else let* updated_gamma = loan_env_prov_update prov loans gamma
      in Succ ((inferred, Ref (prov, omega, ty)), updated_gamma)
    (* T-BorrowIndex *)
    | BorrowIdx (prov, omega, pi, e) ->
      (match tc delta gamma e with
       | Succ ((_, BaseTy U32), gamma1) ->
         let* loans = ownership_safe sigma delta gamma1 omega pi
         in let* () = prov_not_in_closure gamma1 prov
         in let* ty = compute_ty_in omega delta gamma1 pi
         in if tyvar_env_prov_mem delta prov then CannotBorrowIntoAbstractProvenance prov |> fail
         else if prov |> loan_env_lookup gamma |> non_empty then
           CannotBorrowIntoInUseProvenance prov |> fail
         else let* updated_gamma = loan_env_prov_update prov loans gamma1
         in Succ ((inferred, Ref (prov, omega, ty)), updated_gamma)
       | Succ (found, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
       | Fail err -> Fail err)
    (* T-BorrowSlice *)
    | BorrowSlice (prov, omega, pi, e1, e2) ->
      (match tc delta gamma e1 with
       | Succ ((_, BaseTy U32), gamma1) ->
         (match tc delta gamma1 e2 with
          | Succ ((_, BaseTy U32), gamma2) ->
            let* loans = ownership_safe sigma delta gamma2 omega pi
            in let* () = prov_not_in_closure gamma2 prov
            in let* ty = compute_ty_in omega delta gamma2 pi
            in if tyvar_env_prov_mem delta prov then CannotBorrowIntoAbstractProvenance prov |> fail
            else if prov |> loan_env_lookup gamma |> non_empty then
              CannotBorrowIntoInUseProvenance prov |> fail
            else let* updated_gamma = loan_env_prov_update prov loans gamma2
            in Succ ((inferred, Ref (prov, omega, ty)), updated_gamma)
          | Succ (found, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
          | Fail err -> Fail err)
       | Succ (found, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
       | Fail err -> Fail err)
    (* T-IndexCopy *)
    | Idx (pi, e) ->
      (match tc delta gamma e with
       | Succ ((_, BaseTy U32), gamma1) ->
         let* _ = ownership_safe sigma delta gamma1 Shared pi
         in (match compute_ty_in Shared delta gamma1 pi with
          | Succ (_, Array (ty, _)) ->
            let* copy = copyable sigma ty
            in if copy then (ty, gamma1) |> succ
            else CannotMove pi |> fail
          | Succ found -> TypeMismatchArray found |> fail
          | Fail err -> Fail err)
       | Succ (found, _) -> TypeMismatch ((dummy, BaseTy U32), found) |> fail
       | Fail err -> Fail err)
    (* T-Seq *)
    | Seq (e1, e2) ->
      let* (_, gamma1) = tc delta gamma e1
      in let still_used_provs = used_provs gamma1
      in let* gamma1Prime = clear_unused_provenances still_used_provs gamma1
      in tc delta gamma1Prime e2
    (* T-Branch *)
    | Branch (e1, e2, e3) ->
      (match tc delta gamma e1 with
       | Succ ((_, BaseTy Bool), gamma1) ->
         let* (ty2, gamma2) = tc delta gamma1 e2
         in let* (ty3, gamma3) = tc delta gamma1 e3
         in let gammaPrime = union gamma2 gamma3
         in let* (gammaFinal, tyFinal) = unify (fst expr) delta gammaPrime ty2 ty3
         in let* () = valid_type sigma delta gammaFinal tyFinal
         in Succ (tyFinal, gammaFinal)
       | Succ (found, _) -> TypeMismatch ((dummy, BaseTy Bool), found) |> fail
       | Fail err -> Fail err)
    (* T-LetProv *)
    | LetProv (new_provs, e) ->
      let entry_in_new_provs (entry : frame_entry) : bool =
        match entry with
        | Id _ -> false
        | Prov (prov, _) -> new_provs |> List.map snd |> List.mem (snd prov)
      in if gamma |> List.flatten |> List.exists entry_in_new_provs then
        let entry = gamma |> List.flatten |> List.find entry_in_new_provs
        in match entry with
        | Prov (prov, _) -> CannotShadowProvenance prov |> fail
        | Id _ -> failwith "unreachable: entry_in_new_provs never returns true for Id"
      else let gammaPrime = loan_env_include_all new_provs [] gamma
      in let* (ty_out, gamma_out) = tc delta gammaPrime e
      in let final_gamma = shift_n (List.length new_provs) gamma_out
      in let* () = valid_type sigma delta final_gamma ty_out
      in Succ (ty_out, final_gamma)
    (* T-LetInfer *)
    | Let (var, (_, Infer), e1, e2) ->
      let* (ty1, gamma1) = tc delta gamma e1
      in let* () = valid_type sigma delta gamma1 ty1
      in let gamma1Prime = var_env_include gamma1 var ty1
      in let still_used = used_provs gamma1Prime
      in let* gamma1Prime = gamma1Prime |> clear_unused_provenances still_used
      in let* (ty2, gamma2) = tc delta gamma1Prime e2
      in let* gamma2Prime = var |> var_to_place |> var_env_uninit gamma2 ty2
      in let still_used = List.concat [used_provs gamma2Prime; provs_used_in_ty ty2]
      in let* gamma2Prime = gamma2Prime |> clear_unused_provenances still_used >>= (succ >> shift)
      in let* () = ty_valid_before_after sigma delta ty2 gamma2 gamma2Prime
      in Succ (ty2, gamma2Prime)
    (* T-Let *)
    | Let (var, ann_ty, e1, e2) ->
      let* (ty1, gamma1) = tc delta gamma e1
      in let* () = valid_type sigma delta gamma1 ty1
      in let* gamma1Prime = subtype Combine delta gamma1 ty1 ann_ty
      in let* ann_ty = flow_closed_envs_forward ty1 ann_ty
      in let gamma1Prime = var_env_include gamma1Prime var ann_ty
      in let still_used = used_provs gamma1Prime
      in let* gamma1Prime = gamma1Prime |> clear_unused_provenances still_used
      in let* (ty2, gamma2) = tc delta gamma1Prime e2
      in let* gamma2Prime = var |> var_to_place |> var_env_uninit gamma2 ty2
      in let still_used = List.concat [used_provs gamma2Prime; provs_used_in_ty ty2]
      in let* gamma2Prime = gamma2Prime |> clear_unused_provenances still_used >>= (succ >> shift)
      in let* () = ty_valid_before_after sigma delta ty2 gamma2 gamma2Prime
      in Succ (ty2, gamma2Prime)
    (* T-Assign and T-AssignDeref *)
    | Assign (phi, e) ->
      let* (ty_update, gamma1) = tc delta gamma e
      in let* ty_old = compute_ty_in Unique delta gamma1 phi
      in (match place_expr_to_place phi with
       (* T-Assign *)
       | Some pi ->
         let gamma1 = gamma1 |> kill_loans_for phi
         in let* gammaPrime = subtype Noop delta gamma1 ty_update ty_old
         in let* _ = ownership_safe sigma delta gammaPrime Unique phi
         in let* gammaPrime = gammaPrime |> var_env_type_update pi ty_update
         in Succ ((inferred, BaseTy Unit), gammaPrime)
       (* T-AssignDeref *)
       | None ->
         let* gammaPrime = subtype Combine delta gamma1 ty_update ty_old
         in let* _ = ownership_safe sigma delta gammaPrime Unique phi
         in Succ ((inferred, BaseTy Unit), gammaPrime))
    (* T-Abort *)
    | Abort _ -> Succ ((inferred, Any), gamma)
    (* T-While *)
    | While (e1, e2) ->
      (match tc delta gamma e1 with
       | Succ ((_, BaseTy Bool), gamma1) ->
         let* (_, gamma2) =  tc delta gamma1 e2
         in (match tc delta gamma2 e1 with
            | Succ ((_, BaseTy Bool), gamma3) when gamma2 = gamma3 -> tc delta gamma2 e2
            | Succ ((_, BaseTy Bool), gamma3) -> VarEnvMismatch (fst expr, gamma2, gamma3) |> fail
            | Succ (found, _) -> TypeMismatch ((dummy, BaseTy  Bool), found) |> fail
            | Fail err -> Fail err)
       | Succ (found, _) -> TypeMismatch ((dummy, BaseTy Bool), found) |> fail
       | Fail err -> Fail err)
    (* T-ForArray, T-ForSlice *)
    | For (var, e1, e2) ->
      (match tc delta gamma e1 with
       (* T-ForArray *)
       | Succ ((_, Array (elem_ty, _)), gamma1) ->
         let gamma1Prime = var_env_include gamma1 var elem_ty
         in let* (_, gamma2) = tc delta gamma1Prime e2
         in let gamma2Prime = shift gamma2
         in if gamma2Prime = gamma1 then ((inferred, BaseTy Unit), gamma1) |> succ
         else VarEnvMismatch (fst e2, gamma1, gamma2Prime) |> fail
       (* T-ForSlice *)
       | Succ ((_, Ref (prov, omega, (_, Slice elem_ty))), gamma1) ->
         let gamma1Prime = var_env_include gamma1 var (inferred, Ref (prov, omega, elem_ty))
         in let* (_, gamma2) = tc delta gamma1Prime e2
         in let gamma2Prime = shift gamma2
         in if gamma2Prime = gamma1 then ((inferred, BaseTy Unit), gamma1) |> succ
         else VarEnvMismatch (fst e2, gamma1, gamma2Prime) |> fail
       | Succ (found, _) -> TypeMismatchIterable found |> fail
       | Fail err -> Fail err)
    (* T-Function *)
    | Fn fn ->
      (match global_env_find_fn sigma fn with
       | Some (_, evs, provs, tyvars, params, ret_ty, bounds, _) ->
         let fn_ty : ty =
           (inferred, Fun (evs, provs, tyvars, List.map snd params, Env [], ret_ty, bounds))
         in Succ (fn_ty, gamma)
       | None ->
         (match gamma |> stack_to_bindings |> List.assoc_opt fn with
          (* T-Move for a closure *)
          | Some (_, Fun _) ->
            (match ownership_safe sigma delta gamma Unique (fst expr, (fn, [])) with
            | Succ [(Unique, _)] ->
              let* ty = compute_ty_in Unique delta gamma (fst expr, (fn, []))
              in let* closure_copyable = copyable sigma ty
              in if closure_copyable then Succ (ty, gamma)
              else let* gammaPrime = gamma |> var_env_type_update (fst expr, (fn, [])) (uninit ty)
              in Succ (ty, gammaPrime)
            | Succ _ -> failwith "T-Move as T-Function: unreachable"
            | Fail err -> Fail err)
          | Some ((_, Uninit (_, Fun _)) as uninit_fn_ty) ->
            MovedFunction (expr, uninit_fn_ty) |> fail
          | (Some (_, Ref (_, omega, ((_, Fun _))))) ->
            (match ownership_safe sigma delta gamma omega (fst expr, (fn, [Deref])) with
            | Succ _ -> let* ty = compute_ty_in omega delta gamma (fst expr, (fn, [Deref]))
                        in Succ (ty, gamma)
            | Fail err -> Fail err)
          | Some ty -> TypeMismatchFunction ty |> fail
          | None -> UnknownFunction (fst expr, fn) |> fail))
    (* T-Closure *)
    | Fun (provs, tyvars, params, opt_ret_ty, body) ->
      let* free_vars =
        List.filter (fun var -> not $ List.mem_assoc var params) <$> free_vars body
      in let* moved_vars = free_nc_vars sigma gamma body
      in let* gamma_c =
        free_vars |> map (fun var ->
                            let* ty = var_env_lookup_var gamma var
                            in Id (var, ty) |> succ)
      in let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let* gammaMoved = var_env_move_many gamma moved_vars
      in let gammaPrime =
        List.fold_left var_include_fold (var_env_new_frame gammaMoved gamma_c) params
      in let deltaPrime = delta |> tyvar_env_add_provs provs |> tyvar_env_add_ty_vars tyvars
      in let not_in_provs (prov : prov) : bool =
        not $ tyvar_env_prov_mem delta prov &&
        not $ loan_env_mem gammaPrime prov &&
        not $ contains prov provs
      in let free_provs =
        free_provs body |> List.filter not_in_provs
                        |> List.sort_uniq (fun (_, p1) (_, p2) -> String.compare p1 p2)
      in let gammaPrime = gammaPrime |> loan_env_include_all free_provs []
      in let* (ret_ty, gamma_body) = tc deltaPrime gammaPrime body
      in let* () = find_refs_to_captured deltaPrime gamma_body ret_ty gamma_c
      in let still_used = List.concat [used_provs gammaPrime; provs_used_in_ty ret_ty]
      in let fn_ty (ret_ty : ty) : ty =
           (inferred, Fun ([], provs, tyvars, List.map snd params, Env gamma_c, ret_ty, []))
      in let* gamma = pop gamma_body |> clear_unused_provenances still_used
      in (match opt_ret_ty with
          | Some ann_ret_ty ->
            let* gammaFinal = subtype Combine deltaPrime gamma ret_ty ann_ret_ty
            in Succ (fn_ty ann_ret_ty, gammaFinal)
          | None -> Succ (fn_ty ret_ty, gamma))
    (* T-AppFunction and T-AppClosure combined *)
    | App (fn, envs, new_provs, new_tys, args) ->
      (match tc delta gamma fn with
       | Succ ((_, Fun (evs, provs, tyvars, params, _, ret_ty, bounds)), gammaF) ->
         let* (arg_tys, gammaN) = tc_many delta gammaF args
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
         in let* gammaPrime = check_bounds delta gammaN instantiated_bounds
         in let types_mismatch ((expected, found) : ty * ty) : bool tc =
           match subtype CombineUnrestricted delta gammaPrime found expected with
           | Succ _ -> Succ false
           | Fail (UnificationFailed _) -> Succ true
           | Fail err -> Fail err
         in let* type_mismatches = find types_mismatch ty_pairs
         in (match type_mismatches with
             | None ->
               let new_ret_ty = do_sub ret_ty
               in let* () = valid_type sigma delta gammaPrime new_ret_ty
               in Succ (new_ret_ty, gammaPrime)
             | Some (expected, found) -> TypeMismatch (expected, found) |> fail)
       | Succ ((_, Uninit (_, Fun _) as uninit_ty), _) -> MovedFunction (fn, uninit_ty) |> fail
       | Succ (found, _) -> TypeMismatchFunction found |> fail
       | Fail err -> Fail err)
    (* T-Tuple *)
    | Tup exprs ->
      let* (tys, gammaPrime) = tc_many delta gamma exprs
      in let final_ty : ty = (inferred, Tup tys)
      in Succ (final_ty, gammaPrime)
    (* T-Array *)
    | Array exprs ->
      let* (tys, gammaPrime) = tc_many delta gamma exprs
      in let* (gammaFinal, unified_ty) = unify_many (fst expr) delta gammaPrime tys
      in let final_ty : ty = (inferred, Array (unified_ty, List.length tys))
      in Succ (final_ty, gammaFinal)
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
         in let tc_exp (gamma : var_env) (p : expr * ty) =
           let (expr, expected_ty) = p
           in let* (found_ty, gamma_prime) = tc delta gamma expr
           in let* gamma_final = subtype Combine delta gamma_prime found_ty expected_ty
           in Succ gamma_final
         in let* gamma_prime = foldl tc_exp gamma pairs
         in let tagged_ty : ty option = Some (inferred, Rec expected_fields)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), gamma_prime)
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
         in let tc_exp (gamma : var_env) (p : expr * ty) =
           let (expr, expected_ty) = p
           in let* (found_ty, gamma_prime) = tc delta gamma expr
           in let* gamma_final = subtype Combine delta gamma_prime found_ty expected_ty
           in Succ gamma_final
         in let* gamma_prime = foldl tc_exp gamma pairs
         in let tagged_ty : ty option = Some (inferred, Tup expected_tys)
         in Succ ((inferred, Struct (name, provs, tys, tagged_ty)), gamma_prime)
       | Some (Rec _) -> WrongStructConstructor (fst expr, name, Tup) |> fail
       | None ->
         if global_env_find_struct sigma name == None then UnknownStruct (fst expr, name) |> fail
         else WrongStructConstructor (fst expr, name, Tup) |> fail)
    (* T-Pointer *)
    | Ptr _ -> failwith "unimplemented: T-Pointer"
    (* T-ClosureValue *)
    | Closure _ -> failwith "unimplemented: T-ClosureValue"
    (* T-Shift *)
    | Shift _ -> failwith "unimplemented: T-Shift"
    (* T-Framed *)
    | Framed _ -> failwith "unimplemented: T-Framed"
  and tc_many (delta : tyvar_env) (gamma : var_env)
              (exprs : expr list) : (ty list * var_env) tc =
    let tc_next (e : expr) ((curr_tys, curr_gamma) : ty list * var_env) =
      let* (ty, gammaPrime) = tc delta curr_gamma e
      in Succ (List.cons ty curr_tys, gammaPrime)
    in foldr tc_next exprs ([], gamma)
  in let* (out_ty, out_gamma) = tc delta gamma expr
  in let* () = valid_type sigma delta out_gamma out_ty
  in (out_ty, out_gamma) |> succ

(* global environment validity judgment *)
let wf_global_env (sigma : global_env) : unit tc =
  let* sigma = List.cons drop sigma |> struct_to_tagged
     (* global entry validity judgment *)
  in let valid_global_entry (entry : global_entry) : unit tc =
    match entry with
    (* WF-FunctionDef*)
    | FnDef (_, evs, provs, tyvars, params, ret_ty, bounds, body) ->
      let not_in_provs (prov : prov) : bool = provs |> contains prov |> not
      in let free_provs = (* this lets us infer letprovs for unbound provenances *)
         free_provs body |> List.filter not_in_provs
                         |> List.sort_uniq (fun (_, p1) (_, p2) -> String.compare p1 p2)
      in let delta = empty_delta |> tyvar_env_add_env_vars evs
                                 |> tyvar_env_add_provs provs
                                 |> tyvar_env_add_ty_vars tyvars
      in let* delta = foldl (fun delta (prov1, prov2) -> tyvar_env_add_abs_sub delta prov1 prov2)
                            delta bounds
      in let var_include_fold (gamma : var_env) (pair : var * ty) : var_env =
        var_env_include gamma (fst pair) (snd pair)
      in let gamma =
        params |> List.fold_left var_include_fold empty_gamma
               |> loan_env_include_all free_provs []
      in let* (output_ty, gammaPrime) = type_check sigma delta gamma body
      in (match valid_type sigma delta gammaPrime output_ty with
      | Succ () ->
        (* find_refs_to_params corresponds to return type validity: WF-ReturnRef *)
        let* () = find_refs_to_params delta gammaPrime output_ty params
        in let* _ = subtype Combine delta gammaPrime output_ty ret_ty
        in Succ ()
      (* this is caused by a provenance being killed by its loans dropping out of scope *)
      (* in other words: references to temporaries cause an InvalidReturnType *)
      | Fail (InvalidProv prov) -> InvalidReturnType (output_ty, prov) |> fail
      | Fail err -> Fail err)
    (* T-RecordStructDef *)
    | RecStructDef (_, name, provs, tyvars, fields) ->
      let delta = empty_delta |> tyvar_env_add_provs provs |> tyvar_env_add_ty_vars tyvars
      in let* () = name |> global_env_find_struct sigma |> Option.get |> valid_copy_impl sigma
      in let* () = List.map snd fields |> valid_types sigma delta empty_gamma
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
      in let* () = valid_types sigma delta empty_gamma tys
      in Succ ()
  in for_each sigma valid_global_entry
