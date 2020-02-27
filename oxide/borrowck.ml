(* an implementation of ownership safety *)
open Meta
open Syntax
open Util

(* explode the given variable and type into all of its sub-places and their respective types *)
let explode_places (var : var) (ty : ty) : (place * ty) list =
  let proj (pi : place) (entry : path_entry) : place =
    (fst pi, (root_of pi, List.append (path_of pi) [entry]))
  in let rec explode (ty : ty) (pi : place) : (place * ty) list =
    match snd ty with
    | Any | Infer | BaseTy _ | TyVar _ | Ref _ | Fun _ | Array _ | Slice _ -> [(pi, ty)]
    | Rec fields ->
      (pi, ty) :: flat_map (fun (field, ty) ->  proj pi (Field field) |> explode ty) fields
    | Tup tys ->
      (pi, ty) :: flat_mapi (fun idx ty -> proj pi (Index idx) |> explode ty) tys
    | Struct (_, _, _, Some ty) -> explode ty pi
    | Struct (name, _, _, None) -> failwith $ "explode_places encountered untagged struct: " ^ name
    | Uninit _ -> [(pi, ty)]
  in explode ty (dummy, (var, []))

(* collect all the places and their respective types within a variable environment *)
(* n.b. this corresponds to \pi : \tau \in \Gamma *)
(* invariant: all struct types should have already been tagged *)
let collect_places (gamma : var_env) : (place * ty) list =
  flat_map (fun (var, ty) -> explode_places var ty) gamma

(* push closed over environments to the top level *)
let rec expand_closures (gamma : var_env) : var_env =
  let rec expand_closure (ty : ty) : var_env =
    match snd ty with
    | Any | Infer | BaseTy _ | TyVar _ -> []
    | Ref (_, _, ty) -> expand_closure ty
    | Fun (_, _, _, _, Unboxed, _, _) -> []
    | Fun (_, _, _, _, EnvVar _, _, _) -> []
    | Fun (_, _, _, _, Env gamma_c, _, _) -> expand_closures gamma_c
    | Fun (_, _, _, _, EnvOf _, _, _) -> failwith "expand_closure: unreachable"
    | Array (ty, _) | Slice ty -> expand_closure ty
    | Rec fields -> flat_map (expand_closure >> snd) fields
    | Tup tys -> flat_map expand_closure tys
    | Struct (_, _, _, Some ty) -> expand_closure ty
    | Struct (_, _, _, None) -> failwith "expand_closure: unreachable"
    | Uninit _ -> []
  in gamma |> flat_map (expand_closure >> snd) |> List.append gamma

(* keep all the places whose type is a reference type significant in some context *)
(* i.e. if context is unique, all references are significant for checking safety, and
        if context is shared, only unique references are significant *)
let keep_if_ref (context : owned) (places : (place * ty) list) : (place * ty) list =
  let significant_in_context (omega : owned) : bool =
    match (context, omega) with
    | (Unique, _) -> true
    | (Shared, Unique) -> true
    | (Shared, Shared) -> false
  in let ref_test (_, ty) =
    match snd ty with Ref (_, omega, _) -> significant_in_context omega | _ -> false
  in List.filter ref_test places

(* decompose a place expression into an inner place and the rest of the expression path *)
(* invariant: if the path is non-empty, the first entry in the path will always be Deref *)
let decompose_place_expr (phi : place_expr) : place * expr_path =
  let (prefix, suffix) = expr_path_of phi |> partition ((<>) Deref)
  in let inner_pi = (fst phi, (expr_root_of phi, expr_path_to_path prefix |> Option.get))
  in (inner_pi, suffix)

let apply_suffix (suffix : expr_path) (phi : place_expr) : place_expr =
  (fst phi, (expr_root_of phi, List.append (expr_path_of phi) suffix))

(* kill all the loans for phi in ell *)
let kill_loans_for (phi : place_expr) (ell : loan_env) : loan_env =
  let phi = apply_suffix [Deref] phi
  in let not_killed (loan : loan) : bool =
    let (_, phi_prime) = loan
    in not $ expr_prefix_of phi_prime phi
  in ell |> List.map (fun (prov, loans) -> (prov, List.filter not_killed loans))

(* are the given places disjoint? *)
let disjoint (pi1 : place) (pi2 : place) : bool =
  not (prefix_of pi1 pi2 || prefix_of pi2 pi1)

(* are the given place expressions disjoint? *)
let expr_disjoint (phi1 : place_expr) (phi2 : place_expr) : bool =
  not (expr_prefix_of phi1 phi2 || expr_prefix_of phi2 phi1)

(* are the places pi and place expression phi disjoint? *)
let expr_disjoint_place (pi : place) (phi : place_expr) : bool =
  (* they are disjoint if and only if the inner place of phi is disjoint from pi *)
  let (inner_pi, _) = decompose_place_expr phi
  in disjoint pi inner_pi

let ownership_safe (_ : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : var_env)
                   (omega : owned) (tl_phi : place_expr) : (ty * loans) tc =
  let check_permission (ty : ty) (suffix : expr_path) : unit tc =
    match (snd ty, suffix) with
    | (Ref (_, omega_ref, _), Deref :: _) ->
      if is_at_least omega omega_ref then Succ ()
      else Fail (PermissionErr (ty, suffix, omega))
    | _ -> Succ ()
  in let skip_deref (suffix : expr_path) : expr_path =
    match suffix with
    | Deref :: path -> path
    | _ -> failwith "unreachable: skip_deref called with non_suffix path"
  in let refine (exclusions : preplace list) (places : (place * ty) list) : (place * ty) list =
    List.filter (fun ((_, pi), _) -> not $ List.mem pi exclusions) places
  in let ref_places = expand_closures gamma |> collect_places |> keep_if_ref omega
  in let rec impl_safe (exclusions : preplace list) (phi : place_expr) : (ty * loans) tc =
    match place_expr_to_place phi with
    (* O-UniqueSafety, O-SharedSafety *)
    | Some (loc, pi) ->
      let exclusions = List.cons pi exclusions
      in let refined_places = refine exclusions ref_places
      in let not_disjoint_from (pi : place) : place -> bool = not >> disjoint pi
      in let expr_not_disjoint_from (pi : place) : place_expr -> bool =
        not >> expr_disjoint_place pi
      in let safety_test ((_, ty) : place * ty) : unit tc =
        match snd ty with
        | Ref (prov, _, _) ->
          let loans = if tyvar_env_prov_mem delta prov then [] else loan_env_lookup ell prov
          in let loan_to_place : loan -> place option = place_expr_to_place >> snd
          in let places_with_loans = List.map (fun loan -> (loan_to_place loan, loan)) loans
          in let conflicts =
            List.find_all (fun (opt_pi, (_, phi)) ->
                             match opt_pi with
                             | Some loan_pi -> not_disjoint_from (loc, pi) loan_pi
                             | None -> expr_not_disjoint_from (loc, pi) phi)
                          places_with_loans
          in if is_empty conflicts then Succ ()
          else Fail (SafetyErr ((omega, tl_phi), conflicts |> List.hd |> snd))
        | _ -> failwith "O-UniqueSafety/O-SharedSafety: unreachable"
      in let* () = for_each refined_places safety_test
      in let* ty = compute_ty_in omega delta ell gamma phi
      in Succ (ty, [(omega, phi)])
    (* O-Deref, O-DerefAbs *)
    | None ->
      let (inner_pi, suffix) = decompose_place_expr phi
      in let* ty = var_env_lookup gamma inner_pi
      in match snd ty with
      | Ref (prov, _, _) ->
        let* () = check_permission ty suffix
        in let loans = if tyvar_env_prov_mem delta prov then [] else loan_env_lookup ell prov
        in let new_exclusions = List.map (snd >> fst >> decompose_place_expr >> snd) loans
        in let exclusions = List.concat [[(snd inner_pi)]; new_exclusions; exclusions]
        in let* safe_results =
          loans |> List.map (skip_deref suffix |> apply_suffix >> snd)
                |> map (impl_safe exclusions)
        in let refined_places = refine exclusions ref_places
        in let expr_not_disjoint_from (phi : place_expr) : place_expr -> bool =
          not >> expr_disjoint phi
        in let safety_test ((_, ty) : place * ty) : unit tc =
          match snd ty with
          | Ref (prov, _, _) ->
            let loans = if tyvar_env_prov_mem delta prov then [] else loan_env_lookup ell prov
            in let conflicts = List.find_all (expr_not_disjoint_from phi >> snd) loans
            in if is_empty conflicts then Succ ()
            else SafetyErr ((omega, tl_phi), List.hd conflicts) |> fail
          | _ -> failwith "O-Deref/O-DerefAbs: unreachable"
        in let* () = for_each refined_places safety_test
        in let loans = flat_map snd safe_results
        in let* ty = compute_ty_in omega delta ell gamma phi
        in Succ (ty, List.cons (omega, phi) loans)
      | Uninit (loc, Ref (prov, omega, ty)) ->
        PartiallyMoved (inner_pi, (loc, Ref (prov, omega, ty))) |> fail
      | _ -> TypeMismatchRef ty |> fail
  in impl_safe [] tl_phi
