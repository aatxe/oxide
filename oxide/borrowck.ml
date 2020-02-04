(* an implementation of ownership safety *)
open Syntax
open Meta
open Util

(* explode the given variable and type into all of its sub-places and their respective types *)
let explode_places (var : var) (ty : ty) : (place * ty) list =
  let proj (pi : place) (entry : path_entry) : place =
    (fst pi, (root_of pi, List.append (path_of pi) [entry]))
  in let rec explode (pi : place) (ty : ty) : (place * ty) list =
    match snd ty with
    | Any | BaseTy _ | TyVar _ | Ref _ | Fun _ | Array _ | Slice _ -> [(pi, ty)]
    | Rec fields ->
      (pi, ty) :: flat_map (fun (field, ty) -> explode (proj pi (Field field)) ty) fields
    | Tup tys ->
      (pi, ty) :: flat_mapi (fun idx ty -> explode (proj pi (Index idx)) ty) tys
    | Struct (_, _, _, Some ty) -> explode pi ty
    | Struct (name, _, _, None) -> failwith ("explode_places encountered untagged struct: " ^ name)
    | Uninit _ -> [(pi, ty)]
  in explode (dummy, (var, [])) ty

(* collect all the places and their respective types within a variable environment *)
(* n.b. this corresponds to \pi : \tau \in \Gamma *)
(* invariant: all struct types should have already been tagged *)
let collect_places (gamma : var_env) : (place * ty) list =
  flat_map (fun (var, ty) -> explode_places var ty) gamma

(* push closed over environments to the top level *)
let rec expand_closures (gamma : var_env) : var_env =
  let rec expand_closure (ty : ty) : var_env =
    match snd ty with
    | Any | BaseTy _ | TyVar _ -> []
    | Ref (_, _, ty) -> expand_closure ty
    | Fun (_, _, _, gamma_c, _) -> expand_closures gamma_c
    | Array (ty, _) | Slice ty -> expand_closure ty
    | Rec fields -> flat_map (compose expand_closure snd) fields
    | Tup tys -> flat_map expand_closure tys
    | Struct (_, _, _, Some ty) -> expand_closure ty
    | Struct (_, _, _, None) -> failwith "expand_closure: unreachable"
    | Uninit _ -> []
  in List.append gamma (flat_map (compose expand_closure snd) gamma)

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

let decompose_place_expr (phi : place_expr) : place * expr_path =
  let (prefix, suffix) = partition ((!=) Deref) (expr_path_of phi)
  in let inner_pi = (fst phi, (expr_root_of phi, unwrap (expr_path_to_path prefix)))
  in (inner_pi, suffix)

let apply_suffix (phi : place_expr) (suffix : expr_path) : place_expr =
  (fst phi, (expr_root_of phi, List.append (expr_path_of phi) suffix))

(* are the given places disjoint? *)
let disjoint (pi1 : place) (pi2 : place) : bool =
  (* two places are not disjoint if their roots are equal... *)
  if root_of pi1 = root_of pi2 then
    (* ... and one path is a prefix of the other  *)
    not (is_prefix_of (path_of pi1) (path_of pi2) || is_prefix_of (path_of pi2) (path_of pi1))
  else true

let ownership_safe (_ : global_env) (ell : loan_env) (gamma : var_env) (omega : owned)
                   (tl_phi : place_expr) : (ty * loans) tc =
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
  in let rec impl_safe (exclusions : preplace list) (phi : place_expr) : (ty * loans) tc =
    match place_expr_to_place phi with
    (* O-UniqueSafety, O-SharedSafety *)
    | Some (loc, pi) ->
      let ref_places = keep_if_ref omega (collect_places (expand_closures gamma))
      in let exclusions = List.cons pi exclusions
      in let refined_places =
        List.filter (fun ((_, pi), _) -> not (List.mem pi exclusions)) ref_places
      in let not_disjoint_from (pi : place) : place -> bool = compose not (disjoint pi)
      in let safety_test ((_, ty) : place * ty) : unit tc =
        match snd ty with
        | Ref (prov, _, _) ->
          let loans = loan_env_lookup ell prov
          in let loan_to_place : loan -> place option = compose place_expr_to_place snd
          in let places_with_loans = List.map (fun loan -> (loan_to_place loan, loan)) loans
          in let conflicts =
            List.find_all (fun (opt_pi, (_, _)) ->
                             match opt_pi with
                             | Some loan_pi -> not_disjoint_from (loc, pi) loan_pi
                             | None -> false)
                          places_with_loans
          in if is_empty conflicts then Succ ()
          else Fail (SafetyErr ((omega, tl_phi), snd (List.hd conflicts)))
        | _ -> failwith "O-UniqueSafety/O-SharedSafety: unreachable"
      in let* () = for_each refined_places safety_test
      in let* root_ty = var_env_lookup_expr_root gamma phi
      in let* ty = compute_ty_in omega ell root_ty (expr_path_of phi)
      in Succ (ty, [(omega, phi)])
    (* O-Deref, O-DerefAbs *)
    | None ->
      let (inner_pi, suffix) = decompose_place_expr phi
      in let* ty = var_env_lookup gamma inner_pi
      in match snd ty with
      | Ref (prov, _, _) ->
        let* () = check_permission ty suffix
        in let loans = loan_env_lookup ell prov
        in let new_exclusions = List.map (fun (_, phi) -> fstsnd (decompose_place_expr phi)) loans
        in let exclusions = List.concat [[(snd inner_pi)]; new_exclusions; exclusions]
        in let* safe_results =
          map (impl_safe exclusions)
              (List.map (fun (_, phi) -> apply_suffix phi (skip_deref suffix)) loans)
        in let loans = flat_map snd safe_results
        in let* root_ty = var_env_lookup_expr_root gamma phi
        in let* ty = compute_ty_in omega ell root_ty (expr_path_of phi)
        in Succ (ty, List.cons (omega, phi) loans)
      | Uninit (loc, Ref (prov, omega, ty)) ->
        Fail (PartiallyMoved (inner_pi, (loc, Ref (prov, omega, ty))))
      | _ -> Fail (TypeMismatchRef ty)
  in impl_safe [] tl_phi
