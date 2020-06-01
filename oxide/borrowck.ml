(* an implementation of ownership safety *)
open Meta
open Syntax
open Util

(* local type definition for a frame with places exploded *)
type place_frame = (place * ty) list

(* collect all the frames from the top of the stack up to and including the one containing x *)
let rec collect_frames (x : var) (gamma : var_env) : static_frame list =
  let x_is_in_frame (frame : static_frame) : bool =
    frame |> List.exists (fun entry -> match entry with Id (y, _) -> x <> y | Prov _ -> true)
  in match gamma with
  | top_frame :: _ when x_is_in_frame top_frame -> top_frame :: []
  | top_frame :: rest_of_stack -> top_frame :: collect_frames x rest_of_stack
  | [] -> []

(* explode the given variable and type into all of its sub-places and their respective types *)
let explode_places (var : var) (ty : ty) : place_frame =
  let proj (pi : place) (entry : path_entry) : place =
    (fst pi, (root_of pi, List.append (path_of pi) [entry]))
  in let rec explode (ty : ty) (pi : place) : place_frame =
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
let collect_places (frames : static_frame list) : place_frame list =
  frames |> List.map (flat_map (fun entry ->
                                 match entry with
                                 | Id (var, ty) -> explode_places var ty
                                 | Prov _ -> []))

(* collect all the closed-over frames in the given place frame list *)
let rec collect_closure_frames (frames : place_frame list) : static_frame list =
  let find_closed_frames (frame : place_frame) : static_frame list =
    frame |> List.map (fun ((_, ty) : place * ty) ->
                         match snd ty with
                         | Fun (_, _, _, _, Env frame_c, _, _) ->
                             [frame_c] |> collect_places |> collect_closure_frames |> List.cons frame_c
                         | _ -> [])
          |> List.flatten
  in frames |> List.map find_closed_frames |> List.flatten

(* keep all the places whose type is a reference type significant in some context *)
(* i.e. if context is unique, all references are significant for checking safety, and
        if context is shared, only unique references are significant *)
let keep_if_ref (context : owned) (places : place_frame list) : place_frame list =
  let may_conflict_with_context (omega : owned) : bool =
    match (context, omega) with
    | (Unique, _) -> true
    | (Shared, Unique) -> true
    | (Shared, Shared) -> false
  in let ref_test (_, ty) =
    match snd ty with Ref (_, omega, _) -> may_conflict_with_context omega | _ -> false
  in places |> List.map (List.filter ref_test)

(* decompose a place expression into an inner place and the rest of the expression path *)
(* invariant: if the path is non-empty, the first entry in the path will always be Deref *)
let decompose_place_expr (phi : place_expr) : place * expr_path =
  let (prefix, suffix) = expr_path_of phi |> partition ((<>) Deref)
  in let inner_pi = (fst phi, (expr_root_of phi, expr_path_to_path prefix |> Option.get))
  in (inner_pi, suffix)

let apply_suffix (suffix : expr_path) (phi : place_expr) : place_expr =
  (fst phi, (expr_root_of phi, List.append (expr_path_of phi) suffix))

(* kill all the loans for phi in ell *)
let kill_loans_for (phi : place_expr) (gamma : var_env) : var_env =
  let phi = apply_suffix [Deref] phi
  in let not_killed (loan : loan) : bool =
    let (_, phi_prime) = loan
    in not $ expr_prefix_of phi_prime phi
  in let kill_in_frame (frame : static_frame) : static_frame =
      frame |> List.map (fun entry ->
                           match entry with
                           | Id (var, ty) -> Id (var, ty)
                           | Prov (prov, loans) -> Prov (prov, List.filter not_killed loans))
  in gamma |> List.map kill_in_frame

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

(* check if the given place expression is safe to use in an omega context *)
let ownership_safe (_ : global_env) (delta : tyvar_env) (gamma : var_env)
                   (omega : owned) (tl_phi : place_expr) : (ty * loans) tc =
  (* check if the next operation in the suffix is permitted at this type *)
  let check_permission (ty : ty) (suffix : expr_path) : unit tc =
    match (snd ty, suffix) with
    | (Ref (_, omega_ref, _), Deref :: _) ->
      if is_at_least omega omega_ref then Succ ()
      else Fail (PermissionErr (ty, suffix, omega))
    | _ -> Succ ()
  (* return the given suffix without the Deref at the front, failing if no Deref *)
  in let skip_deref (suffix : expr_path) : expr_path =
    match suffix with
    | Deref :: path -> path
    | _ -> failwith "unreachable: skip_deref called with non_suffix path"
  (* remove all entries whose key is found in the exclusions list *)
  in let refine (exclusions : preplace list) (places : (place * ty) list) : (place * ty) list =
    List.filter (fun ((_, pi), _) -> not $ List.mem pi exclusions) places
  in let recent_frames = gamma |> collect_frames (expr_root_of tl_phi) |> collect_places
  in let closure_frames = recent_frames |> collect_closure_frames |> collect_places
  in let ref_places = List.append recent_frames closure_frames |> keep_if_ref omega |> List.flatten
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
          let loans = if tyvar_env_prov_mem delta prov then [] else loan_env_lookup gamma prov
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
      in let* ty = compute_ty_in omega delta gamma phi
      in Succ (ty, [(omega, phi)])
    (* O-Deref, O-DerefAbs *)
    | None ->
      let (inner_pi, suffix) = decompose_place_expr phi
      in let* ty = var_env_lookup gamma inner_pi
      in match snd ty with
      | Ref (prov, _, _) ->
        let* () = check_permission ty suffix
        in let loans = if tyvar_env_prov_mem delta prov then [] else loan_env_lookup gamma prov
        in let new_exclusions = List.map (snd >> fst >> decompose_place_expr >> snd) loans
        in let exclusions = List.concat [[snd inner_pi]; new_exclusions; exclusions]
        in let* safe_results =
          loans |> List.map (skip_deref suffix |> apply_suffix >> snd)
                |> map (impl_safe exclusions)
        in let refined_places = refine exclusions ref_places
        in let expr_not_disjoint_from (phi : place_expr) : place_expr -> bool =
          not >> expr_disjoint phi
        in let safety_test ((_, ty) : place * ty) : unit tc =
          match snd ty with
          | Ref (pv, _, _) ->
            let loans = if tyvar_env_prov_mem delta pv then [] else loan_env_lookup gamma pv
            in let conflicts = List.find_all (expr_not_disjoint_from phi >> snd) loans
            in if is_empty conflicts then Succ ()
            else SafetyErr ((omega, tl_phi), List.hd conflicts) |> fail
          | _ -> failwith "O-Deref/O-DerefAbs: unreachable"
        in let* () = for_each refined_places safety_test
        in let loans = flat_map snd safe_results
        in let* ty = compute_ty_in omega delta gamma phi
        in Succ (ty, List.cons (omega, phi) loans)
      | Uninit (loc, Ref (prov, omega, ty)) ->
        PartiallyMoved (inner_pi, (loc, Ref (prov, omega, ty))) |> fail
      | _ -> TypeMismatchRef ty |> fail
  in impl_safe [] tl_phi
