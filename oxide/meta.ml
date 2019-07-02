open Syntax
open Util

(* checks if the given list is empty *)
let is_empty (lst : 'a list) : bool = List.length lst = 0

(* checks that omega_prime is at least omega *)
let is_at_least (omega : owned) (omega_prime : owned) : bool =
  match (omega, omega_prime) with
  | (Shared, _) -> true
  | (Unique, Unique) -> true
  | (Unique, Shared) -> false

(* extract all the specific loans from a given region *)
let prov_to_loans (ell : loan_env) (prov : prov) : loans =
  loan_env_lookup ell prov

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
    | Struct (name, provs, tys) ->
      let work (pv : prov) (provs : provs) =
        List.cons (if (snd pv) = (snd that) then this else pv) provs
      in let new_provs = List.fold_right work provs []
      in (loc, Struct (name, new_provs, sub_many tys))
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
    | Struct (name, provs, tys) -> (loc, Struct (name, provs, sub_many tys))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  in sub ty

let subst_many (ty : ty) (pairs : (ty * ty_var) list) : ty =
  List.fold_right (fun pair ty -> subst ty (fst pair) (snd pair)) pairs ty

(* given a root identier x, compute all the places based on tau *)
let rec places_typ (sigma : global_env) (pi : place) (tau : ty) : place_env tc =
  let work (acc : place_env tc) (pair : place * ty) =
    let* acc = acc
    in let (pi, ty) = pair
    in let* gam_ext = places_typ sigma pi ty
    in Succ (List.append acc gam_ext)
  in let idx_func (idx : int) (typ : ty) =
    let piPrime : place = IndexProj  (pi, idx)
    in (piPrime, typ)
  in let field_func (pair : field * ty) =
    let piPrime : place = FieldProj (pi, fst pair)
    in (piPrime, snd pair)
  in match snd tau with
  | Any -> Succ [(pi, tau)]
  | BaseTy _ -> Succ [(pi, tau)]
  | TyVar _ -> Succ [(pi, tau)]
  | Ref (_, _, _) -> Succ [(pi, tau)]
  | Fun (_, _, _, _, _) -> Succ [(pi, tau)]
  | Array (_, _) -> Succ [(pi, tau)]
  | Slice (_)  -> Succ [(pi, tau)]
  | Tup (tys) ->
    let projs = List.mapi idx_func tys
    in List.fold_left work (Succ [(pi, tau)]) projs
  | Struct (name, provs, tys) ->
    (match global_env_find_struct sigma name with
     | Some (Rec (_, _, dfn_provs, tyvs, fields)) ->
        let sub (pair : field * ty) : field * ty =
          let (field, ty) = pair
          in (field, subst_many (subst_many_prov ty (List.combine provs dfn_provs))
                                (List.combine tys tyvs))
        in let new_fields = List.map sub fields
        in let projs = List.map field_func new_fields
        in List.fold_left work (Succ [(pi, tau)]) projs
     | Some (Tup (_, _, dfn_provs, tyvs, fields)) ->
        let sub (ty : ty) : ty =
          subst_many (subst_many_prov ty (List.combine provs dfn_provs)) (List.combine tys tyvs)
        in let new_fields = List.map sub fields
        in let projs = List.mapi idx_func new_fields
        in List.fold_left work (Succ [(pi, tau)]) projs
     | None -> Fail (UnknownStruct (fst tau, name)))

(* place env operations *)

let place_env_lookup (gamma : place_env) (x : place) = List.assoc x gamma
let place_env_lookup_opt (gamma : place_env) (x : place) = List.assoc_opt x gamma
let place_env_lookup_speco (gamma : place_env) (x : place_expr) =
  match place_expr_to_place x with
  | Some pi -> place_env_lookup_opt gamma pi
  | None -> None
let place_env_lookup_spec (gamma : place_env) (x : place_expr) =
  match (place_env_lookup_speco gamma x) with
  | Some pi -> pi
  | None ->
    Format.fprintf Format.str_formatter "place %a was not bound in place_env %a"
      pp_place_expr x pp_place_env gamma;
    failwith (Format.flush_str_formatter())
let place_env_contains_spec (gamma : place_env) (x : place_expr) =
  match place_env_lookup_speco gamma x with
  | Some _ -> true
  | None -> false
let place_env_include (sigma : global_env) (gamma : place_env) (x : place) (typ : ty) =
  let* ext = places_typ sigma x typ
  in Succ (List.append ext gamma)
let place_env_append (gamma1 : place_env) (gamma2 : place_env) = List.append gamma1 gamma2
let place_env_exclude (gamma : place_env) (x : place) = List.remove_assoc x gamma

(* compute all the at-least-omega loans in a given gamma *)
let rec all_loans (omega : owned) (ell : loan_env) (gamma : place_env) : loans =
  let rec work (typ : ty) (loans : loans) : loans =
    match snd typ with
    | Any -> loans
    | BaseTy _ -> loans
    | TyVar _ -> loans
    | Ref (prov, omega_prime, typ) ->
      if is_at_least omega omega_prime then List.append (prov_to_loans ell prov) (work typ loans)
      else work typ loans
    | Fun (_, _, _, gamma_c, _) -> List.append loans (all_loans omega ell gamma_c)
    | Array (typ, _) -> work typ loans
    | Slice typ -> work typ loans
    | Tup typs -> List.fold_right List.append (List.map (fun typ -> work typ []) typs) loans
    | Struct (_, provs, _) ->  List.concat (loans :: List.map (prov_to_loans ell) provs)
  in List.fold_right (fun entry -> work (snd entry)) gamma []

(*  compute all subplaces from a given place *)
let all_subplaces (pi : place_expr) : place_expr list =
  let rec work (pi : place_expr) (places : place_expr list) : place_expr list =
    match pi with
    | Var _ -> List.cons pi places
    | Deref _ -> List.cons pi places
    | FieldProj (pi_prime, _) -> work pi_prime (List.cons pi places)
    | IndexProj (pi_prime, _) -> work pi_prime (List.cons pi places)
  in work pi []

(* find the root of a given place *)
let rec root_of (pi : place_expr) : var =
  match pi with
  | Var root -> root
  | Deref pi_prime -> root_of pi_prime
  | FieldProj (pi_prime, _) -> root_of pi_prime
  | IndexProj (pi_prime, _) -> root_of pi_prime

(* find all at-least-omega loans in gamma that have to do with pi *)
let find_loans (omega : owned) (ell : loan_env) (gamma : place_env) (pi : place_expr) : loans =
  (* n.b. this is actually too permissive because of reborrowing and deref *)
  let root_of_pi = root_of pi
  in let relevant (loan : loan) : bool =
    (* a loan is relevant if it is a descendant of any subplace of pi *)
    let (_, pi_prime) = loan
       (* the easiest way to check is to check if their roots are the same *)
    in root_of_pi = root_of pi_prime
  in List.filter relevant (all_loans omega ell gamma)

(* decompose the type by peforming the operations in phi on it to compute the type of phi *)
(* invariant: ty must be the type of root_of phi on use *)
let rec compute_ty (sigma : global_env) (phi : place_expr_parts) (ty : ty) : ty tc =
  match (phi, snd ty) with
  | ([], _) -> Succ ty
  | (Deref :: phi_prime, Ref (_, _, ty)) -> compute_ty sigma phi_prime ty
  | (FieldProj field :: phi_prime, Struct (name, provs, tys)) ->
    (match global_env_find_struct sigma name with
     | Some (Rec (_, _, dfn_provs, tyvars, dfn_tys)) ->
       (match List.assoc_opt field dfn_tys with
        | Some ty ->
          let new_ty = subst_many (subst_many_prov ty (List.combine provs dfn_provs))
                                  (List.combine tys tyvars)
          in compute_ty sigma phi_prime new_ty
        | None -> Fail (InvalidOperationOnType (List.hd phi, ty)))
     | Some (Tup _) -> Fail (InvalidOperationOnType (List.hd phi, ty))
     | None -> Fail (UnknownStruct (fst ty, name)))
  | (IndexProj idx :: phi_prime, Struct (name, provs, tys)) ->
    (match global_env_find_struct sigma name with
     | Some (Tup (_, _, dfn_provs, tyvars, dfn_tys)) ->
       (match List.nth_opt dfn_tys idx with
        | Some ty ->
          let new_ty = subst_many (subst_many_prov ty (List.combine provs dfn_provs))
                                  (List.combine tys tyvars)
          in compute_ty sigma phi_prime new_ty
        | None -> Fail (InvalidOperationOnType (List.hd phi, ty)))
     | Some (Rec _) -> Fail (InvalidOperationOnType (List.hd phi, ty))
     | None -> Fail (UnknownStruct (fst ty, name)))
  | (IndexProj idx :: phi_prime, Tup tys) ->
    (match List.nth_opt tys idx with
     | Some ty -> compute_ty sigma phi_prime ty
     | None -> Fail (InvalidOperationOnType (List.hd phi, ty)))
  | (_, _) -> Fail (InvalidOperationOnType (List.hd phi, ty))

(* evaluates the place expression down to a collection of possible places *)
let rec eval_place_expr (loc : source_loc) (ell : loan_env) (gamma : place_env)
    (omega : owned) (pi : place_expr) : loans tc =
  match pi with
  | Var var -> Succ [(omega, Var var)]
  | Deref pi ->
    let* loans = eval_place_expr loc ell gamma omega pi
    in let work (acc : loans tc) (loan : loan) : loans tc =
         let* loans = acc
         in match place_env_lookup_speco gamma (snd loan) with
         | Some (ref_loc, Ref (prov, rfomega, ty)) ->
           if is_at_least omega rfomega then
              match loan_env_lookup_opt ell prov with
              | Some new_loans -> Succ (List.append loans new_loans)
              | None ->
                if loan_env_is_abs ell prov then Succ []
                else Fail (InvalidProv prov)
          else Fail (PermissionErr (loc, (omega, Deref pi), (ref_loc, Ref (prov, rfomega, ty))))
         | Some found -> Fail (TypeMismatchRef found)
         | None ->
            match place_env_lookup_opt gamma (Var (root_of pi)) with
            | Some ty ->
              let* _ = compute_ty empty_sigma (to_parts pi) ty
              in Succ []
            | None -> Fail (UnboundPlaceExpr (loc, snd loan))
    in List.fold_left work (Succ []) loans
  | FieldProj (pi, field) ->
    let to_proj (loan : loan) : loan = (fst loan, FieldProj (snd loan, field))
    in let* loans = eval_place_expr loc ell gamma omega pi
    in Succ (List.map to_proj loans)
  | IndexProj (pi, idx) ->
    let to_proj (loan : loan) : loan = (fst loan, IndexProj (snd loan, idx))
    in let* loans = eval_place_expr loc ell gamma omega pi
    in Succ (List.map to_proj loans)

let norm_place_expr (loc : source_loc) (ell : loan_env) (gamma : place_env)
    (phi : place_expr) : places tc =
  let rec norm (phi : place_expr) : places tc =
    let* loans = eval_place_expr loc ell gamma Shared phi
    in let progress = List.map (fun loan -> (place_expr_to_place (snd loan), snd loan)) loans
    in let still_to_norm =
         List.map (fun pair -> snd pair) (List.filter (fun pair -> fst pair = None) progress)
    in let complete =
         List.map (fun pair -> unwrap (fst pair)) (List.filter (fun pair -> fst pair != None) progress)
    in let continue (acc : places tc) (phi : place_expr) : places tc =
         let* completed = acc
         in let* newly_completed = norm phi
         in Succ (List.append completed newly_completed)
    in List.fold_left continue (Succ complete) still_to_norm
  in norm phi

(* this definition of disjoint essentially only works on places *)
let not_disjoint (pi : place_expr * place_expr) : bool =
  List.mem (fst pi) (all_subplaces (snd pi)) || List.mem (snd pi) (all_subplaces (fst pi))

(* given a gamma, determines whether it is safe to use pi according to omega *)
let is_safe (loc : source_loc) (ell : loan_env) (gamma : place_env)
    (omega : owned) (phi : place_expr) : loans option tc =
  let relevant (acc : loans tc) (loan : loan) : loans tc =
    let (_, phi_prime) = loan
    in let* acc = acc
    in let* pis = norm_place_expr loc ell gamma phi_prime
    in if List.for_all not_disjoint (List.map (fun pi -> (phi, place_to_place_expr pi)) pis) then
      Succ (List.cons loan acc)
    else Succ acc
  in match omega with
  | Unique -> (* for unique use to be safe, we need _no_ relevant loans *)
    let* res = List.fold_left relevant (Succ []) (find_loans Shared ell gamma phi)
    in (match res with
        | [] -> Succ None
        | loans -> Succ (Some loans))
  | Shared -> (* for shared use, we only care that there are no relevant _unique_ loans *)
    let* res = List.fold_left relevant (Succ []) (find_loans Unique ell gamma phi)
    in (match res with
        | [] -> Succ None
        | loans -> Succ (Some loans))

(* remove the whole set of identifiers rooted at the place pi from gamma *)
let place_env_subtract (sigma : global_env) (gamma : place_env) (pi : place) : place_env tc =
  let* gammaSub = places_typ sigma pi (place_env_lookup gamma pi)
  in let ids = List.map (fun (pi, _) -> pi) gammaSub
  in Succ (List.fold_left place_env_exclude gamma ids)

let rec contains_prov (gamma : place_env) (prov : prov) =
  let rec ty_contains (ty : ty) : bool =
    match snd ty with
    | Any | BaseTy _ | TyVar _ -> false
    | Ref (pv, _, ty) -> pv = prov || ty_contains ty
    | Fun (pvs, _, tys, gam, ret_ty) ->
      if not (List.mem prov pvs) then
        ty_contains ret_ty || tys_contains tys || contains_prov gam prov
      else false
    | Array (ty, _) | Slice ty -> ty_contains ty
    | Tup tys -> tys_contains tys
    | Struct (_, pvs, _) -> List.mem prov pvs
  and tys_contains (tys : ty list) : bool =
    List.exists ty_contains tys
  in List.exists (fun pair -> ty_contains (snd pair)) gamma

let envs_minus (sigma : global_env) (ell : loan_env) (gamma : place_env)
  (pi : place) : (loan_env * place_env) tc =
  let rec loop (ty : ty option) (pair : (loan_env * place_env) tc) : (loan_env * place_env) tc =
    match ty with
    | Some (_, Ref (prov, _, ty)) ->
      let* (ell, gamma) = loop (Some ty) pair
      in let* new_gamma = place_env_subtract sigma gamma pi
      in if not (contains_prov new_gamma prov) then Succ (loan_env_exclude ell prov, new_gamma)
      else Succ (ell, new_gamma)
    | Some (_, Any) | Some (_, BaseTy _) | Some (_, TyVar _) | Some (_, Fun _)
    | Some (_, Struct _) -> pair
    | Some (_, Array (ty, _)) | Some (_, Slice ty) -> loop (Some ty) pair
    | Some (_, Tup tys) -> loops tys pair
    | None -> Succ (ell, gamma)
  and loops (tys : ty list) (pair : (loan_env * place_env) tc) =
    List.fold_right loop (List.map (fun x -> Some x) tys) pair
  in loop (place_env_lookup_opt gamma pi) (Succ (ell, gamma))


let rec prefixed_by (target : place) (in_pi : place) : bool =
  if target = in_pi then true
  else match in_pi with
  | Var _ -> false
  | FieldProj (piPrime, _) -> prefixed_by target piPrime
  | IndexProj (piPrime, _) -> prefixed_by target piPrime

let rec replace (prefix : place) (new_pi : place)  (in_pi : place) : place =
  if prefix = in_pi then new_pi
  else match in_pi with
  | Var x -> Var x
  | FieldProj (piPrime, field) -> FieldProj (replace prefix new_pi piPrime, field)
  | IndexProj (piPrime, idx) -> IndexProj (replace prefix new_pi piPrime, idx)

(* given a root place pi, compute all the places and shapes based on v *)
let rec places_val (sigma : store) (pi : place) (v : value) : (place * shape) list =
  match v with
  | Prim p -> [(pi, Prim p)]
  | Ptr (omega, piPrime) -> [(pi, Ptr (omega, piPrime))]
  | Fun (provvars, tyvars, params, body) -> [(pi, Fun (provvars, tyvars, params, body))]
  | Tup values ->
    let work (acc : (place * shape) list) (pair : place * value) =
      let (pi, v) = pair
      in List.concat [acc; places_val sigma pi v]
    in let func (idx : int) (v : value) =
      let piPrime : place = IndexProj  (pi, idx)
      in (piPrime, v)
    in let projs = List.mapi func values
    in List.fold_left work [(pi, Tup (List.map (fun _ -> ()) values))] projs
  | Array values -> [(pi, Array values)]

(* given a store sigma, compute the value at pi from its shape in sigma *)
let rec value (sigma : store) (pi : place) : value =
  match List.assoc pi sigma with
  | Hole -> value sigma pi
  | Prim p -> Prim p
  | Ptr (omega, pi) -> Ptr (omega, pi)
  | Fun (provvars, tyvars, params, body) -> Fun (provvars, tyvars, params, body)
  | Tup boxes ->
    let values = List.mapi (fun idx -> fun () -> value sigma (IndexProj (pi, idx))) boxes
    in Tup values
  | Array values -> Array values

let rec noncopyable (sigma : global_env) (typ : ty) : bool tc =
  match snd typ with
  | Any -> Succ false
  | BaseTy _ -> Succ false
  | TyVar _ -> Succ true
  | Ref (_, Unique, _) -> Succ true
  | Ref (_, Shared, typPrime) -> noncopyable sigma typPrime
  | Fun (_, _, _, _, _) -> Succ false
  | Array (typPrime, _) -> noncopyable sigma typPrime
  | Slice typPrime -> noncopyable sigma typPrime
  | Tup typs ->
    let work (acc : bool tc) (typ : ty) : bool tc =
      let* res = acc
      in let* ty_noncopyable = noncopyable sigma typ
      in Succ (res || ty_noncopyable)
    in List.fold_left work (Succ false) typs
  | Struct (name, _, _) ->
    match  global_env_find_struct sigma name with
    | Some (Rec (copyable, _, _, _, _)) | Some (Tup (copyable, _, _, _, _)) -> Succ (not copyable)
    | None -> Fail (UnknownStruct (fst typ, name))

let copyable (sigma : global_env) (typ : ty) : bool tc =
  let* res = noncopyable sigma typ
  in Succ (not res)

let valid_copy_impl (sigma : global_env) (def : struct_def) : unit tc =
  match def with
  | Rec (true, name, _, _, fields) ->
    let work (acc : (ty option) tc) (typ : ty) : (ty option) tc =
      let* res = acc
      in let* ty_copyable = copyable sigma typ
      in if (res == None) then
        if ty_copyable then Succ None
        else acc
      else Succ (Some typ)
    in (match List.fold_left work (Succ None) (List.map snd fields) with
    | Succ None -> Succ ()
    | Succ (Some ty) -> Fail (InvalidCopyImpl (name, ty))
    | Fail err -> Fail err)
  | Tup (true, name, _, _, tys) ->
    let work (acc : (ty option) tc) (typ : ty) : (ty option) tc =
      let* res = acc
      in let* ty_copyable = copyable sigma typ
      in if (res == None) then
        if ty_copyable then Succ None
        else acc
      else Succ (Some typ)
    in (match List.fold_left work (Succ None) tys with
    | Succ None -> Succ ()
    | Succ (Some ty) -> Fail (InvalidCopyImpl (name, ty))
    | Fail err -> Fail err)
  | Rec (false, _, _, _, _) | Tup (false, _, _, _, _) -> Succ ()
