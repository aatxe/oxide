open Syntax

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
  match prov with
  | ProvVar var -> loan_env_lookup ell var
  | ProvSet lns -> lns

(* given a root identier x, compute all the places based on tau *)
let rec places_typ (pi : place) (tau : ty) : (place * ty) list =
  match tau with
  | Any -> [(pi, tau)]
  | BaseTy _ -> [(pi, tau)]
  | TyVar _ -> [(pi, tau)]
  | Ref (_, _, _) -> [(pi, tau)]
  | Fun (_, _, _, _, _) -> [(pi, tau)]
  | Array(_, _) -> [(pi, tau)]
  | Slice(_)  -> [(pi, tau)]
  | Tup(tys) ->
    let work (acc : (place * ty) list) (pair : place * ty) =
      let (pi, ty) = pair
      in List.concat [acc; places_typ pi ty]
    in let func (idx : int) (typ : ty) =
         let piPrime : place = IndexProj  (pi, idx)
         in (piPrime, typ)
    in let projs = List.mapi func tys
    in List.fold_left work [(pi, tau)] projs

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
let place_env_include (gamma : place_env) (x : place) (typ : ty) =
  let ext = places_typ x typ
  in List.append ext gamma
let place_env_append (gamma1 : place_env) (gamma2 : place_env) = List.append gamma1 gamma2
let place_env_exclude (gamma : place_env) (x : place) = List.remove_assoc x gamma

(* compute all the at-least-omega loans in a given gamma *)
let all_loans (omega : owned) (ell : loan_env) (gamma : place_env) : loans =
  let rec work (typ : ty) (loans : loans) : loans =
    match typ with
    | Any -> loans
    | BaseTy _ -> loans
    | TyVar _ -> loans
    | Ref (var, omega_prime, typ) ->
      if is_at_least omega omega_prime then List.append (prov_to_loans ell (ProvVar var)) (work typ loans)
      else work typ loans
    | Fun (_, _, _, _, _) -> loans
    | Array (typ, _) -> work typ loans
    | Slice typ -> work typ loans
    | Tup typs -> List.fold_right List.append (List.map (fun typ -> work typ []) typs) loans
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

(* given a gamma, determines whether it is safe to use pi according to omega *)
let is_safe (ell : loan_env) (gamma : place_env) (omega : owned) (pi : place_expr) : loans option =
  let subplaces_of_pi = all_subplaces pi
  in let relevant (loan : loan) : bool =
    (* a loan is relevant if it is for either a subplace or an ancestor of pi *)
    let (_, pi_prime) = loan
        (* either pi is an ancestor of pi_prime *)
    in List.exists (fun x -> root_of x = root_of pi) (all_subplaces pi_prime)
        (* or pi_prime is a subplace of pi *)
        || List.mem pi_prime subplaces_of_pi
  in match omega with
  | Unique -> (* for unique use to be safe, we need _no_ relevant loans *)
    (match List.filter relevant (find_loans Shared ell gamma pi) with
    | [] -> None
    | loans -> Some loans)
  | Shared -> (* for shared use, we only care that there are no relevant _unique_ loans *)
    (match List.filter relevant (find_loans Unique ell gamma pi) with
    | [] -> None
    | loans -> Some loans)

(* evaluates the place expression down to a collection of possible places *)
let rec eval_place_expr (loc : source_loc) (ell : loan_env) (gamma : place_env)
    (omega : owned) (pi : place_expr) : loans tc =
  match pi with
  | Var var -> Succ [(omega, Var var)]
  | Deref pi ->
    (match eval_place_expr loc ell gamma omega pi with
    | Succ loans ->
      let work (acc : loans tc) (loan : loan) : loans tc =
        match acc with
        | Fail err -> Fail err
        | Succ loans ->
          match place_env_lookup_speco gamma (snd loan) with
          | Some (Ref (prov, _, _)) ->
            (match loan_env_lookup_opt ell prov with
             | Some new_loans -> Succ (List.append loans new_loans)
             | None -> Fail (InvalidProv (loc, ProvVar prov)))
          | Some found -> Fail (TypeMismatchRef (loc, found))
          | None -> Fail (UnboundPlaceExpr (loc, snd loan))
      in List.fold_left work (Succ []) loans
    | Fail err -> Fail err)
  | FieldProj (pi, field) ->
    let to_proj (loan : loan) : loan = (fst loan, FieldProj (snd loan, field))
    in (match eval_place_expr loc ell gamma omega pi with
     | Succ loans -> Succ (List.map to_proj loans)
     | Fail err -> Fail err)
  | IndexProj (pi, idx) ->
    let to_proj (loan : loan) : loan = (fst loan, IndexProj (snd loan, idx))
    in (match eval_place_expr loc ell gamma omega pi with
        | Succ loans -> Succ (List.map to_proj loans)
        | Fail err -> Fail err)

(* remove the whole set of identifiers rooted at the place pi from gamma *)
let place_env_subtract (gamma : place_env) (pi : place) : place_env =
  let gammaSub = places_typ pi (place_env_lookup gamma pi)
  in let ids = List.map (fun (pi, _) -> pi) gammaSub
  in List.fold_left place_env_exclude gamma ids

let rec contains_prov (gamma : place_env) (prov : prov_var) =
  let rec ty_contains (ty : ty) : bool =
    match ty with
    | Any | BaseTy _ | TyVar _ -> false
    | Ref (pv, _, ty) -> pv = prov || ty_contains ty
    | Fun (pvs, _, tys, gam, ret_ty) ->
      if not (List.mem prov pvs) then
        ty_contains ret_ty || tys_contains tys || contains_prov gam prov
      else false
    | Array (ty, _) | Slice ty -> ty_contains ty
    | Tup tys -> tys_contains tys
  and tys_contains (tys : ty list) : bool =
    List.exists ty_contains tys
  in List.exists (fun pair -> ty_contains (snd pair)) gamma

let envs_minus (ell : loan_env) (gamma : place_env) (pi : place) : loan_env * place_env =
  let rec loop (ty : ty option) (pair : loan_env * place_env) =
    match ty with
    | Some (Ref (prov, _, ty)) ->
      let (ell, gamma) = loop (Some ty) pair
      in let new_gamma = place_env_subtract gamma pi
      in if not (contains_prov new_gamma prov) then (loan_env_exclude ell prov, new_gamma)
      else (ell, new_gamma)
    | Some Any | Some (BaseTy _) | Some (TyVar _) | Some (Fun _) -> pair
    | Some (Array (ty, _)) | Some (Slice ty) -> loop (Some ty) pair
    | Some (Tup tys) -> loops tys pair
    | None -> (ell, gamma)
  and loops (tys : ty list) (pair : loan_env * place_env) =
    List.fold_right loop (List.map (fun x -> Some x) tys) pair
  in loop (place_env_lookup_opt gamma pi) (ell, gamma)


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

let rec noncopyable (typ : ty) : bool =
  match typ with
  | Any -> false
  | BaseTy _ -> false
  | TyVar _ -> true
  | Ref (_, Unique, _) -> true
  | Ref (_, Shared, typPrime) -> noncopyable typPrime
  | Fun (_, _, _, _, _) -> false
  | Array (typPrime, _) -> noncopyable typPrime
  | Slice typPrime -> noncopyable typPrime
  | Tup typs -> List.for_all noncopyable typs

let copyable (typ : ty) : bool = not (noncopyable typ)
