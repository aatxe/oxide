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
  match loan_env_lookup_opt ell prov with
  | Some loans -> loans
  | None -> []

(* substitutes this for that in ty *)
let subst_prov (ty : ty) (this : prov) (that : prov) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ | TyVar _ -> ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (pv, omega, ty) ->
      let prov = if (snd pv) = (snd that) then this else pv
      in (loc, Ref (prov, omega, sub ty))
    | Fun (pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that pvs) then (loc, Fun (pvs, tvs, sub_many tys, gamma, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      let work (pv : prov) (provs : provs) =
        List.cons (if (snd pv) = (snd that) then this else pv) provs
      in let new_provs = List.fold_right work provs []
      in (loc, Struct (name, new_provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many_prov (ty : ty) (pairs : (prov * prov) list) : ty =
  List.fold_right (fun pair ty -> subst_prov ty (fst pair) (snd pair)) pairs ty

let subst (ty : ty) (this : ty)  (that : ty_var) : ty =
  let rec sub (ty : ty) : ty =
    let loc = fst ty
    in match snd ty with
    | Any | BaseTy _ -> ty
    | TyVar tv -> if tv = that then this else ty
    | Uninit ty -> (loc, Uninit (sub ty))
    | Ref (pv, omega, ty) -> (loc, Ref (pv, omega, sub ty))
    | Fun (pvs, tvs, tys, gamma, ret_ty) ->
      if not (List.mem that tvs) then (loc, Fun (pvs, tvs, sub_many tys, gamma, sub ret_ty))
      else ty
    | Array (ty, n) -> (loc, Array (sub ty, n))
    | Slice ty -> (loc, Slice (sub ty))
    | Rec pairs -> (loc, Rec (sub_many_pairs pairs))
    | Tup tys -> (loc, Tup (sub_many tys))
    | Struct (name, provs, tys, tagged_ty) ->
      (loc, Struct (name, provs, sub_many tys, sub_opt tagged_ty))
  and sub_many (tys : ty list) : ty list = List.map sub tys
  and sub_many_pairs (pairs : (field * ty) list) : (field * ty) list =
    List.map (fun (f, ty) -> (f, sub ty)) pairs
  and sub_opt (ty : ty option) : ty option = Option.map sub ty
  in sub ty

let subst_many (ty : ty) (pairs : (ty * ty_var) list) : ty =
  List.fold_right (fun pair ty -> subst ty (fst pair) (snd pair)) pairs ty

(* use the path to decompose a type into a context and an inner type *)
let rec decompose (ty : ty) (path : path) : (ty_ctx * ty) tc =
  let (loc, ty) = ty
  in match (ty, path) with
  | (ty, []) -> Succ ((inferred, Hole), (loc, ty))
  | (Rec pairs, (Field f) :: path) ->
    let* (inner_ctx, ty) = decompose (List.assoc f pairs) path
    in let replace (pair : field * ty) : field * ty_ctx =
      if fst pair = f then (f, inner_ctx) else (fst pair, (fst ty, Ty ty))
    in let ctx : ty_ctx = (loc, Rec (List.map replace pairs))
    in Succ (ctx, ty)
  | (Tup tys, (Index n) :: path) ->
    let* (inner_ctx, ty) = decompose (List.nth tys n) path
    in let replace (idx : int) (ty : ty) : ty_ctx = if idx = n then inner_ctx else (fst ty, Ty ty)
    in let ctx : ty_ctx = (loc, Tup (List.mapi replace tys))
    in Succ (ctx, ty)
  | (Struct (_, _, _, Some ty), path) -> decompose ty path
  | (ty, path) -> Fail (InvalidOperationOnType (path, (loc, ty)))

(* find the type of the expr path based on the original type in a context *)
(* this will error if the context doesn't allow the operation,
   e.g. dereferencing a shared reference in a unique context *)
let rec compute_ty_in (ctx : owned) (ty : ty) (path : expr_path) : ty tc =
  let (loc, ty) = ty
  in match (ty, path) with
  | (ty, []) -> Succ (loc, ty)
  | (Ref (_, omega, ty), Deref :: path) ->
    if is_at_least ctx omega then compute_ty_in ctx ty path
    else Fail (PermissionErr (ty, path, ctx))
  | (Rec pairs, (Field f) :: path) -> compute_ty_in ctx (List.assoc f pairs) path
  | (Tup tys, (Index n) :: path) -> compute_ty_in ctx (List.nth tys n) path
  | (Struct (_, _, _, Some ty), path) -> compute_ty_in ctx ty path
  | (ty, path) -> Fail (InvalidOperationOnTypeEP (path, (loc, ty)))

(* find the type of the expr path based on the original type, assuming a shared use context*)
let compute_ty (ty : ty) (path : expr_path) : ty tc =  compute_ty_in Shared ty path

let rec plug (fill : ty) (ctx : ty_ctx) : ty =
  let (loc, ctx) = ctx
  in match ctx with
  | Hole -> fill
  | Ty ty -> ty
  | Tagged (tag, provs, tys, ctx) -> (loc, Struct (tag, provs, tys, Some (plug fill ctx)))
  | Rec pair -> (loc, Rec (List.map (fun (f, ctx) -> (f, plug fill ctx)) pair))
  | Tup ctx -> (loc, Tup (List.map (plug fill) ctx))

(* var env operations *)

let var_env_lookup (gamma : var_env) (pi : place) : ty tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty ->
    let* (_, ty) = decompose ty path
    in Succ ty
  | None -> Fail (UnboundPlace pi)
let var_env_lookup_many (gamma : var_env) (pis : place list) : ty list tc =
  let lookup_seq (pi : place) (acc : ty list tc) : ty list tc =
    let* tys = acc
    in let* ty = var_env_lookup gamma pi
    in Succ (List.cons ty tys)
  in List.fold_right lookup_seq pis (Succ [])
let var_env_lookup_opt (gamma : var_env) (pi : place) : (ty option) tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some ty ->
    let* (_, ty) = decompose ty path
    in Succ (Some ty)
  | None -> Succ None
let var_env_lookup_place_expr (gamma : var_env) (pi : place_expr) : ty tc =
  match place_expr_to_place pi with
  | Some pi -> var_env_lookup gamma pi
  | None -> Fail (PlaceExprNotAPlace pi)
let var_env_contains_place_expr (gamma : var_env) (pi : place_expr) : bool =
  match place_expr_to_place pi with
  | Some (_, (root, _)) ->
    (match List.assoc_opt root gamma with
    | Some _ -> true
    | None -> false)
  | None -> false

let var_env_type_update (gamma : var_env) (pi : place) (ty : ty) : var_env tc =
  let (root, path) = snd pi
  in match List.assoc_opt root gamma with
  | Some root_ty ->
    let* (ctx, _) = decompose root_ty path
    in Succ (replace_assoc gamma root (plug ty ctx))
  | None -> Fail (UnboundPlace pi)

let var_env_uninit_many (gamma : var_env) (vars : var list) : var_env =
  let work (entry : var * ty) : var * ty =
    if List.mem (fst entry) vars then (fst entry, (inferred, Uninit (snd entry))) else entry
  in List.map work gamma

let var_env_include (gamma : var_env) (x : var) (typ : ty) = List.cons (x, typ) gamma
let var_env_append (gamma1 : var_env) (gamma2 : var_env) = List.append gamma1 gamma2
let var_env_exclude (gamma : var_env) (x : var) = List.remove_assoc x gamma

(* compute all the at-least-omega loans in a given gamma *)
let rec all_loans (omega : owned) (ell : loan_env) (gamma : var_env) : loans =
  let rec work (typ : ty) (loans : loans) : loans =
    match snd typ with
    | Any | BaseTy _ | TyVar _ -> loans
    | Ref (prov, omega_prime, typ) ->
      if is_at_least omega omega_prime then List.append (prov_to_loans ell prov) (work typ loans)
      else work typ loans
    | Fun (_, _, _, gamma_c, _) -> List.append loans (all_loans omega ell gamma_c)
    | Uninit typ | Array (typ, _) | Slice typ -> work typ loans
    | Rec pairs -> List.fold_right List.append (List.map (fun pr -> work (snd pr) []) pairs) loans
    | Tup typs -> List.fold_right List.append (List.map (fun typ -> work typ []) typs) loans
    | Struct (_, provs, _, _) ->  List.concat (loans :: List.map (prov_to_loans ell) provs)
  in List.fold_right (fun entry -> work (snd entry)) gamma []

(* find the root of a given place expr *)
let root_of (pi : place_expr) : var = sndfst pi

(* find all at-least-omega loans in gamma that have to do with pi *)
let find_loans (omega : owned) (ell : loan_env) (gamma : var_env) (pi : place_expr) : loans =
  (* n.b. this is actually too permissive because of reborrowing and deref *)
  let root_of_pi = root_of pi
  in let relevant (loan : loan) : bool =
    (* a loan is relevant if it is a descendant of any subplace of pi *)
    let (_, pi_prime) = loan
       (* the easiest way to check is to check if their roots are the same *)
    in root_of_pi = root_of pi_prime
  in List.filter relevant (all_loans omega ell gamma)

(* evaluates the place expression down to a collection of possible places *)
let eval_place_expr (ell : loan_env) (gamma : var_env) (omega : owned) (pi : place_expr) : loans tc =
  let rec eval_place_expr (pi : place_expr) : loans tc =
    let (prefix, suffix) = partition ((!=) Deref) (sndsnd pi)
    in match suffix with
    | [] -> Succ [(omega, pi)]
    | Deref :: path ->
        let* ty = var_env_lookup gamma (fst pi, (sndfst pi, unwrap (expr_path_to_path prefix)))
        in (match snd ty with
        | Ref (prov, _, _) ->
          let loans = loan_env_lookup ell prov
          in let add_path_to_back (loan : loan) : place_expr =
            let (_, (loc, (root, loan_path))) = loan
            in (loc, (root, List.append loan_path path))
          in let current_loans = List.map add_path_to_back loans
          in let follow (pi : place_expr) (acc : loans tc) =
            let* loans_so_far = acc
            in let* new_loans = eval_place_expr pi
            in Succ (List.append loans_so_far new_loans)
          in List.fold_right follow current_loans (Succ [])
        | _ -> Fail (TypeMismatchRef ty))
    | _ :: _ -> failwith "unreachable"
  in eval_place_expr pi

let norm_place_expr (ell : loan_env) (gamma : var_env) (phi : place_expr) : places tc =
  let rec norm (phi : place_expr) : places tc =
    let* loans = eval_place_expr ell gamma Shared phi
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

let rec is_prefix_of (path1 : expr_path) (path2 : expr_path) : bool =
  match (path1, path2) with
  | (_, []) -> true
  | ([], _) -> false
  | (Field f1 :: path1, Field f2 :: path2) -> if f1 = f2 then is_prefix_of path1 path2 else false
  | (Index i1 :: path1, Index i2 :: path2) -> if i1 = i2 then is_prefix_of path1 path2 else false
  | (Deref :: path1, Deref :: path2) -> is_prefix_of path1 path2
  | (_, _) -> false

(* this definition of disjoint essentially only works on places *)
let not_disjoint (pi : place_expr * place_expr) : bool =
  let (pi1, pi2) = pi
  in if sndfst pi1 = sndfst pi2 then
    is_prefix_of (sndsnd pi1) (sndsnd pi2) || is_prefix_of (sndsnd pi2) (sndsnd pi1)
  else true

(* given a gamma, determines whether it is safe to use pi according to omega *)
let is_safe (ell : loan_env) (gamma : var_env) (omega : owned) (phi : place_expr) : loans option tc =
  let relevant (acc : loans tc) (loan : loan) : loans tc =
    let (_, phi_prime) = loan
    in let* acc = acc
    in let* pis = norm_place_expr ell gamma phi_prime
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

let rec contains_prov (gamma : var_env) (prov : prov) =
  let rec ty_contains (ty : ty) : bool =
    match snd ty with
    | Any | BaseTy _ | TyVar _ -> false
    | Ref (pv, _, ty) -> pv = prov || ty_contains ty
    | Fun (pvs, _, tys, gam, ret_ty) ->
      if not (List.mem prov pvs) then
        ty_contains ret_ty || tys_contains tys || contains_prov gam prov
      else false
    | Uninit ty | Array (ty, _) | Slice ty -> ty_contains ty
    | Rec pairs -> tys_contains (List.map snd pairs)
    | Tup tys -> tys_contains tys
    | Struct (_, pvs, _, _) -> List.mem prov pvs
  and tys_contains (tys : ty list) : bool =
    List.exists ty_contains tys
  in List.exists (fun pair -> ty_contains (snd pair)) gamma

let envs_minus (ell : loan_env) (gamma : var_env) (pi : place) : (loan_env * var_env) tc =
  let rec loop (ty : ty option) (pair : (loan_env * var_env) tc) : (loan_env * var_env) tc =
    match ty with
    | Some (_, Ref (prov, _, ty)) ->
      let* (ell, gamma) = loop (Some ty) pair
      in let new_gamma = var_env_exclude gamma (sndfst pi)
      in if not (contains_prov new_gamma prov) then Succ (loan_env_exclude ell prov, new_gamma)
      else Succ (ell, new_gamma)
    | Some (_, Any) | Some (_, BaseTy _) | Some (_, TyVar _) | Some (_, Fun _)
    | Some (_, Struct _) -> pair
    | Some (_, Uninit ty) | Some (_, Array (ty, _)) | Some (_, Slice ty) -> loop (Some ty) pair
    | Some (_, Rec pairs) -> loops (List.map snd pairs) pair
    | Some (_, Tup tys) -> loops tys pair
    | None -> Succ (ell, gamma)
  and loops (tys : ty list) (pair : (loan_env * var_env) tc) =
    List.fold_right loop (List.map (fun x -> Some x) tys) pair
  in let* opt = var_env_lookup_opt gamma pi
  in loop opt (Succ (ell, gamma))

let rec path_prefixed_by (target : path) (in_path : path) : bool =
  match (target, in_path) with
  | ([], _) -> true
  | (_, []) -> false
  | (x :: target, y :: in_path) -> x = y && path_prefixed_by target in_path

let prefixed_by (target : place) (in_pi : place) : bool =
  let (target, in_pi) = (snd target, snd in_pi)
  in fst target = fst in_pi && path_prefixed_by (snd target) (snd in_pi)

let rec noncopyable (sigma : global_env) (typ : ty) : bool tc =
  match snd typ with
  | Any -> Succ false
  | BaseTy _ -> Succ false
  | TyVar _ -> Succ true
  | Uninit _ -> Succ false (* probably never ask this question anyway *)
  | Ref (_, Unique, _) -> Succ true
  | Ref (_, Shared, _) -> Succ false
  | Fun (_, _, _, _, _) -> Succ false
  | Array (typPrime, _) -> noncopyable sigma typPrime
  | Slice typPrime -> noncopyable sigma typPrime
  | Rec pairs ->
    let work (acc : bool tc) (pair : field * ty) : bool tc =
      let* res = acc
      in let* ty_noncopyable = noncopyable sigma (snd pair)
      in Succ (res || ty_noncopyable)
    in List.fold_left work (Succ false) pairs
  | Tup typs ->
    let work (acc : bool tc) (typ : ty) : bool tc =
      let* res = acc
      in let* ty_noncopyable = noncopyable sigma typ
      in Succ (res || ty_noncopyable)
    in List.fold_left work (Succ false) typs
  | Struct (name, _, _, _) ->
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

let rec free_provs_ty (ty : ty) : provs =
  match snd ty with
  | Any | BaseTy _ | TyVar _ -> []
  | Uninit ty -> free_provs_ty ty
  | Ref (prov, _, ty) -> List.cons prov (free_provs_ty ty)
  | Fun _ -> [] (* FIXME: actually implement *)
  | Array (ty, _) | Slice ty -> free_provs_ty ty
  | Rec tys -> List.flatten (List.map (fun pair -> free_provs_ty (snd pair)) tys)
  | Tup tys -> List.flatten (List.map free_provs_ty tys)
  | Struct (_, provs, tys, _) -> List.flatten (List.cons provs (List.map free_provs_ty tys))
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
  | RecStruct (_, provs, _, es) ->
    List.flatten (provs :: List.map (fun x -> free_provs (snd x)) es)
  | TupStruct (_, provs, _, es) -> List.flatten (provs :: List.map free_provs es)

let free_vars_helper (expr : expr) (should_include : var -> bool tc) : var list tc =
   let rec free (expr : expr) : var list tc =
     match snd expr with
     | Prim _ | Fn _ | Abort _ -> Succ []
     | BinOp (_, e1, e2)
     | While (e1, e2)
     | Seq (e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in Succ (List.append free1 free2)
     | Move (_, (root, _))
     | Borrow (_, _, (_, (root, _)))
     | Ptr (_, (_, (root, _))) ->
       let* should_include = should_include root
       in if should_include then Succ [root] else Succ []
     | BorrowIdx (_, _, (_, (root, _)), e1)
     | Idx ((_, (root, _)), e1)
     | Assign ((_, (root, _)), e1) ->
       let* free1 = free e1
       in Succ (List.cons root free1)
     | BorrowSlice (_, _, (_, (root, _)), e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in let* should_include = should_include root
       in Succ (List.concat [if should_include then [root] else []; free1; free2])
     | LetProv (_, e) -> free e
     | Let (x, _, e1, e2)
     | For (x, e1, e2) ->
       let* free1 = free e1
       in let* free2 = free e2
       in Succ (List.append free1 (List.filter ((!=) x) free2))
     | Fun _ -> Succ [] (* FIXME: actually implement *)
     | App (e1, _, _, exprs) ->
       let* frees = free_many exprs
       in let* free1 = free e1
       in Succ (List.append free1 frees)
     | Branch (e1, e2, e3) ->
       let* free1 = free e1
       in let* free2 = free e2
       in let* free3 = free e3
       in Succ (List.concat [free1; free2; free3])
     | Tup exprs | Array exprs -> free_many exprs
     | RecStruct _ | TupStruct _ -> Succ [] (* FIXME: implement *)
   and free_many (exprs : expr list) : var list tc =
     let work (expr : expr) (acc : var list tc) : var list tc =
       let* free_so_far = acc
       in let* free = free expr
       in Succ (List.append free free_so_far)
     in List.fold_right work exprs (Succ [])
   in free expr

let free_nc_vars (sigma : global_env) (gamma : var_env) (expr : expr) =
  free_vars_helper expr (fun var -> noncopyable sigma (List.assoc var gamma))

let free_vars (expr : expr) = free_vars_helper expr (fun _ -> Succ true)

let free_provs_var_env (gamma : var_env) : provs =
  List.flatten (List.map (fun x -> free_provs_ty (snd x)) gamma)
