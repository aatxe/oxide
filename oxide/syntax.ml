open Util

type linecol = int * int [@@deriving show]
type source_loc = string * linecol * linecol [@@deriving show]
let inferred : source_loc = ("<inferred>", (-1, -1), (-1, -1))
let dummy : source_loc = ("<dummy>", (-1, -1), (-1, -1))
type var = string [@@deriving show]
type vars = var list [@@deriving show]
type ty_var = string [@@deriving show]
type fn_var = string [@@deriving show]
type prov_var = string [@@deriving show]
type struct_var = string [@@deriving show]
type field = string [@@deriving show]

type subtype_modality = Combine | Override [@@deriving show]
type owned = Shared | Unique [@@deriving show]

type env_var = owned * string [@@deriving show]
type env_vars = env_var list [@@deriving show]

type path_entry =
  | Field of field
  | Index of int
[@@deriving show]
type path = path_entry list [@@deriving show]
type preplace = var * path [@@deriving show]
type place = source_loc * preplace [@@deriving show]
type places = place list [@@deriving show]
type expr_path_entry =
  | Field of field
  | Index of int
  | Deref
[@@deriving show]
type expr_path = expr_path_entry list [@@deriving show]
type preplace_expr = var * expr_path [@@deriving show]
type place_expr = source_loc * preplace_expr [@@deriving show]

let path_entry_to_expr_path_entry (entry : path_entry) : expr_path_entry =
  match entry with
  | Field f -> Field f
  | Index i -> Index i

let path_to_expr_path (path : path) : expr_path = List.map path_entry_to_expr_path_entry path

let place_to_place_expr (pi : place) : place_expr =
  let (root, path) = snd pi
  in (fst pi, (root, path_to_expr_path path))

let expr_path_entry_to_path_entry (entry : expr_path_entry) : path_entry option =
  match entry with
  | Field f -> Some (Field f)
  | Index i -> Some (Index i)
  | Deref -> None

let expr_path_to_path (path : expr_path) : path option =
  let work (entry : expr_path_entry) (acc : path option) : path option =
    match acc with
    | Some path ->
      (match expr_path_entry_to_path_entry entry with
       | Some entry -> Some (List.cons entry path)
       | None -> None)
    | None -> None
  in List.fold_right work path (Some [])

let place_expr_to_place (pi : place_expr) : place option =
  let (root, path) = snd pi
  in match expr_path_to_path path with
  | Some path -> Some (fst pi, (root, path))
  | None -> None

(* returns true if the place expression doesn't contain any dereferencing *)
let place_expr_is_place (pi : place_expr) : bool = not (List.mem Deref (sndsnd pi))

type loan = owned * place_expr [@@deriving show]
type loans = loan list [@@deriving show]
type prov = source_loc * prov_var [@@deriving show]
type provs = prov list [@@deriving show]
type bound = prov * prov [@@deriving show]
type bounds = bound list [@@deriving show]

type kind = Star | Prov [@@deriving show]
type base_ty = Bool | U32 | Unit [@@deriving show]
type prety =
  | Any
  | Infer (* infer this type! *)
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of prov * owned * ty
  | Fun of env_vars * provs * ty_var list * ty list * env * ty
  | Array of ty * int
  | Slice of ty
  | Rec of (field * ty) list
  | Tup of ty list
  | Struct of struct_var * prov list * ty list * ty option
  | Uninit of ty
[@@deriving show]
and ty = source_loc * prety [@@deriving show]
and env =
  | Unboxed (* a dummy environment for function pointers, not closures *)
  | EnvVar of env_var (* a quantified environment variable *)
  | Env of var_env (* a concrete environment *)
  | EnvOf of var (* the environment of a specific bound function at closure type *)
[@@deriving show]
and var_env = (var * ty) list [@@deriving show]

type tys = ty list [@@deriving show]

(* invariant: a type context should only ever include one hole *)
type prety_ctx =
  | Hole
  | Ty of ty
  | Tagged of struct_var * prov list * ty list * ty_ctx
  | Rec of (field * ty_ctx) list
  | Tup of ty_ctx list
[@@deriving show]
and ty_ctx = source_loc * prety_ctx [@@deriving show]

(* type distinguishers: these exist to prevent the need for syntactic stratification *)

(* is the given type a sized type? *)
let is_sized (typ : ty) : bool =
  match snd typ with
  | Slice _ -> false
  | _ -> true

(* is the given type fully initialized? *)
let rec is_init (typ : ty) : bool =
  match snd typ with
  | Any | Infer | BaseTy _ | TyVar _ -> true
  | Ref (_, _, ty) -> is_init ty (* invariant: this should always be true *)
  | Fun (_, _, _, tys, gamma, ty) ->
    all_init tys && var_env_init gamma && is_init ty
  | Array (ty, _) | Slice ty -> is_init ty
  | Rec fields -> all_init (List.map snd fields)
  | Tup tys -> all_init tys
  | Struct (_, _, tys, Some ty) -> all_init tys && is_init ty
  | Struct (_, _, tys, None) -> all_init tys
  | Uninit _ -> false
and all_init (tys : ty list) : bool =
  List.fold_right (fun ty acc -> acc && is_init ty) tys true
and var_env_init (gamma : env) : bool =
  match gamma with
  | Unboxed | EnvVar _ -> true
  | Env gamma -> all_init (List.map snd gamma)
  | EnvOf _ -> true

type prim =
  | Unit
  | Num of int
  | True
  | False
[@@deriving show]

type binop =
  | Add (* addition *)
  | Sub (* subtraction *)
  | Mul (* multiplication *)
  | Div (* division *)
  | Rem (* remainder *)
  | And (* boolean and *)
  | Or (* boolean or *)
  | BitXor (* bitwise xor *)
  | BitAnd (* bitwise and *)
  | BitOr (* bitwise or *)
  | Shl (* shift left *)
  | Shr (* shift right *)
  | Eq (* equal *)
  | Lt (* less than *)
  | Le (* less than or equal to *)
  | Ne (* not equal *)
  | Ge (* greater than or equal to *)
  | Gt (* greater than *)
[@@deriving show]

(* output: (lhs * rhs * result) *)
let binop_to_types (op : binop) : ty option * ty option * ty =
  let u32 = (dummy, BaseTy U32)
  in let bool = (dummy, BaseTy Bool)
  in match op with
  | Add | Sub | Mul | Div | Rem
  | BitXor | BitAnd | BitOr | Shl | Shr -> (Some u32, Some u32, u32)
  | And | Or -> (Some bool, Some bool, bool)
  | Eq | Lt | Le | Ne | Ge | Gt -> (None, None, bool)

type preexpr =
  | Prim of prim
  | BinOp of binop * expr * expr
  | Move of place_expr
  | Drop of place_expr (* like move but _always_ drops, even if copyable, but errors if not a place *)
  | Borrow of prov * owned * place_expr
  | BorrowIdx of prov * owned * place_expr * expr
  | BorrowSlice of prov * owned * place_expr * expr * expr
  | LetProv of prov list * expr
  | Let of var * ty * expr * expr
  | Assign of place_expr * expr
  | Seq of expr * expr
  | Fn of fn_var
  | Fun of prov list * ty_var list * (var * ty) list * (ty option) * expr
  | App of expr * env list * prov list * ty list * expr list
  | Idx of place_expr * expr
  | Abort of string
  | Branch of expr * expr * expr
  | While of expr * expr
  | For of var * expr * expr
  | Tup of expr list
  | Array of expr list
  | RecStruct of struct_var * prov list * ty list * (field * expr) list
  | TupStruct of struct_var * prov list * ty list * expr list
  | Ptr of owned * place
and expr = source_loc * preexpr
[@@deriving show]

type value =
  | Dead
  | Prim of prim
  | Fun of prov list * ty_var list * (var * ty) list * expr
  | Tup of value list
  | Array of value list
  | Ptr of owned * place
[@@deriving show]

type store = (var * value) list [@@deriving show]

(* name * env vars * prov vars * type vars * parameters * return type * bounds * body *)
type fn_def = fn_var * env_vars * provs * ty_var list * (var * ty) list * ty * bounds * expr
[@@deriving show]
type rec_struct_def = bool * struct_var * prov list * ty_var list * (field * ty) list
[@@deriving show]
type tup_struct_def = bool * struct_var * prov list * ty_var list * ty list
[@@deriving show]
type struct_def =
  | Rec of rec_struct_def
  | Tup of tup_struct_def
[@@deriving show]
type global_entry =
  | FnDef of fn_def
  | RecStructDef of rec_struct_def
  | TupStructDef of tup_struct_def
[@@deriving show]

type global_env = global_entry list [@@deriving show]
let empty_sigma : global_env = []

let global_env_find_fn (sigma : global_env) (fn : fn_var) : fn_def option =
  let is_right_fn (entry : global_entry) : bool =
    match entry with
    | FnDef (fn_here, _, _, _, _, _, _, _) -> fn_here = fn
    (* we treat tuple structs as having defined a function to construct them *)
    | TupStructDef (_, fn_here, _, _, _) -> fn_here = fn
    | _ -> false
  in match List.find_opt is_right_fn sigma with
  | Some (FnDef defn) -> Some defn
  | _ -> None

let global_env_find_struct (sigma : global_env) (name : struct_var) : struct_def option =
  let is_right_struct (entry : global_entry) : bool =
    match entry with
    | RecStructDef (_, name_here, _, _, _) -> name_here = name
    | TupStructDef (_, name_here, _, _, _) -> name_here = name
    | _ -> false
  in match List.find_opt is_right_struct sigma with
  | Some (RecStructDef defn) -> Some (Rec defn)
  | Some (TupStructDef defn) -> Some (Tup defn)
  | _ -> None

type tyvar_env = env_vars * provs * ty_var list [@@deriving show]
let empty_delta : tyvar_env = ([], [], [])

let env_vars_of (delta : tyvar_env) : env_vars = match delta with (evs, _, _) -> evs
let provs_of (delta : tyvar_env) : provs = match delta with (_, provs, _) -> provs
let ty_vars_of (delta : tyvar_env) : ty_var list = match delta with (_, _, tyvars) -> tyvars

let tyvar_env_add_env_vars (evs : env_vars) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (curr_evs, provs, tyvars) -> (list_union curr_evs evs, provs, tyvars)
let tyvar_env_add_provs (provs : provs) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (evs, curr_provs, tyvars) -> (evs, list_union curr_provs provs, tyvars)
let tyvar_env_add_ty_vars (tyvars : ty_var list) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (evs, provs, curr_tyvars) -> (evs, provs, list_union curr_tyvars tyvars)

let tyvar_env_prov_mem (var : prov) (delta : tyvar_env) : bool = List.mem var (provs_of delta)
let tyvar_env_ty_mem (var : ty_var) (delta : tyvar_env) : bool = List.mem var (ty_vars_of delta)
let tyvar_env_env_var_mem (var : env_var) (delta : tyvar_env) : bool =
  List.mem var (env_vars_of delta)

type subty = prov_var * prov_var [@@deriving show]
type loan_env = (prov * loans) list * (prov list * subty list) [@@deriving show]
let empty_ell : loan_env = ([], ([], []))

let to_prov_var_keys (concrete : (prov * loans) list) : (prov_var * loans) list =
  List.map (fun ((_, prov), loans) -> (prov, loans)) concrete

let loan_env_mem (ell : loan_env) (var : prov) : bool =
  fst ell |> to_prov_var_keys |> List.mem_assoc (snd var)
let loan_env_lookup_opt (ell : loan_env) (var : prov) : loans option =
  fst ell |> to_prov_var_keys |> List.assoc_opt (snd var)
let loan_env_is_abs (ell : loan_env) (var : prov) : bool =
  sndfst ell |> List.map snd |> List.mem (snd var)
let loan_env_abs_sub (ell : loan_env) (v1 : prov) (v2 : prov) : bool =
  List.mem (snd v1, snd v2) (sndsnd ell) || (snd v1) = (snd v2)
let loan_env_lookup (ell : loan_env) (var : prov) : loans =
  if loan_env_is_abs ell var then []
  else fst ell |> to_prov_var_keys |> List.assoc (snd var)

let loan_env_eq (ell1: loan_env) (ell2: loan_env) : bool =
  let concrete_dom = List.map (snd >> fst) >> fst
  in let abs_names = List.map snd >> sndfst
  in let equal_loans (prov : prov) : bool =
    equal_unordered (loan_env_lookup ell1 prov) (loan_env_lookup ell2 prov)
  in let concrete_matches =
    equal_unordered (concrete_dom ell1) (concrete_dom ell2) &&
    ell1 |> fst |> List.map fst |> List.for_all equal_loans
  in let abstract_matches = equal_unordered (abs_names ell1) (abs_names ell2)
  in let binding_matches = equal_unordered (sndsnd ell1) (sndsnd ell2)
  in concrete_matches && abstract_matches && binding_matches

let loan_env_filter_dom (ell : loan_env) (provs : provs) : loan_env =
  let prov_vars = List.map snd provs
  in (fst ell |> List.filter (fun ((_, var), _) -> List.mem var prov_vars),
      (sndfst ell |> List.filter (fun (_, var) -> List.mem var prov_vars),
       sndsnd ell |> List.filter (fun (lhs, rhs) -> List.mem lhs prov_vars ||
                                                    List.mem rhs prov_vars)))

let loan_env_include (var : prov) (loans : loans) (ell : loan_env) : loan_env =
  (fst ell |> List.filter ((<>) (snd var) >> fstsnd) |> List.cons (var, loans),
   snd ell)
let loan_env_include_all (provs : provs) (loans : loans) (ell : loan_env) : loan_env =
  let entries = List.map (fun prov -> (prov, loans)) provs
  in (fst ell |> List.filter (fun (prov, _) -> provs |> List.map snd |> List.mem (snd prov) |> not)
              |> List.append entries,
      snd ell)

let loan_env_bind (ell : loan_env) (prov : prov) : loan_env =
  (fst ell, (sndfst ell |> List.cons prov, sndsnd ell))
let loan_env_bindall (ell : loan_env) (provs : prov list) : loan_env =
  (fst ell, (sndfst ell |> List.append provs, sndsnd ell))
let loan_env_append (ell1 : loan_env) (ell2 : loan_env) : loan_env =
  (List.append (fst ell1) (fst ell2),
   (List.append (sndfst ell1) (sndfst ell2), sndsnd ell2))

let loan_env_exclude (prov : prov) (ell : loan_env) : loan_env =
  (fst ell |> List.filter ((<>) (snd prov) >> fstsnd),
   (sndfst ell |> List.filter (fun v -> snd v <> snd prov),
    sndsnd ell |> List.filter (fun cs -> fst cs <> snd prov && snd cs <> snd prov)))
let loan_env_exclude_all (provs : provs) (ell : loan_env) : loan_env =
  let prov_vars = List.map snd provs
  in (fst ell |> List.filter (fun ((_, prov), _) -> prov_vars |> List.mem prov |> not),
   (sndfst ell |> List.filter (fun v -> prov_vars |> List.mem (snd v) |> not),
    sndsnd ell |> List.filter (fun (lhs, rhs) -> prov_vars |> List.mem lhs |> not &&
                                                 prov_vars |> List.mem rhs |> not)))

let canonize (ell : loan_env) : loan_env =
  (fst ell |> List.sort_uniq compare_keys,
   (sndfst ell |> List.sort_uniq compare_keys,
    sndsnd ell |> List.sort_uniq compare_keys))

(* var_env is mutually recursive with ty and as such, is defined above *)
let empty_gamma : var_env = []

(* useful for pretty-printing in ownership safety *)
type place_env = (place * ty) list [@@deriving show]

type struct_kind = Rec | Tup [@@deriving show]

type tc_error =
  | TypeMismatch of ty * ty (* expected * found *)
  | TypeMismatchIterable of ty (* found *)
  | TypeMismatchFunction of ty (* found *)
  | TypeMismatchRef of ty (* found *)
  | TypeMismatchArray of ty (* found *)
  | VarEnvMismatch of source_loc * var_env * var_env (* source_loc * expected * found *)
  | LoanEnvMismatch of source_loc * loan_env * loan_env (* source_loc * expected * found *)
  | SafetyErr of (owned * place_expr) * (owned * place_expr)
                (* attempted access * conflicting loan *)
  | PermissionErr of ty * expr_path * owned
                     (* type not allowing access * operation being performed * context *)
  | NoReferenceToParameter of place
  | NoReferenceToCaptured of place
  | CannotMove of place_expr
  | MovedFunction of expr * ty (* expr in function position * the uninitialized type *)
  | PartiallyMoved of place * ty (* place that was moved * the type for it *)
  | PartiallyMovedPath of ty * path (* the type * the path that was moved *)
  | PartiallyMovedExprPath of ty * expr_path (* the type * the expr path that was moved *)
  | PartiallyMovedTypes of ty * ty (* uninitialized type * initialized type *)
  | UnificationFailed of ty * ty (* lhs is not a subtype of rhs *)
  | UnknownFunction of source_loc * fn_var
  | UnknownStruct of source_loc * struct_var
  | UnevaluatedEnvOf of var
  | UnsatisfiedEnvQualifier of owned * env (* the qualifier * the environment used *)
  | WrongStructConstructor of source_loc * struct_var * struct_kind
  | InvalidReturnType of ty * prov (* return type * invalidated provenance *)
  | InvalidType of ty
  | InvalidEnvVar of env_var * ty (* invalid env var * the type it was found in *)
  | InvalidProv of prov
  | InvalidLoan of owned * place_expr
  | InvalidArrayLen of ty * int
  | InvalidOperationOnType of path * ty
  | InvalidOperationOnTypeEP of expr_path * ty
  | DuplicateFieldsInStructDef of struct_var * (field * ty) * (field * ty)
  | InvalidCopyImpl of struct_var * ty (* for struct * because of ty *)
  | UnboundPlace of place
  | UnboundPlaceExpr of place_expr
  | PlaceExprNotAPlace of place_expr
  | AbsProvsNotSubtype of prov * prov
  | CannotPromoteLocalProvToAbstract of prov * prov (* cannot promote local prov to abstract prov *)
  | EnvArityMismatch of string * env list * env_vars
  | ProvArityMismatch of string * provs * provs
  | TysArityMismatch of string * ty list * ty list
  | TyArityMismatch of string * ty list * ty_var list
  | ExprArityMismatch of string * expr list * ty list
[@@deriving show]

type 'a tc =
  | Succ of 'a
  | Fail of tc_error
[@@deriving show]

let bind (tc : 'a tc) (f : 'a -> 'b tc) : 'b tc =
  match tc with
  | Succ x -> f x
  | Fail err -> Fail err

let succ (elem : 'a) : 'a tc = Succ elem
let fail (err : tc_error) : 'a tc = Fail err
let (let*) (tc : 'a tc) (f : 'a -> 'b tc) : 'b tc = bind tc f

(* lifting normal list operations to tc monad *)

let foldl (fn : 'a -> 'b -> 'a tc) (acc : 'a) (lst : 'b list) : 'a tc =
  let worker (acc : 'a tc) (elem : 'b) : 'a tc =
    let* acc = acc in fn acc elem
  in List.fold_left worker (Succ acc) lst

let foldr (fn : 'a -> 'b -> 'b tc) (lst : 'a list) (acc : 'b) : 'b tc =
  let worker (elem : 'a) (acc : 'b tc) : 'b tc =
    let* acc = acc in fn elem acc
  in List.fold_right worker lst (Succ acc)

let map (fn : 'a -> 'b tc) (lst : 'a list) : ('b list) tc =
  foldr (fun elem acc -> let* elem = elem in Succ (List.cons elem acc))
        (List.map fn lst) []

let for_each_rev (fn : 'a -> unit tc) (lst : 'a list) : unit tc =
  foldr (fun elem () -> fn elem) lst ()

let for_each (lst : 'a list) (fn : 'a -> unit tc) : unit tc =
  foldl (fun () elem -> fn elem) () lst

let find (fn : 'a -> bool tc) (lst : 'a list) : 'a option tc =
  let worker (acc : 'a option) (elem : 'a) : 'a option tc =
    match acc with
    | Some ans -> Succ (Some ans)
    | None -> let* test = fn elem in if test then Succ (Some elem) else Succ None
  in foldl worker None lst

let all (fn : 'a -> bool tc) (lst : 'a list) : bool tc =
  let worker (elem : 'a) (acc : 'b tc) : 'b tc =
    let* acc = acc
    in let* next = fn elem
    in Succ (acc && next)
  in List.fold_right worker lst (Succ true)

let any (fn : 'a -> bool tc) (lst : 'a list) : bool tc =
  let worker (elem : 'a) (acc : 'b tc) : 'b tc =
    let* acc = acc
    in let* next = fn elem
    in Succ (acc || next)
  in List.fold_right worker lst (Succ false)

(* combine helpers *)

let combine_evs (ctx : string) (ev1 : env list) (ev2 : env_vars) : (env * env_var) list tc =
  if List.length ev1 != List.length ev2 then Fail (EnvArityMismatch (ctx, ev1, ev2))
  else List.combine ev1 ev2 |> succ

let combine_prov (ctx : string) (prov1 : provs) (prov2 : provs) : (prov * prov) list tc =
  if List.length prov1 != List.length prov2 then Fail (ProvArityMismatch (ctx, prov1, prov2))
  else Succ (List.combine prov1 prov2)

let combine_tys (ctx : string) (tys1 : ty list) (tys2 : ty list) : (ty * ty) list tc =
  if List.length tys1 != List.length tys2 then Fail (TysArityMismatch (ctx, tys1, tys2))
  else Succ (List.combine tys1 tys2)

let combine_ty (ctx : string) (tys : ty list) (vars : ty_var list) : (ty * ty_var) list tc =
  if List.length tys != List.length vars then Fail (TyArityMismatch (ctx, tys, vars))
  else Succ (List.combine tys vars)

let combine_expr (ctx : string) (exprs : expr list) (tys : ty list) : (expr * ty) list tc =
  if List.length exprs != List.length tys then Fail (ExprArityMismatch (ctx, exprs, tys))
  else Succ (List.combine exprs tys)
