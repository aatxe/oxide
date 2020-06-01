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
type place_exprs = place_expr list [@@deriving show]

(* find the root of a given place expr *)
let root_of : place -> var = fst >> snd
(* find the path for the given place *)
let path_of : place -> path = snd >> snd

(* find the root of a given place expr *)
let expr_root_of : place_expr -> var = fst >> snd
(* find the path for the given place_expr *)
let expr_path_of : place_expr -> expr_path = snd >> snd

(* converts a path entry into an expr path entry *)
let path_entry_to_expr_path_entry (entry : path_entry) : expr_path_entry =
  match entry with
  | Field f -> Field f
  | Index i -> Index i

(* converts a path into a place expression path *)
let path_to_expr_path (path : path) : expr_path = List.map path_entry_to_expr_path_entry path

(* converts a place into a place expression, which always succeeds *)
let place_to_place_expr (pi : place) : place_expr =
  let (root, path) = snd pi
  in (fst pi, (root, path_to_expr_path path))

(* converts expr path entries to their corresponding path entry form *)
(* returns none if the expr path entry is Deref *)
let expr_path_entry_to_path_entry (entry : expr_path_entry) : path_entry option =
  match entry with
  | Field f -> Some (Field f)
  | Index i -> Some (Index i)
  | Deref -> None

(* converts a place expression path to a path, if possible, reutrning none otherwise *)
let expr_path_to_path (path : expr_path) : path option =
  let work (entry : expr_path_entry) (acc : path option) : path option =
    match acc with
    | Some path ->
      (match expr_path_entry_to_path_entry entry with
       | Some entry -> Some (List.cons entry path)
       | None -> None)
    | None -> None
  in List.fold_right work path (Some [])

(* converts a place expression to a place, if possible, returning none otherwise *)
let place_expr_to_place (pi : place_expr) : place option =
  let (root, path) = snd pi
  in match expr_path_to_path path with
  | Some path -> Some (fst pi, (root, path))
  | None -> None

(* returns true if the place expression doesn't contain any dereferencing *)
let place_expr_is_place : place_expr -> bool = not >> List.mem Deref >> snd >> snd

type loan = owned * place_expr [@@deriving show]
type loans = loan list [@@deriving show]
type prov = source_loc * prov_var [@@deriving show]
type provs = prov list [@@deriving show]
type bound = prov * prov [@@deriving show]
type bounds = bound list [@@deriving show]

(* does the given provenance list contain the given provenance? *)
let contains (prov : prov) (provs : provs) : bool =
  provs |> List.map snd |> List.mem (snd prov)

(* are the two given bounds lists equal? *)
let eq_bounds (bounds1 : bounds) (bounds2 : bounds) : bool =
  equal_unordered (bounds1 |> List.map (fun (l, r) -> (snd l, snd r)))
                  (bounds2 |> List.map (fun (l, r) -> (snd l, snd r)))

type base_ty = Bool | U32 | Unit [@@deriving show]
type prety =
  | Any
  | Infer (* infer this type! *)
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of prov * owned * ty
  | Fun of env_vars * provs * ty_var list * ty list * env * ty * bounds
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
  | Env of static_frame (* a concrete environment *)
  | EnvOf of var (* the environment of a specific bound function at closure type *)
[@@deriving show]
and frame_entry =
  | Id of var * ty
  | Prov of prov * loans
and static_frame = frame_entry list [@@deriving show]

let to_bindings (frame : static_frame) : (var * ty) list =
  frame |> List.map (fun entry ->
                       match entry with Id (id, ty) -> [(id, ty)] | Prov _ -> [])
        |> List.flatten

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
  | Fun (_, _, _, tys, gamma, ty, _) ->
    all_init tys && var_env_init gamma && is_init ty
  | Array (ty, _) | Slice ty -> is_init ty
  | Rec fields -> all_init (List.map snd fields)
  | Tup tys -> all_init tys
  | Struct (_, _, tys, Some ty) -> all_init tys && is_init ty
  | Struct (_, _, tys, None) -> all_init tys
  | Uninit _ -> false
and all_init (tys : ty list) : bool =
  List.fold_right (fun ty acc -> acc && is_init ty) tys true
and var_env_init (frame : env) : bool =
  match frame with
  | Unboxed | EnvVar _ -> true
  | Env frame -> frame |> to_bindings |> List.map snd |> all_init
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

type subty = prov_var * prov_var [@@deriving show]
type tyvar_env = env_vars * provs * ty_var list * subty list [@@deriving show]
let empty_delta : tyvar_env = ([], [], [], [])

let env_vars_of (delta : tyvar_env) : env_vars = match delta with (evs, _, _, _) -> evs
let provs_of (delta : tyvar_env) : provs = match delta with (_, provs, _, _) -> provs
let ty_vars_of (delta : tyvar_env) : ty_var list = match delta with (_, _, tyvars, _) -> tyvars
let bounds_of (delta : tyvar_env) : subty list = match delta with (_, _, _, bounds) -> bounds

let tyvar_env_add_env_vars (evs : env_vars) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (curr_evs, provs, tyvars, bounds) -> (list_union curr_evs evs, provs, tyvars, bounds)
let tyvar_env_add_provs (provs : provs) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (evs, curr_provs, tyvars, bounds) -> (evs, list_union curr_provs provs, tyvars, bounds)
let tyvar_env_add_ty_vars (tyvars : ty_var list) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (evs, provs, curr_tyvars, bounds) -> (evs, provs, list_union curr_tyvars tyvars, bounds)
let tyvar_env_add_bounds (bounds : subty list) (delta : tyvar_env) : tyvar_env =
  match delta with
  | (evs, provs, tyvars, curr_bounds) -> (evs, provs, tyvars, list_union curr_bounds bounds)

let tyvar_env_prov_mem (delta : tyvar_env) (var : prov) : bool =
  provs_of delta |> List.map snd |> List.mem (snd var)
let tyvar_env_ty_mem (delta : tyvar_env) (var : ty_var) : bool =
  ty_vars_of delta |> List.mem var
let tyvar_env_env_var_mem (delta : tyvar_env) (var : env_var) : bool =
  env_vars_of delta |> List.mem var
let tyvar_env_abs_sub (delta : tyvar_env) (v1 : prov) (v2 : prov) : bool =
  bounds_of delta |> List.mem (snd v1, snd v2) || (snd v1) = (snd v2)

type var_env = static_frame list [@@deriving show]
let empty_gamma : var_env = [[]]

(* shift the latest entry off the frame *)
let shift (gamma : var_env) : var_env =
  match gamma with
  | (_ :: top_frame) :: rest_of_stack -> top_frame :: rest_of_stack
  | [] :: _ -> failwith "cannot shift with empty frame on stack"
  | [] -> failwith "unreachable: var_env should never have zero frames"

(* shift the last n stack entries off the frame *)
let rec shift_n (n : int) (gamma : var_env) : var_env =
  match n with
  | 0 -> gamma
  | n -> shift gamma |> shift_n (pred n)

(* pops off the top frame of the stack *)
let pop (gamma : var_env) : var_env =
  match gamma with
  | _ :: [] -> [[]]
  | _ :: rest_of_stack -> rest_of_stack
  | [] -> failwith "unreachable: var_env should never have zero frames"

(* get the places from the given frame entry *)
let places_from_frame_entry (entry : frame_entry) : place_expr list =
  match entry with
  | Id _ -> []
  | Prov (_, loans) -> loans |> List.map snd

(* compute all the places in the loan sets occurring in gamma *)
let places_of (gamma : var_env) : place_expr list =
  gamma |> List.flatten
        |> List.map places_from_frame_entry
        |> List.flatten

let provs_in (frame : static_frame) : provs =
  frame |> List.map (fun entry -> match entry with Id _ -> [] | Prov (prov, _) -> [prov])
        |> List.flatten

let prov_domain_of (gamma : var_env) : provs =
  gamma |> List.flatten |> provs_in

let to_loan_env (gamma : var_env) : (prov * loans) list =
  gamma |> List.flatten
        |> List.map (fun entry ->
                       match entry with Id _ -> [] | Prov (prov, loans) -> [(prov, loans)])
        |> List.flatten

let to_prov_var_keys (concrete : (prov * loans) list) : (prov_var * loans) list =
  List.map (fun ((_, prov), loans) -> (prov, loans)) concrete

let loan_env_mem (gamma : var_env) (var : prov) : bool =
  gamma |> to_loan_env |> to_prov_var_keys |> List.mem_assoc (snd var)
let loan_env_lookup_opt (gamma : var_env) (var : prov) : loans option =
  gamma |> to_loan_env |> to_prov_var_keys |> List.assoc_opt (snd var)
let loan_env_lookup (gamma : var_env) (var : prov) : loans =
  gamma |> to_loan_env |> to_prov_var_keys |> List.assoc (snd var)

let loan_env_include (var : prov) (loans : loans) (gamma : var_env) : var_env =
  match gamma with
  | top_frame :: rest_of_stack -> (Prov (var, loans) :: top_frame) :: rest_of_stack
  | [] -> failwith "unreachable: var_env should never have zero frames"
let loan_env_include_all (provs : provs) (loans : loans) (gamma : var_env) : var_env =
  match gamma with
  | top_frame :: rest_of_stack ->
    let new_provs = provs |> List.map (fun prov -> Prov (prov, loans)) |> List.rev
    in List.append new_provs top_frame :: rest_of_stack
  | [] -> failwith "unreachable: var_env should never have zero frames"

(* useful for pretty-printing in ownership safety *)
type place_env = (place * ty) list [@@deriving show]

type struct_kind = Rec | Tup [@@deriving show]

type tc_error =
  | TypeMismatch of ty * ty (* expected * found *)
  | TypeMismatchIterable of ty (* found *)
  | TypeMismatchFunction of ty (* found *)
  | TypeMismatchRef of ty (* found *)
  | TypeMismatchArray of ty (* found *)
  | UnrelatedTypes of ty * ty (* neither ty1 nor ty2 are contained within one another *)
  | VarEnvMismatch of source_loc * var_env * var_env (* source_loc * expected * found *)
  | SafetyErr of (owned * place_expr) * (owned * place_expr)
                (* attempted access * conflicting loan *)
  | AbstractSafetyErr of prov * prov (* attempted access * conflicting provenance *)
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
  | CannotShadowProvenance of prov
  | ProvDoesNotOutlive of prov * prov (* the first provenance does not outlive the second *)
  | CannotCombineProvsInDifferentFrames of prov * prov
  | CannotBorrowIntoAbstractProvenance of prov
  | InvalidArrayLen of ty * int
  | InvalidOperationOnType of path * ty
  | InvalidOperationOnTypeEP of expr_path * ty
  | DuplicateFieldsInStructDef of struct_var * (field * ty) * (field * ty)
  | InvalidCopyImpl of struct_var * ty (* for struct * because of ty *)
  | UnboundPlace of place
  | UnboundPlaceExpr of place_expr
  | UnboundLoanInProv of loan * prov (* unbound loan * in prov *)
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

let succ (elem : 'a) : 'a tc = Succ elem
let fail (err : tc_error) : 'a tc = Fail err

let bind (tc : 'a tc) (f : 'a -> 'b tc) : 'b tc =
  match tc with
  | Succ x -> f x
  | Fail err -> Fail err
let (>>=) (tc : 'a tc) (f : 'a -> 'b tc) : 'b tc = bind tc f
let (<$>) (f : 'a -> 'b) (tc : 'a tc) : 'b tc = tc >>= (succ >> f)

let is_succ (elem : 'a tc) : bool = match elem with Succ _ -> true | Fail _ -> false
let is_fail (elem : 'a tc) : bool = match elem with Fail _ -> true | Succ _ -> false

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
