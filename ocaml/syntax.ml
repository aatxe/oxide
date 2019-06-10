type source_loc = int * int [@@deriving show]
type var = int [@@deriving show]
type ty_var = int [@@deriving show]
type fn_var = int [@@deriving show]
type prov_var = int [@@deriving show]

type owned = Shared | Unique [@@deriving show]
type place =
  | Var of var
  | FieldProj of place * string
  | IndexProj of place * int
[@@deriving show]
type place_expr =
  | Var of var
  | Deref of place_expr
  | FieldProj of place_expr * string
  | IndexProj of place_expr * int
[@@deriving show]

type loan = owned * place [@@deriving show]
type loans = (owned * place) list [@@deriving show]
type prov =
  | ProvVar of prov_var
  | ProvSet of loans
[@@deriving show]

type kind = Star | Prov [@@deriving show]
type base_ty = Bool | U32 | Unit [@@deriving show]
type ty =
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of prov_var * owned * ty
  | Fun of prov_var list * ty_var list * ty list * place_env * ty
  | Array of ty * int
  | Slice of ty
  | Tup of ty list
[@@deriving show]
and place_env = (place * ty) list [@@deriving show]

type ann_ty = source_loc * ty [@@deriving show]

(* is the given type a sized type? *)
let is_sized (typ : ty) : bool =
  (* this exists so that we don't have to stratify our types *)
  match typ with
  | Slice _ -> false
  | _ -> true

type prim =
  | Unit
  | Num of int
  | True
  | False
[@@deriving show]

type preexpr =
  | Prim of prim
  | Move of place_expr
  | Borrow of prov_var * owned * place_expr
  | BorrowIdx of prov_var * owned * place_expr * expr
  | BorrowSlice of prov_var * owned * place_expr * expr * expr
  | LetProv of prov_var list * expr
  | Let of var * ann_ty * expr * expr
  | Assign of place_expr * expr
  | Seq of expr * expr
  | Fn of fn_var
  | Fun of prov_var list * ty_var list * (var * ann_ty) list * expr
  | App of expr * prov list * ann_ty list * expr list
  | Idx of place_expr * expr
  | Abort of string
  | Branch of expr * expr * expr
  | For of var * expr * expr
  | Tup of expr list
  | Array of expr list
  | Ptr of owned * place
and expr = source_loc * preexpr
[@@deriving show]

type value =
  | Prim of prim
  | Fun of prov_var list * ty_var list * (var * ann_ty) list * expr
  | Tup of value list
  | Array of value list
  | Ptr of owned * place
[@@deriving show]

type shape =
  | Hole
  | Prim of prim
  | Fun of prov_var list * ty_var list * (var * ann_ty) list * expr
  | Tup of unit list
  | Array of value list
  | Ptr of owned * place
[@@deriving show]

type store = (place * shape) list [@@deriving show]

type fn_def = fn_var * prov_var list * ty_var list * (var * ty) list * ty * expr [@@deriving show]
type global_entry =
  | FnDef of fn_def
[@@deriving show]

type global_env = global_entry list [@@deriving show]

let global_env_find_fn (sigma : global_env) (fn : fn_var) : fn_def option =
  let is_right_fn (entry : global_entry) : bool =
    match entry with
    | FnDef (fn_here, _, _, _, _, _) -> fn_here = fn
  in match List.find_opt is_right_fn sigma with
  | Some (FnDef defn) -> Some defn
  | _ -> None

type tyvar_env = prov_var list * ty_var list [@@deriving show]
type loan_env = (prov_var * loans) list [@@deriving show]

let loan_env_lookup (ell : loan_env) (var : prov_var) : loans = List.assoc var ell
let loan_env_include (ell : loan_env) (var : prov_var) (loans : loans) = List.cons (var, loans) ell
let loan_env_exclude (ell : loan_env) (var : prov_var) = List.remove_assoc var ell

(* place_env is mutually recursive with ty and as such, is defined above *)
let place_env_lookup (gamma : place_env) (x : place) : ty = List.assoc x gamma
let place_env_include (gamma : place_env) (x : place) (typ : ty) = List.cons (x, typ) gamma
let place_env_exclude (gamma : place_env) (x : place) = List.remove_assoc x gamma

type tc_error =
  | TypeMismatch of source_loc * ty * ty (* source_loc * expected * found *)
  | TypeMismatchIterable of source_loc * ty (* source_loc * found *)
  | TypeMismatchFunction of source_loc * ty (* source_loc * found *)
  | PlaceEnvMismatch of source_loc * place_env * place_env (* source_loc * expected * found *)
  | LoanEnvMismatch of source_loc * loan_env * loan_env (* source_loc * expected * found *)
  | SafetyErr of source_loc * owned * place_expr
  | CannotMove of source_loc * place_expr
  | UnificationFailed of source_loc * ty * ty
  | UnknownFunction of source_loc * fn_var

type 'a tc =
  | Succ of 'a
  | Fail of tc_error
