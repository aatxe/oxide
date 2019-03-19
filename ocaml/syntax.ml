type var = int [@@deriving show]
type ty_var = int [@@deriving show]
type prov_var = int [@@deriving show]

type muta = Shared | Unique [@@deriving show]
type place =
  | Var of var
  | Deref of place
  | FieldProj of place * string
  | IndexProj of place * int
[@@deriving show]

type loan = muta * place [@@deriving show]
type loans = (muta * place) list [@@deriving show]
type prov =
  | ProvVar of prov_var
  | ProvSet of loans
[@@deriving show]

type kind = Star | Prov [@@deriving show]
type base_ty = Bool | U32 | Unit [@@deriving show]
type ty =
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of prov * muta * ty
  | Fun of prov_var list * ty_var list * ty list * ty
  | Array of ty * int
  | Slice of ty
  | Tup of ty list
[@@deriving show]

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

type expr =
  | Prim of prim
  | Borrow of muta * place
  | BorrowIdx of muta * place * expr
  | BorrowSlice of muta * place * expr * expr
  | Let of var * ty * expr * expr
  | Assign of place * expr
  | Seq of expr * expr
  | Fun of prov_var list * ty_var list * (var * ty) list * expr
  | App of expr * prov list * ty list * expr list
  | Idx of place * expr
  | Abort of string
  | Branch of expr * expr * expr
  | For of var * expr * expr
  | Tup of expr list
  | Array of expr list
  | Ptr of muta * place
[@@deriving show]

type value =
  | Prim of prim
  | Fun of prov_var list * ty_var list * (var * ty) list * expr
  | Tup of value list
  | Array of value list
  | Ptr of muta * place
[@@deriving show]

type shape =
  | Hole
  | Prim of prim
  | Fun of prov_var list * ty_var list * (var * ty) list * expr
  | Tup of unit list
  | Array of value list
  | Ptr of muta * place
[@@deriving show]

type store = (place * shape) list [@@deriving show]

type global_ctx = unit (* TODO: actual global context definition *)
type tyvar_ctx = prov_var list * ty_var list [@@deriving show]
type place_ctx = (place * ty) list [@@deriving show]

let place_ctx_lookup (gamma : place_ctx) (x : place) : ty = List.assoc x gamma
let place_ctx_include (gamma : place_ctx) (x : place) (typ : ty) = List.cons (x, typ) gamma
let place_ctx_exclude (gamma : place_ctx) (x : place) = List.remove_assoc x gamma
