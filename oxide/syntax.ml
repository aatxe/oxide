open Util

type linecol = int * int [@@deriving show]
type source_loc = string * linecol * linecol [@@deriving show]
let inferred : source_loc = ("<inferred>", (-1, -1), (-1, -1))
let dummy : source_loc = ("<dummy>", (-1, -1), (-1, -1))
type var = string [@@deriving show]
type ty_var = string [@@deriving show]
type fn_var = string [@@deriving show]
type prov_var = string [@@deriving show]
type struct_var = string [@@deriving show]
type field = string [@@deriving show]

type subtype_modality = Combine | Override [@@deriving show]
type owned = Shared | Unique [@@deriving show]
type place =
  | Var of var
  | FieldProj of place * field
  | IndexProj of place * int
[@@deriving show]
type places = place list [@@deriving show]
type place_expr =
  | Var of var
  | Deref of place_expr
  | FieldProj of place_expr * string
  | IndexProj of place_expr * int
[@@deriving show]

let rec place_to_place_expr (pi : place) : place_expr =
  match pi with
  | Var var -> Var var
  | FieldProj (pi_prime, field) -> FieldProj (place_to_place_expr pi_prime, field)
  | IndexProj (pi_prime, idx) -> IndexProj (place_to_place_expr pi_prime, idx)

let rec place_expr_to_place (pi : place_expr) : place option =
  match pi with
  | Var var -> Some (Var var)
  | Deref _ -> None
  | FieldProj (pi_prime, field) ->
    (match place_expr_to_place pi_prime with
     | Some pi_prime -> Some (FieldProj (pi_prime, field))
     | None -> None)
  | IndexProj (pi_prime, idx) ->
    (match place_expr_to_place pi_prime with
    | Some pi_prime -> Some (IndexProj (pi_prime, idx))
    | None -> None)

(* returns true if the place expression doesn't contain any dereferencing *)
let rec place_expr_is_place (pi : place_expr) : bool =
  match pi with
  | Var _ -> true
  | Deref _ -> false
  | FieldProj (pi_prime, _) | IndexProj (pi_prime, _) -> place_expr_is_place pi_prime

type loan = owned * place_expr [@@deriving show]
type loans = loan list [@@deriving show]
type prov = source_loc * prov_var [@@deriving show]
type provs = prov list [@@deriving show]

type kind = Star | Prov [@@deriving show]
type base_ty = Bool | U32 | Unit [@@deriving show]
type prety =
  | Any
  | BaseTy of base_ty
  | TyVar of ty_var
  | Ref of prov * owned * ty
  | Fun of prov list * ty_var list * ty list * place_env * ty
  | Array of ty * int
  | Slice of ty
  | Tup of ty list
  | Struct of struct_var * prov list * ty list
[@@deriving show]
and ty = source_loc * prety [@@deriving show]
and place_env = (place * ty) list [@@deriving show]

(* is the given type a sized type? *)
let is_sized (typ : ty) : bool =
  (* this exists so that we don't have to stratify our types *)
  match snd typ with
  | Slice _ -> false
  | _ -> true

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
  | Borrow of prov * owned * place_expr
  | BorrowIdx of prov * owned * place_expr * expr
  | BorrowSlice of prov * owned * place_expr * expr * expr
  | LetProv of prov list * expr
  | Let of var * ty * expr * expr
  | Assign of place_expr * expr
  | Seq of expr * expr
  | Fn of fn_var
  | Fun of prov list * ty_var list * (var * ty) list * (ty option) * expr
  | App of expr * prov list * ty list * expr list
  | Idx of place_expr * expr
  | Abort of string
  | Branch of expr * expr * expr
  | While of expr * expr
  | For of var * expr * expr
  | Tup of expr list
  | Array of expr list
  | RecStruct of struct_var * prov list * ty list * (field * expr) list
  | TupStruct of struct_var * prov list * ty list
  | Ptr of owned * place
and expr = source_loc * preexpr
[@@deriving show]

type value =
  | Prim of prim
  | Fun of prov list * ty_var list * (var * ty) list * expr
  | Tup of value list
  | Array of value list
  | Ptr of owned * place
[@@deriving show]

type shape =
  | Hole
  | Prim of prim
  | Fun of prov list * ty_var list * (var * ty) list * expr
  | Tup of unit list
  | Array of value list
  | Ptr of owned * place
[@@deriving show]

type store = (place * shape) list [@@deriving show]

type fn_def = fn_var * prov list * ty_var list * (var * ty) list * ty * expr
[@@deriving show]
type rec_struct_def = struct_var * prov list * ty_var list * (field * ty) list
[@@deriving show]
type tup_struct_def = struct_var * prov list * ty_var list * ty list
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
    | FnDef (fn_here, _, _, _, _, _) -> fn_here = fn
    (* we treat tuple structs as having defined a function to construct them *)
    | TupStructDef (fn_here, _, _, _) -> fn_here = fn
    | _ -> false
  in match List.find_opt is_right_fn sigma with
  | Some (FnDef defn) -> Some defn
  | Some (TupStructDef (name, provs, tyvars, tys)) ->
    let params = List.mapi (fun i ty -> (string_of_int i, ty)) tys
    in let tys = List.map (fun var -> (inferred, TyVar var)) tyvars
    in let body =
      (inferred, (App ((inferred, TupStruct (name, provs, tys)), provs, tys,
                     List.map (fun pair -> (inferred, Move (Var (fst pair)))) params)))
    in Some (name, provs, tyvars, params, (inferred, Struct (name, provs, tys)), body)
  | _ -> None

let global_env_find_struct (sigma : global_env) (name : struct_var) : struct_def option =
  let is_right_struct (entry : global_entry) : bool =
    match entry with
    | RecStructDef (name_here, _, _, _) -> name_here = name
    | TupStructDef (name_here, _, _, _) -> name_here = name
    | _ -> false
  in match List.find_opt is_right_struct sigma with
  | Some (RecStructDef defn) -> Some (Rec defn)
  | Some (TupStructDef defn) -> Some (Tup defn)
  | _ -> None

type tyvar_env = prov list * ty_var list [@@deriving show]
let empty_delta : tyvar_env = ([], [])

let tyvar_env_prov_mem (delta : tyvar_env) (var : prov) : bool = List.mem var (fst delta)
let tyvar_env_ty_mem (delta : tyvar_env) (var : ty_var) : bool = List.mem var (snd delta)

type subty = prov_var * prov_var [@@deriving show]
type loan_env = (prov_var * loans) list * (prov_var list * subty list) [@@deriving show]
let empty_ell : loan_env = ([], ([], []))

let loan_env_mem (ell : loan_env) (var : prov) : bool = List.mem_assoc (snd var) (fst ell)
let loan_env_lookup_opt (ell : loan_env) (var : prov) : loans option =
  List.assoc_opt (snd var) (fst ell)
let loan_env_is_abs (ell : loan_env) (var : prov) : bool = List.mem (snd var) (sndfst ell)
let loan_env_abs_sub (ell : loan_env) (v1 : prov) (v2 : prov) : bool =
  List.mem (snd v1, snd v2) (sndsnd ell)
let loan_env_lookup (ell : loan_env) (var : prov) : loans =
  if loan_env_is_abs ell var then [] else List.assoc (snd var) (fst ell)

let loan_env_include (ell : loan_env) (var : prov) (loans : loans) : loan_env =
  (List.cons (snd var, loans) (fst ell), snd ell)
let loan_env_bind (ell : loan_env) (var : prov) : loan_env =
  (fst ell, (List.cons (snd var) (sndfst ell), sndsnd ell))
let loan_env_bindall (ell : loan_env) (vars : prov list) : loan_env =
  (fst ell, (List.append (List.map snd vars) (sndfst ell), sndsnd ell))
let loan_env_add_abs_sub (ell : loan_env) (v1 : prov) (v2 : prov) : loan_env =
  let trans_extend (cs : subty list) (lhs : prov_var) (rhs : prov_var) : subty list =
    let into_lhs = List.filter (fun cx -> (snd cx) = lhs) cs
    in let from_rhs = List.filter (fun cx -> (fst cx) = rhs) cs
    in let new_cs = List.append (List.map (fun cx -> (fst cx, rhs)) into_lhs)
           (List.map (fun cx -> (lhs, snd cx)) from_rhs)
    in List.append new_cs cs
  in (fst ell, (sndfst ell, trans_extend (sndsnd ell) (snd v1) (snd v2)))
let loan_env_append (ell1 : loan_env) (ell2 : loan_env) : loan_env =
  (List.append (fst ell1) (fst ell2),
   (List.append (sndfst ell1) (sndfst ell2), sndsnd ell2))

let loan_env_exclude (ell : loan_env) (var : prov) : loan_env =
  (List.remove_assoc (snd var) (fst ell),
   (List.filter (fun v -> v != (snd var)) (sndfst ell),
    List.filter (fun cs -> fst cs != snd var || snd cs != snd var) (sndsnd ell)))

(* place_env is mutually recursive with ty and as such, is defined above *)
let empty_gamma : place_env = []

type struct_kind = Rec | Tup [@@deriving show]

type tc_error =
  | TypeMismatch of ty * ty (* expected * found *)
  | TypeMismatchIterable of ty (* found *)
  | TypeMismatchFunction of ty (* found *)
  | TypeMismatchRef of ty (* found *)
  | PlaceEnvMismatch of source_loc * place_env * place_env (* source_loc * expected * found *)
  | LoanEnvMismatch of source_loc * loan_env * loan_env (* source_loc * expected * found *)
  | SafetyErr of source_loc * (owned * place_expr) * (owned * place_expr)
                (* source_loc * attempted access * conflicting loan *)
  | PermissionErr of source_loc * (owned * place_expr) * ty
                     (* source_loc * attempted access * ty that doesn't permit this access *)
  | CannotMove of source_loc * place_expr
  | UnificationFailed of ty * ty
  | UnknownFunction of source_loc * fn_var
  | UnknownStruct of source_loc * struct_var
  | WrongStructConstructor of source_loc * struct_var * struct_kind
  | InvalidType of ty
  | InvalidProv of prov
  | InvalidLoan of source_loc * owned * place_expr
  | InvalidArrayLen of ty * int
  | InvalidPlaceExprFromType of place_expr * ty
  | DuplicateFieldsInStructDef of struct_var * (field * ty) * (field * ty)
  | UnboundPlace of source_loc * place
  | UnboundPlaceExpr of source_loc * place_expr
  | AbsProvsNotSubtype of prov * prov
[@@deriving show]

type 'a tc =
  | Succ of 'a
  | Fail of tc_error
[@@deriving show]

let bind (tc : 'a tc) (f : 'a -> 'b tc) : 'b tc =
  match tc with
  | Succ x -> f x
  | Fail err -> Fail err

let (let*) (tc : 'a tc) (f : 'a -> 'b tc) : 'b tc = bind tc f
