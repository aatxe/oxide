open Syntax

(* stores the last used location *)
let gloc : source_loc ref = ref ("", 0, 0)

(* returns a fresh location every time *)
let loc (_ : unit) : source_loc =
  let (file, line, char) = !gloc
  in gloc := (file, line + 1, 0);
     (file, line, char)

(* resets the source location info *)
let reset (file : string) : unit =
  gloc := (file, 0, 0)

(* variables for use in programs *)
let (x, y, z, w, a, b, r) = (1, 2, 3, 4, 5, 6, 7)
let (x_mut, ref_x, ref_x_mut) = (8, 9, 10)
(* provenance variables for use in programs *)
let (p1, p2, p3, p4, p5, p6, p7) = (101, 102, 103, 104, 105, 106, 107)

(* short-hand for use in programs *)
let (~:) (ty : ty) : ann_ty = (loc(), ty)
let u32 : ty = BaseTy U32
let bool : ty = BaseTy Bool
let shrd : owned = Shared
let uniq : owned = Unique
let (~&) (prov : prov_var) (omega : owned) (ty : ty) : ty = Ref (prov, omega, ty)

let borrow (prov : prov_var) (omega : owned) (pi : place_expr) : expr =
  (loc(), Borrow (prov, omega, pi))
let move (pi : place_expr) : expr = (loc(), Move pi)
let letexp (var : var) (ty : ann_ty) (e1 : expr) (e2 : expr) : expr =
  (loc(), Let (var, ty, e1, e2))
let (~*) (pi : place_expr) : place_expr = Deref pi
let ($.) (pi : place_expr) (idx : int) : place_expr = IndexProj (pi, idx)
let ($.$) (pi : place_expr) (field : string) : place_expr = FieldProj (pi, field)
let num (n : int) : expr = (loc(), Prim (Num n))
let tup (exprs : expr list) : expr = (loc(), Tup exprs)
let unit : expr = (loc(), Prim Unit)

(* rustc commit: e699ea096fcc2fc9ce8e8bcf884e11496a31cc9f *)

(* borrow_tuple_fields_1 omitted because of Box<_> type *)

let borrow_tuple_fields_2 : expr =
  reset "borrow_tuple_fields_2.rs";
  (letexp x ~:(Tup [u32; u32]) (*=*) (tup [num 1; num 2])
  (letexp a ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd ((Var x) $. 0))
  (letexp b ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq ((Var x) $. 0))
  (move (Var a)))))

let borrow_tuple_fields_3 : expr =
  reset "borrow_tuple_fields_3.rs";
  (letexp x ~:(Tup [u32; u32]) (*=*) (tup [num 1; num 2])
  (letexp a ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd ((Var x) $. 0))
  (letexp b ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq ((Var x) $. 0))
  (move (Var a)))))

(* borrow_tuple_fields 4, 5, 6 omitted because of structs (4 also has Box<_>) *)

(* borrowck_access_permissions 1, 2 omitted because of mut binding restrictions *)
(* borrowck_access_permissions 3 omitted because of Box<_> *)

let borrowck_access_permissions_4a : expr =
  reset "borrowck_access_permissions_4a.rs";
  (letexp x ~:u32 (*=*) (num 1)
  (letexp x_mut ~:u32 (*=*) (num 2)
  (letexp ref_x ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd (Var x))
  (letexp ref_x_mut ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq (Var x_mut))
  (letexp y ~:(~&p3 uniq u32) (*=*) (borrow p3 uniq ~*(Var ref_x))
  unit)))))

let borrowck_access_permissions_4b : expr =
  reset "borrowck_access_permissions_4b.rs";
  (letexp x ~:u32 (*=*) (num 1)
  (letexp x_mut ~:u32 (*=*) (num 2)
  (letexp ref_x ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd (Var x))
  (letexp ref_x_mut ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq (Var x_mut))
  (letexp y ~:(~&p3 uniq u32) (*=*) (borrow p3 uniq ~*(Var ref_x_mut))
  unit)))))

(* borrowck_access_permissions 5 omitted because of unsafe *)
(* borrowck_access_permissions 6 omitted because of structs *)
