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
let (x, y, z, w, a, b, r, v) = (1, 2, 3, 4, 5, 6, 7, 8)
let (x_mut, ref_x, ref_x_mut) = (9, 10, 11)
(* provenance variables for use in programs *)
let (p1, p2, p3, p4, p5, p6, p7) = (101, 102, 103, 104, 105, 106, 107)

(* function names for use in prograrms *)
let (gimmie) = (201)

(* short-hand for use in programs *)
let fn (name : fn_var) (provs : prov_var list) (tyvars : ty_var list) (params : (var * ty) list)
    (ret_ty : ty) (body : expr) : global_entry =
  FnDef (name, provs, tyvars, params, ret_ty, body)
let (@:) (var : var) (ty : ty) : var * ty = (var, ty)

let (~:) (ty : ty) : ann_ty = (loc(), ty)
let u32 : ty = BaseTy U32
let bool : ty = BaseTy Bool
let shrd : owned = Shared
let uniq : owned = Unique
let (~&) (prov : prov_var) (omega : owned) (ty : ty) : ty = Ref (prov, omega, ty)

let unit : expr = (("static", 0, 0), Prim Unit)
let tru : expr = (("static", 0, 0), Prim True)
let fls : expr = (("static", 0, 0), Prim False)

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
let app (fn : expr) (provs : prov_var list) (tys : ann_ty list) (args : expr list) : expr =
  (loc(), App (fn, provs, tys, args))
let (~@) (fn : fn_var) : expr = (loc(), Fn fn)
let cond (e1 : expr) (e2 : expr) (e3 : expr) : expr = (loc(), Branch (e1, e2, e3))
let (<==) (pi : place_expr) (e : expr) : expr = (loc(), Assign (pi, e))
let (>>) (e1 : expr) (e2 : expr) : expr = (loc(), Seq (e1, e2))
