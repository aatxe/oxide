open Oxide.Edsl
open Oxide.Syntax

(* rustc commit: e699ea096fcc2fc9ce8e8bcf884e11496a31cc9f *)

(* borrow_tuple_fields_1 omitted because of Box<_> type *)

let borrow_tuple_fields_2 : expr =
  reset "borrow_tuple_fields_2.rs";
  (letexp x ~:(prod [u32; u32]) (*=*) (tup [num 1; num 2])
  (letexp a ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd ((var x) $. 0))
  (letexp b ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq ((var x) $. 0))
  (move (var a)))))

let borrow_tuple_fields_3 : expr =
  reset "borrow_tuple_fields_3.rs";
  (letexp x ~:(prod [u32; u32]) (*=*) (tup [num 1; num 2])
  (letexp a ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd ((var x) $. 0))
  (letexp b ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq ((var x) $. 0))
  (move (var a)))))

(* borrow_tuple_fields 4, 5, 6 omitted because of structs (4 also has Box<_>) *)

(* borrowck_access_permissions 1, 2 omitted because of mut binding restrictions *)
(* borrowck_access_permissions 3 omitted because of Box<_> *)

let borrowck_access_permissions_4a : expr =
  reset "borrowck_access_permissions_4a.rs";
  (letexp x ~:u32 (*=*) (num 1)
  (letexp x_mut ~:u32 (*=*) (num 2)
  (letexp ref_x ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd (var x))
  (letexp ref_x_mut ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq (var x_mut))
  (letexp y ~:(~&p3 uniq u32) (*=*) (borrow p3 uniq ~*(var ref_x))
  unit)))))

let borrowck_access_permissions_4b : expr =
  reset "borrowck_access_permissions_4b.rs";
  (letexp x ~:u32 (*=*) (num 1)
  (letexp x_mut ~:u32 (*=*) (num 2)
  (letexp ref_x ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd (var x))
  (letexp ref_x_mut ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq (var x_mut))
  (letexp y ~:(~&p3 uniq u32) (*=*) (borrow p3 uniq ~*(var ref_x_mut))
  unit)))))

(* borrowck_access_permissions 5 omitted because of unsafe *)
(* borrowck_access_permissions 6 omitted because of structs *)

(* borrowck_and_init omitted because it's about uninitialized variables *)

(* borrowck_anon_fields_struct tuple variant omitted because pattern matching *)

(* borrowck_argument omitted because of mut binding restrictions *)
