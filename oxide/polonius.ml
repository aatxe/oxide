open Oxide.Edsl
open Oxide.Syntax

(* this variant of 4b tries to re-use the reborrowed ref, and should error *)
let borrowck_access_permissions_4b_variant : expr =
  reset "borrowck_access_permissions_4b_variant.rs";
  (letexp x ~:u32 (*=*) (num 1)
  (letexp x_mut ~:u32 (*=*) (num 2)
  (letexp ref_x ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd (Var x))
  (letexp ref_x_mut ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq (Var x_mut))
  (letexp y ~:(~&p3 uniq u32) (*=*) (borrow p3 uniq ~*(Var ref_x_mut))
  (move (Var ref_x_mut)))))))

let (borrowed_local_error_sigma, borrowed_local_error) : global_env * expr =
  reset "borrowed_local_error.rs"; (
    [
      fn gimmie [(loc(), p1)] [] [x @: (~&p1 shrd (prod [u32]))] (~&p1 shrd u32) (
        borrow p1 shrd ((Var x) $. 0)
      )
    ],
    (letexp x ~:(~&p2 shrd u32) (*=*) (app (~@ gimmie) [p2] [] [
        (letexp v ~:(prod [u32]) (*=*) (tup [num 22])
        (borrow p2 shrd (Var v)))
      ]) (* at this point, the scope of v ends, and the prov p2 is invalid *)
    (move (Var x)))
  )

(* from https://paper.dropbox.com/doc/Polonius-and-subset-propagation-2uMIPkQSbqpPjqrJ9L9DM *)
let unnecessary_error : expr =
  reset "unnecessary_error.rs";
  (letexp a ~:u32 (*=*) (num 0)
  (letexp b ~:u32 (*=*) (num 1)
  (letexp x ~:(prod [~&p1 shrd u32]) (*=*) (tup [borrow p1 shrd (Var a)])
  (letexp y ~:(prod [~&p2 shrd u32]) (*=*) (tup [borrow p2 shrd (Var b)])
  (letexp z ~:u32 (*=*) (num 2) (
  (cond (tru)
     (((Var y) $. 0) <== (move ((Var x) $. 0)))
     (unit)
  ) >>
  (cond (tru)
     ((((Var x) $. 0) <== (borrow p3 shrd (Var z))) >>
      (move ((Var x) $. 0)) >>
      unit)
     (unit)
  ) >>
  ((Var z) <== (num 3)))))))) (* Polonius errors here, and so do we *)
