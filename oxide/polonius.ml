open Oxide.Edsl
open Oxide.Syntax

(* this variant of 4b tries to re-use the reborrowed ref, and should error *)
let borrowck_access_permissions_4b_variant : expr =
  reset "borrowck_access_permissions_4b_variant.rs";
  (letexp x ~:u32 (*=*) (num 1)
  (letexp x_mut ~:u32 (*=*) (num 2)
  (letexp ref_x ~:(~&p1 shrd u32) (*=*) (borrow p1 shrd (var x))
  (letexp ref_x_mut ~:(~&p2 uniq u32) (*=*) (borrow p2 uniq (var x_mut))
  (letexp y ~:(~&p3 uniq u32) (*=*) (borrow p3 uniq ~*(var ref_x_mut))
  (move (var ref_x_mut)))))))

let (borrowed_local_error_sigma, borrowed_local_error) : global_env * expr =
  reset "borrowed_local_error.rs"; (
    [
      fn gimmie [(loc(), p1)] [] [x @: (~&p1 shrd (prod [u32]))] (~&p1 shrd u32) (
        borrow p1 shrd ((var x) $. 0)
      )
    ],
    (letexp x ~:(~&p2 shrd u32) (*=*) (app (~@ gimmie) [p2] [] [
        (letexp v ~:(prod [u32]) (*=*) (tup [num 22])
        (borrow p2 shrd (var v)))
      ]) (* at this point, the scope of v ends, and the prov p2 is invalid *)
    (move (var x)))
  )

(* from https://paper.dropbox.com/doc/Polonius-and-subset-propagation-2uMIPkQSbqpPjqrJ9L9DM *)
let unnecessary_error : expr =
  reset "unnecessary_error.rs";
  (letexp a ~:u32 (*=*) (num 0)
  (letexp b ~:u32 (*=*) (num 1)
  (letexp x ~:(prod [~&p1 shrd u32]) (*=*) (tup [borrow p1 shrd (var a)])
  (letexp y ~:(prod [~&p2 shrd u32]) (*=*) (tup [borrow p2 shrd (var b)])
  (letexp z ~:u32 (*=*) (num 2) (
  (cond (tru)
     (((var y) $. 0) <== (move ((var x) $. 0)))
     (unit)
  ) >>
  (cond (tru)
     ((((var x) $. 0) <== (borrow p3 shrd (var z))) >>
      (move ((var x) $. 0)) >>
      unit)
     (unit)
  ) >>
  ((var z) <== (num 3)))))))) (* Polonius errors here, and so do we *)
