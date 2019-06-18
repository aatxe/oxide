open Syntax
open Meta
open Typeck
open Borrowck (* examples from rust's borrowck tests *)
open Polonius (* examples from me, Niko, or the nll tests *)

let print_is_safe (ell : loan_env) (gamma : place_env) (omega : owned) (pi : place_expr) =
  (match is_safe ell gamma omega pi with
   | None -> Format.printf "%a is %a safe in@.  %a@."
   | Some _ -> Format.printf "%a is not %a safe in@.  %a@.")
    pp_place_expr pi pp_owned omega pp_place_env gamma

let print_tc (sigma : global_env) (expr : expr) =
  match type_check sigma empty_delta empty_ell empty_gamma expr with
  | Succ (ty, ellPrime, gammaPrime) ->
    Format.printf "%a@. under %a@. and@. %a@."
      pp_ty ty
      pp_loan_env ellPrime
      pp_place_env gammaPrime
  | Fail err -> Format.printf "ERROR: %a@." pp_tc_error err

let print_tc_closed (expr : expr) = print_tc empty_sigma expr

let main =
  print_tc_closed borrow_tuple_fields_2;
  print_tc_closed borrow_tuple_fields_3;
  print_tc_closed borrowck_access_permissions_4a;
  print_tc_closed borrowck_access_permissions_4b;
  print_tc_closed borrowck_access_permissions_4b_variant;
  print_tc borrowed_local_error_sigma borrowed_local_error;
  print_tc_closed unnecessary_error;
  (* let (x, y, _) : place * place * place = (Var 1, Var 2, Var 3)
   * in let tick_a = 1
   * in let u32 = BaseTy U32
   * in let pi1 : place = x
   * in let pi2 : place = IndexProj (x, 0)
   * in let shared_ref from ty : ty = Ref (from, Shared, ty)
   * in let ell1 : loan_env = ([], ([], []))
   * in let ell2 : loan_env = ([(tick_a, [(Shared, pi2)])], ([], []))
   * in let ell3 : loan_env = ([(tick_a, [(Shared, pi1)])], ([], []))
   * in let gam1 : place_env = [(x, Tup [u32])]
   * in let gam2 : place_env = [(x, Tup [u32]); (y, shared_ref tick_a u32)]
   * in let gam3 : place_env = [(x, Tup [u32]); (y, shared_ref tick_a (Tup [u32]))]
   * in begin
   *   print_is_safe ell1 gam1 Unique pi1;
   *   print_is_safe ell1 gam1 Unique pi2;
   *   print_is_safe ell2 gam2 Unique pi1;
   *   print_is_safe ell2 gam2 Unique pi2;
   *   print_is_safe ell2 gam2 Shared pi1;
   *   print_is_safe ell2 gam2 Shared pi2;
   *   print_is_safe ell3 gam3 Shared pi2;
   *   print_is_safe ell3 gam3 Unique pi2;
   * end *)
