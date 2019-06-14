open Syntax
open Meta
open Typeck
open Borrowck (* examples *)

let print_is_safe (ell : loan_env) (gamma : place_env) (omega : owned) (pi : place) =
  (match is_safe ell gamma omega pi with
   | None -> Format.printf "%a is %a safe in@.  %a@."
   | Some _ -> Format.printf "%a is not %a safe in@.  %a@.")
    pp_place pi pp_owned omega pp_place_env gamma

let print_tc_closed (expr : expr) =
  match type_check empty_sigma empty_delta empty_ell empty_gamma expr with
  | Succ (ty, ellPrime, gammaPrime) ->
    Format.printf "%a@. under %a@. and@. %a@."
      pp_ty ty
      pp_loan_env ellPrime
      pp_place_env gammaPrime
  | Fail err -> Format.printf "ERROR: %a@." pp_tc_error err

let main =
  print_tc_closed borrow_tuple_fields_2;
  print_tc_closed borrow_tuple_fields_3;
  print_tc_closed borrowck_access_permissions_4a;
  print_tc_closed borrowck_access_permissions_4b;
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
