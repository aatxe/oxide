open Syntax
open Meta

let print_is_safe (gamma : place_ctx) (omega : owned) (pi : place) =
  (if is_safe gamma omega pi then Format.printf "%a is %a safe in@.  %a@."
   else Format.printf "%a is not %a safe in@.  %a@.")
    pp_place pi pp_owned omega pp_place_ctx gamma

let main =
  let (x, y, _) = (Var 1, Var 2, Var 3)
  in let u32  = BaseTy U32
  in let pi1 = x
  in let pi2 = IndexProj (x, 0)
  in let shared_ref from ty : ty = Ref (ProvSet [(Shared, from)], Shared, ty)
  in let ctx1 : place_ctx = [(x, Tup [u32])]
  in let ctx2 : place_ctx = [(x, Tup [u32]); (y, shared_ref pi2 u32)]
  in let ctx3 : place_ctx = [(x, Tup [u32]); (y, shared_ref pi1 (Tup [u32]))]
  in begin
    print_is_safe ctx1 Unique pi1;
    print_is_safe ctx1 Unique pi2;
    print_is_safe ctx2 Unique pi1;
    print_is_safe ctx2 Unique pi2;
    print_is_safe ctx2 Shared pi1;
    print_is_safe ctx2 Shared pi2;
    print_is_safe ctx3 Shared pi2;
    print_is_safe ctx3 Unique pi2;
  end
