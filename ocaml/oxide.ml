open Syntax
open Meta

let print_is_safe (gamma : place_env) (mu : muta) (pi : place) =
  (if is_safe gamma mu pi then Format.printf "%a is %a safe in@.  %a@."
   else Format.printf "%a is not %a safe in@.  %a@.") pp_place pi pp_muta mu pp_place_env gamma

let main =
  let (x, y, _) = (Var 1, Var 2, Var 3)
  in let u32  = BaseTy U32
  in let pi1 = x
  in let pi2 = IndexProj (x, 0)
  in let shared_ref from ty : ty = Ref (ProvSet [(Shared, from)], Shared, ty)
  in let env1 : place_env = [(x, Tup [u32])]
  in let env2 : place_env = [(x, Tup [u32]); (y, shared_ref pi2 u32)]
  in let env3 : place_env = [(x, Tup [u32]); (y, shared_ref pi1 (Tup [u32]))]
  in begin
    print_is_safe env1 Unique pi1;
    print_is_safe env1 Unique pi2;
    print_is_safe env2 Unique pi1;
    print_is_safe env2 Unique pi2;
    print_is_safe env2 Shared pi1;
    print_is_safe env2 Shared pi2;
    print_is_safe env3 Shared pi2;
    print_is_safe env3 Unique pi2;
  end
