open Syntax
open Meta

let rec omega_safe (gamma : place_env) (omega : owned) (pi : place) : ty option =
  if is_safe gamma omega pi then Some (List.assoc pi gamma)
  else None

let type_check (sigma : global_env) (delta : tyvar_env) (gamma : place_env) (expr : expr) : (ty * place_env) tc =
  let rec tc (delta : tyvar_env) (gamma : place_env) (expr : expr) : (ty * place_env) tc =
    match snd expr with
    | Move pi ->
      (match omega_safe gamma Unique pi with
       | Some ty -> Succ (ty, if noncopyable ty then place_env_subtract gamma pi else gamma)
       | None -> Fail (SafetyErr (fst expr, Unique, pi)))
    | Borrow (omega, pi) ->
      (match omega_safe gamma omega pi with
       | Some ty -> Succ (Ref (ProvSet [(omega, pi)], omega, ty), gamma)
       | None -> Fail (SafetyErr (fst expr, omega, pi)))
    | Seq (e1, e2) ->
      (match tc delta gamma e1 with
       | Succ (_, gamma1) -> tc delta gamma1 e2
       | Fail err -> Fail err)
    | Branch (e1, e2, e3) ->
      (match tc delta gamma e1 with
       | Succ (BaseTy Bool, gamma1) ->
         (match (tc delta gamma1 e2, tc delta gamma1 e3) with
          | (Succ (ty2, gamma2), Succ (ty3, gamma3)) -> failwith "unimplemented"
          | (Fail err, _) | (_, Fail err) -> Fail err)
       | Succ (found, _) -> Fail (TypeMismatch (fst e1, BaseTy Bool, found))
       | Fail err -> Fail err)
  | _ -> failwith "unimplemented"
  in tc delta gamma expr
