open Syntax
open Meta

let omega_safe (ell : loan_env) (gamma : place_env) (omega : owned) (pi : place_expr) : (ty * loans) option =
  failwith "unimplemented"
  (* if is_safe ell gamma omega pi then Some (List.assoc pi gamma)
   * else None *)

let unify (ell : loan_env) (ty1 : ty) (ty2 : ty) : loan_env * ty = failwith "unimplemented"

let intersect (envs1 : loan_env * place_env) (envs2 : loan_env * place_env) : loan_env * place_env =
  let (ell1, gamma1) = envs1
  in let (ell2, gamma2) = envs2
  in failwith "unimplemented"

let valid_type (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env) (ty : ty) : () tc =
  failwith "unimplemented"

let type_check (sigma : global_env) (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
               (expr : expr) : (ty * loan_env * place_env) tc =
  let rec tc (delta : tyvar_env) (ell : loan_env) (gamma : place_env)
             (expr : expr) : (ty * loan_env * place_env) tc =
    match snd expr with
    | Move pi ->
      (match omega_safe ell gamma Unique pi with
       | Some (ty, _) -> Succ (ty, ell, if noncopyable ty then place_env_subtract gamma pi else gamma)
       | None -> Fail (SafetyErr (fst expr, Unique, pi)))
    | Borrow (prov, omega, pi) ->
      (match omega_safe ell gamma omega pi with
       | Some (ty, loans) -> Succ (Ref (prov, omega, ty), loan_env_include ell prov loans, gamma)
       | None -> Fail (SafetyErr (fst expr, omega, pi)))
    | Seq (e1, e2) ->
      (match tc delta ell gamma e1 with
       | Succ (_, ell1, gamma1) -> tc delta ell1 gamma1 e2
       | Fail err -> Fail err)
    | Branch (e1, e2, e3) ->
      (match tc delta ell gamma e1 with
       | Succ (BaseTy Bool, ell1, gamma1) ->
         (match (tc delta ell1 gamma1 e2, tc delta ell1 gamma1 e3) with
          | (Succ (ty2, ell2, gamma2), Succ (ty3, ell3, gamma3)) ->
            (let (ellPrime, gammaPrime) = intersect (ell2, gamma2) (ell3, gamm3)
             in let (ellFinal, tyFinal) = unify ellPrime ty2 ty3
             in match valid_type sigma delta ellFinal gammaPrime tyFinal with
             | Succ () -> (tyFinal, ellFinal, gammaPrime)
             | Fail err -> Fail err)
          | (Fail err, _) | (_, Fail err) -> Fail err)
       | Succ (found, _, _) -> Fail (TypeMismatch (fst e1, BaseTy Bool, found))
       | Fail err -> Fail err)
  | _ -> failwith "unimplemented"
  in tc delta ell gamma expr
