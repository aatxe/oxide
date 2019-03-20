open Syntax
open Meta

let rec omega_safe (gamma : place_env) (omega : owned) (pi : place) : ty option =
  if is_safe gamma omega pi then Some (List.assoc pi gamma)
  else None

let type_check (sigma : global_env) (delta : tyvar_env) (gamma : place_env) (expr : expr) : (ty * place_env) =
  let rec tc (delta : tyvar_env) (gamma : place_env) (expr : expr) : (ty * place_env) =
    match expr with
    | Move pi ->
      (match omega_safe gamma Unique pi with
       | Some ty -> (ty, if noncopyable ty then place_env_subtract gamma pi else gamma)
       | None -> failwith "type error")
    | _ -> failwith "unimplemented"
  in tc delta gamma expr
