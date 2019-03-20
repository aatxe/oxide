open Syntax
open Meta

let rec omega_safe (gamma : place_ctx) (omega : owned) (pi : place) : ty option =
  if is_safe gamma omega pi then Some (List.assoc pi gamma)
  else None

let type_check (sigma : global_ctx) (delta : tyvar_ctx) (gamma : place_ctx) (expr : expr) : (ty * place_ctx) =
  let rec tc (delta : tyvar_ctx) (gamma : place_ctx) (expr : expr) : (ty * place_ctx) =
    match expr with
    | Move pi ->
      (match omega_safe gamma Unique pi with
       | Some ty -> (ty, if noncopyable ty then place_ctx_subtract gamma pi else gamma)
       | None -> failwith "type error")
    | _ -> failwith "unimplemented"
  in tc delta gamma expr
