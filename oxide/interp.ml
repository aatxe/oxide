open Meta
open Syntax
open Util

type rt_error =
  | Aborted of string
  | StuckAtValue of value
  | CannotMovePlaceExpr of place_expr
  | NotAnArray of value
  | NoFunctionDefined of fn_var * global_env
  | NotANumber of prim
  | NotABoolean of prim
  | NotUnit of prim
and 'a rt =
  | Succ of 'a
  | Fail of rt_error
[@@deriving show]

let succ (elem : 'a) : 'a rt = Succ elem
let fail (err : rt_error) : 'a rt = Fail err

let bind (rt : 'a rt) (f : 'a -> 'b rt) : 'b rt =
  match rt with
  | Succ x -> f x
  | Fail err -> Fail err
let (>>=) (rt : 'a rt) (f : 'a -> 'b rt) : 'b rt = bind rt f
let (<$>) (f : 'a -> 'b) (rt : 'a rt) : 'b rt = rt >>= (succ >> f)

let is_succ (elem : 'a rt) : bool = match elem with Succ _ -> true | Fail _ -> false
let is_fail (elem : 'a rt) : bool = match elem with Fail _ -> true | Succ _ -> false

let (let*) (rt : 'a rt) (f : 'a -> 'b rt) : 'b rt = bind rt f

let extend (sigma : store) (id : var) (v : value) = failwith "unimplemented"
let update (sigma : store) (id : var) (v : value) = failwith "unimplemented"
let update_all (sigma : store) (ids : vars) (v : value) = failwith "unimplemented"

let from_store : source_loc = ("<store>", (-1, -1), (-1, -1))
let rec value_to_expr (value : value) : expr =
  match value with
  | Dead -> failwith "cannot convert dead to an expression"
  | PrimVal prim -> (from_store, Prim prim)
  | FnVal fn_var -> (from_store, Fn fn_var)
  | ClosureVal (frame, params, ret_ty, body) ->
    (from_store, Closure (frame, params, ret_ty, body))
  | TupVal values -> (from_store, Tup (values |> List.map value_to_expr))
  | ArrayVal values -> (from_store, Array (values |> List.map value_to_expr))
  | PtrVal referent -> (from_store, Ptr referent)

let expr_to_value (_ : expr) : value rt = failwith "unimplemented"

let unsafe_expr_to_value (e : expr) : value =
  match expr_to_value e with
  | Succ v -> v
  | Fail  err ->
    let () = pp_rt_error Format.str_formatter err
    in failwith ("unsafe_expr_to_value: " ^ Format.flush_str_formatter())

let is_value (_ : expr) : bool = false

let copyable (_ : value) : bool = false

let free_nc_vars_rt (_ : store) (_ : expr) : vars rt = failwith "unimplemented"

(* evaluate a binary operator on two primitive values *)
let delta (op : binop) (p1 : prim) (p2 : prim) : prim rt =
  (* mod in ocaml allows negative results, this redefines mod to be remainder *)
  let (mod) x y = ((x mod y) + y) mod y
  in match (op, p1, p2) with
  | (Add, Num n1, Num n2) -> Num (n1 + n2) |> succ
  | (Sub, Num n1, Num n2) -> Num (n1 - n2) |> succ
  | (Mul, Num n1, Num n2) -> Num (n1 * n2) |> succ
  | (Div, Num n1, Num n2) -> Num (n1 / n2) |> succ
  | (Rem, Num n1, Num n2) -> Num (n1 mod n2) |> succ
  | (BitXor, Num n1, Num n2) -> Num (n1 lxor n2) |> succ
  | (BitAnd, Num n1, Num n2) -> Num (n1 land n2) |> succ
  | (BitOr, Num n1, Num n2) -> Num (n1 lor n2) |> succ
  | (Shl, Num n1, Num n2) -> Num (n1 lsl n2) |> succ
  | (Shr, Num n1, Num n2) -> Num (n1 lsr n2) |> succ
  | (Add, Num _, p) | (Add, p, _) -> NotANumber p |> fail
  | (Sub, Num _, p) | (Sub, p, _) -> NotANumber p |> fail
  | (Mul, Num _, p) | (Mul, p, _) -> NotANumber p |> fail
  | (Div, Num _, p) | (Div, p, _) -> NotANumber p |> fail
  | (Rem, Num _, p) | (Rem, p, _) -> NotANumber p |> fail
  | (BitXor, Num _, p) | (BitXor, p, _) -> NotANumber p |> fail
  | (BitAnd, Num _, p) | (BitAnd, p, _) -> NotANumber p |> fail
  | (BitOr, Num _, p) | (BitOr, p, _) -> NotANumber p |> fail
  | (Shl, Num _, p) | (Shl, p, _) -> NotANumber p |> fail
  | (Shr, Num _, p) | (Shr, p, _) -> NotANumber p |> fail
  | (And, True, True) -> True |> succ
  | (And, True, False) | (And, False, True) | (And, False, False) -> False |> succ
  | (Or, True, True) | (Or, True, False) | (Or, False, True) -> True |> succ
  | (Or, False, False) -> False |> succ
  | (And, True, p) | (And, False, p) | (And, p, _) -> NotABoolean p |> fail
  | (Or, True, p) | (Or, False, p) | (Or, p, _) -> NotABoolean p |> fail
  | (Eq, Num n1, Num n2) -> if n1 == n2 then True |> succ else False |> succ
  | (Lt, Num n1, Num n2) -> if n1 < n2 then True |> succ else False |> succ
  | (Le, Num n1, Num n2) -> if n1 <= n2 then True |> succ else False |> succ
  | (Ne, Num n1, Num n2) -> if n1 <> n2 then True |> succ else False |> succ
  | (Ge, Num n1, Num n2) -> if n1 >= n2 then True |> succ else False |> succ
  | (Gt, Num n1, Num n2) -> if n1 > n2 then True |> succ else False |> succ
  | (Lt, Num _, p) | (Lt, p, _) -> NotANumber p |> fail
  | (Le, Num _, p) | (Le, p, _) -> NotANumber p |> fail
  | (Ge, Num _, p) | (Ge, p, _) -> NotANumber p |> fail
  | (Gt, Num _, p) | (Gt, p, _) -> NotANumber p |> fail
  | (Eq, True, True) | (Eq, False, False) -> True |> succ
  | (Eq, True, False) | (Eq, False, True) -> False |> succ
  | (Ne, True, True) | (Ne, False, False) -> False |> succ
  | (Ne, True, False) | (Ne, False, True) -> True |> succ
  | (Eq, Unit, Unit) -> True |> succ
  | (Ne, Unit, Unit) -> False |> succ
  | (Eq, Num _, p) | (Ne, Num _, p) -> NotANumber p |> fail
  | (Eq, True, p) | (Eq, False, p)
  | (Ne, True, p) | (Ne, False, p) -> NotABoolean p |> fail
  | (Eq, Unit, p) | (Ne, Unit, p) -> NotUnit p |> fail

(* replace pi's value in sigma with dead *)
let moved (pi : place) (sigma : sigma) : sigma rt =
  failwith "unimplemented"

(* evaluates a place expression to a referent and its associated value in sigma *)
let eval_place_expr (sigma : store) (phi : place_expr) : (referent * value) rt =
  failwith "unimplemented"

(* computes the value context for the value bound to phi in sigma *)
let value_ctx_in (sigma : store) (phi : place_expr) : value_ctx rt =
  failwith "unimplemented"

(* plugs the holes in the value context using the given value *)
let plug_value_ctx (ctx : value_ctx) (v : value) : value rt =
  failwith "unimplemented"

let step (globals : global_env) (sigma : store) (e : expr) : (store * expr) rt =
  let rec step (sigma : store) (e : expr) : (store * expr) rt =
    match snd e with
    | Prim prim -> StuckAtValue (PrimVal prim) |> fail
    | BinOp (op, (_, Prim p1), (_, Prim p2)) ->
      let* res = delta op p1 p2
      in let ePrime : expr = (inferred, Prim res)
      in (sigma, ePrime) |> succ
    | BinOp (op, (loc, Prim p1), e2) ->
      let* (sigmaPrime, e2Prime) = step sigma e2
      in (sigmaPrime, (fst e, BinOp (op, (loc, Prim p1), e2Prime))) |> succ
    | BinOp (op, e1, e2) ->
      let* (sigmaPrime, e1Prime) = step sigma e1
      in (sigmaPrime, (fst e, BinOp (op, e1Prime, e2))) |> succ
    | Move phi ->
      let* (_, value) = eval_place_expr sigma phi
      in if copyable value then (sigma, value_to_expr value) |> succ
      else (match place_expr_to_place phi with
      | Some pi -> (moved pi sigma, value_to_expr value) |> succ
      | None -> CannotMovePlaceExpr phi |> fail)
    | Drop phi ->
      let* (_, value) = eval_place_expr sigma phi
      in (match place_expr_to_place phi with
      | Some pi -> (moved pi sigma, value_to_expr value) |> succ
      | None -> CannotMovePlaceExpr phi |> fail)
    | Borrow (_, _, phi) ->
      let* (referent, _) = eval_place_expr sigma phi
      in let ptr : expr = (inferred, Ptr referent)
      in (sigma, ptr) |> succ
    | BorrowIdx (_, _, phi, (_, Prim (Num n))) ->
      let* (referent, value) = eval_place_expr sigma phi
      in (match value with
      | ArrayVal values ->
        if n < 0 then Aborted "negative array index out of bounds" |> fail
        else if n > List.length values then Aborted "array index out of bounds" |> fail
        else let ptr : expr = (inferred, Ptr referent)
        in (sigma, ptr) |> succ
      | _ -> NotAnArray value |> fail)
    | BorrowIdx (prov, omega, phi, idx) ->
      let* (sigmaPrime, idxPrime) = step sigma idx
      in (sigmaPrime, (fst e, BorrowIdx (prov, omega, phi, idxPrime))) |> succ
    | BorrowSlice (_, _, phi, (_, Prim (Num n1)), (_, Prim (Num n2))) ->
      let* (referent, value) = eval_place_expr sigma phi
      in (match value with
      | ArrayVal values ->
        if n1 < 0 then Aborted "negative slice out of bounds" |> fail
        else if n2 > List.length values then Aborted "slice out of bounds" |> fail
        else if n1 > n2 then Aborted "negative-sized slice" |> fail
        else let ptr : expr = (inferred, Ptr referent)
        in (sigma, ptr) |> succ
      | _ -> NotAnArray value |> fail)
    | BorrowSlice (prov, omega, phi, ((_, Prim (Num _)) as idx1), idx2) ->
      let* (sigmaPrime, idx2Prime) = step sigma idx2
      in (sigmaPrime, (fst e, BorrowSlice (prov, omega, phi, idx1, idx2Prime))) |> succ
    | BorrowSlice (prov, omega, phi, idx1, idx2) ->
      let* (sigmaPrime, idx1Prime) = step sigma idx1
      in (sigmaPrime, (fst e, BorrowSlice (prov, omega, phi, idx1Prime, idx2))) |> succ
    | LetProv (_, e) -> (sigma, e) |> succ
    | Let (var, ty, e1, e2) ->
      if is_value e1 then let* v1 = expr_to_value e1
      in (extend sigma var v1, e2) |> succ
      else let* (sigmaPrime, e1Prime) = step sigma e1
      in (sigmaPrime, (fst e, Let (var, ty, e1Prime, e2))) |> succ
    | Assign (phi, exp) ->
      if is_value exp then let x = expr_root_of phi
      in let* ctx = value_ctx_in sigma phi
      in let* new_value = exp |> expr_to_value >>= plug_value_ctx ctx
      in let new_exp : expr = (fst e, Prim Unit)
      in (update sigma x new_value, new_exp) |> succ
      else let* (sigmaPrime, ePrime) = step sigma exp
      in (sigmaPrime, (fst e, Assign (phi, ePrime))) |> succ
    | Seq (e1, e2) ->
      if is_value e1 then (sigma, e2) |> succ
      else let* (sigmaPrime, e1Prime) = step sigma e1
      in (sigmaPrime, (fst e, Seq (e1Prime, e2))) |> succ
    | Fn fn_var -> StuckAtValue (FnVal fn_var) |> fail
    | Fun ([], [], params, ret_ty, body) ->
      (match free_vars body with
      | Fail _ -> failwith "unreachable: free_vars on closure body cannot error at runtime"
      | Succ xfs ->
        let* xncs = free_nc_vars_rt sigma body
        in let captured_frame = sigma |> List.flatten |> List.filter ((flip List.mem $ xfs) >> fst)
        in let sigmaPrime = update_all sigma xncs Dead
        in let ePrime : expr = (inferred, Closure (captured_frame, params, ret_ty, body))
        in (sigmaPrime, ePrime) |> succ)
    | Fun (_, _, _, _, _) -> failwith "unreachable: closures cannot be polymorphic"
    | App ((_, Fn fn_var) as fn, _, _, _, args) ->
      let (already_values, to_be_evaluated) = partition is_value args
      in if is_empty to_be_evaluated then
        match global_env_find_fn globals fn_var with
        | Some (_, _, _, _, params, _, _, body) ->
          let vars = List.map fst params
          in let arg_values : value list = List.map unsafe_expr_to_value args
          in let top_frame = List.combine vars arg_values
          in (top_frame :: sigma, body) |> succ
          (* FIXME: do substitution, though I'm not sure it matters for runtime only *)
        | None -> NoFunctionDefined (fn_var, globals) |> fail
      else let* (sigmaPrime, hdPrime) = to_be_evaluated |> List.hd |> step sigma
      in let new_args = List.concat [already_values; [hdPrime]; List.tl to_be_evaluated]
      in let ePrime : expr = (fst e, App (fn, [], [], [], new_args))
      in (sigmaPrime, ePrime) |> succ
    | App ((_, Closure (frame, params, _, body)) as cls, [], [], [], args) ->
      let (already_values, to_be_evaluated) = partition is_value args
      in if is_empty to_be_evaluated then
        let vars = List.map fst params
        in let arg_values : value list = List.map unsafe_expr_to_value args
        in let top_frame = List.concat [List.combine vars arg_values; frame]
        in (top_frame :: sigma, body) |> succ
      else let* (sigmaPrime, hdPrime) = to_be_evaluated |> List.hd |> step sigma
      in let new_args = List.concat [already_values; [hdPrime]; List.tl to_be_evaluated]
      in let ePrime : expr = (fst e, App (cls, [], [], [], new_args))
      in (sigmaPrime, ePrime) |> succ
    | App (e, envs, provs, tys, args) ->
      let* (sigmaPrime, ePrime) = step sigma e
      in (sigmaPrime, (fst e, App (ePrime, envs, provs, tys, args))) |> succ
    | Idx (phi, (_, Prim (Num idx))) ->
      (match eval_place_expr sigma phi with
      | Succ (_, ArrayVal values) ->
          if idx < 0 then Aborted "negative array index out of bounds" |> fail
          else if idx > List.length values then Aborted "array index out of bounds" |> fail
          else (sigma, List.nth values idx |> value_to_expr) |> succ
      | Succ (_, value) -> NotAnArray value |> fail
      | Fail err -> Fail err)
    | Idx (phi, idx) ->
      let* (sigmaPrime, idxPrime) = step sigma idx
      in (sigmaPrime, (fst e, Idx (phi, idxPrime))) |> succ
    | Abort msg -> Aborted msg |> fail
    | Branch ((_, Prim True), cons, _) -> (sigma, cons) |> succ
    | Branch ((_, Prim False), _, alt) -> (sigma, alt) |> succ
    | Branch (cond, cons, alt) ->
      let* (sigmaPrime, condPrime) = step sigma cond
      in (sigmaPrime, (fst e, Branch (condPrime, cons, alt))) |> succ
    | While (e1, e2) ->
      let cons = (inferred, Seq (e2, e))
      in let alt : expr = (inferred, Prim Unit)
      in (sigma, (inferred, Branch (e1, cons, alt))) |> succ
    | Tup exprs ->
      let (already_values, to_be_evaluated) = partition is_value exprs
      in if is_empty to_be_evaluated then
        let* v = expr_to_value e
        in StuckAtValue v |> fail
      else let* (sigmaPrime, hdPrime) = to_be_evaluated |> List.hd |> step sigma
      in let ePrime : expr = (fst e, Tup (List.concat [already_values; [hdPrime];
                                                      List.tl to_be_evaluated]))
      in (sigmaPrime, ePrime) |> succ
    | Array exprs ->
      let (already_values, to_be_evaluated) = partition is_value exprs
      in if is_empty to_be_evaluated then
        let* v = expr_to_value e
        in StuckAtValue v |> fail
      else let* (sigmaPrime, hdPrime) = to_be_evaluated |> List.hd |> step sigma
      in let ePrime : expr = (fst e, Tup (List.concat [already_values; [hdPrime];
                                                      List.tl to_be_evaluated]))
      in (sigmaPrime, ePrime) |> succ
    | RecStruct (sn, provs, tys, field_pairs) ->
      let (already_values, to_be_evaluated) = partition (is_value >> snd) field_pairs
      in if is_empty to_be_evaluated then
        let* v = expr_to_value e
        in StuckAtValue v |> fail
      else let (field, hd) = List.hd to_be_evaluated
      in let* (sigmaPrime, hdPrime) = step sigma hd
      in let new_field_pairs = List.concat [already_values; [(field, hdPrime)];
                                            List.tl to_be_evaluated]
      in let ePrime : expr = (fst e, RecStruct (sn, provs, tys, new_field_pairs))
      in (sigmaPrime, ePrime) |> succ
    | TupStruct (sn, provs, tys, exprs) ->
      let (already_values, to_be_evaluated) = partition is_value exprs
      in if is_empty to_be_evaluated then
        let* v = expr_to_value e
        in StuckAtValue v |> fail
      else let* (sigmaPrime, hdPrime) = to_be_evaluated |> List.hd |> step sigma
      in let new_exprs = (List.concat [already_values; [hdPrime];
                                      List.tl to_be_evaluated])
      in let ePrime : expr = (fst e, TupStruct (sn, provs, tys, new_exprs))
      in (sigmaPrime, ePrime) |> succ
    | Ptr referent -> StuckAtValue (PtrVal referent) |> fail
    | Closure (frame, params, ret_ty, body) ->
      StuckAtValue (ClosureVal (frame, params, ret_ty, body)) |> fail
  in step sigma e

let interp (globals : global_env) (exp : expr) : value rt =
  let rec loop (sigma : store) (exp : expr) : value rt =
    if is_value exp then expr_to_value exp
    else let* (sigmaPrime, expPrime) = step globals sigma exp
    in loop sigmaPrime expPrime
  in loop [] exp
