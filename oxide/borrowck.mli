open Syntax

val kill_loans_for :
  place_expr -> var_env -> var_env

val ownership_safe :
  global_env -> tyvar_env -> var_env -> owned ->
  place_expr -> (ty * loans) tc
