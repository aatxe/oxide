open Syntax

val kill_loans_for :
  place_expr -> loan_env -> loan_env

val ownership_safe :
  global_env -> tyvar_env -> loan_env -> var_env -> owned ->
  place_expr -> (ty * loans) tc
