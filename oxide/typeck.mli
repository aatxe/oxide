open Syntax

val valid_prov : tyvar_env -> var_env -> prov -> unit tc

val valid_type :
  global_env -> tyvar_env -> var_env ->
  ty -> unit tc

val valid_types :
  global_env -> tyvar_env -> var_env ->
  ty list -> unit tc

val wf_global_env : global_env -> unit tc

val valid_var_env :
  global_env -> tyvar_env ->
  var_env -> unit tc

val valid_envs :
  global_env -> tyvar_env -> var_env -> unit tc

val type_check :
  global_env -> tyvar_env -> var_env ->
  expr -> (ty * var_env) tc
