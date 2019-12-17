open Oxide.Edsl
open Oxide.Typeck
open Oxide.Syntax

let prog : global_env =
  [(fn "unnest"
      [(("unknown_file", (1, 10), (1, 11)), "a"); (("unknown_file", (1, 14), (1, 15)), "b")]
      []
      ["pt"
      @:
      ((("unknown_file", (1, 22), (1, 23)),
      Ref
      ((("unknown_file", (1, 23), (1, 24)), "a"),
      Unique,
      ((("unknown_file", (1, 30), (1, 31)),
      Ref
      ((("unknown_file", (1, 31), (1, 32)), "b"),
      Unique,
      ((("unknown_file", (1, 38), (1, 41)), BaseTy U32))))))))]
      ((("unknown_file", (1, 46), (1, 47)),
      Ref
      ((("unknown_file", (1, 47), (1, 48)), "a"),
      Unique,
      ((("unknown_file", (1, 54), (1, 57)), BaseTy U32)))))
      ((("unknown_file", (2, 4), (2, 5)),
          Borrow
          ((("unknown_file", (2, 4), (2, 5)), "p1"), Unique, (Deref ((Deref (Var "pt"))))))))]

let main = match wf_global_env prog with
  | Succ () -> Format.printf "valid global environment:@. %a@." pp_global_env prog
  | Fail err ->
    Format.printf "error: %a@.invalid global environment:@. %a@." pp_tc_error err pp_global_env prog
