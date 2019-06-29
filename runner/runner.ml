module Json = Yojson.Basic
open Shexp_process
open Base

let (let*) x f = bind x ~f

type result =
  | OutputMatches
  | OutputDoesntMatch
  | OutputMissing
  | TypeCheckerFailed
  | ReducerFailed
  | NotTestFile
[@@deriving show, eq]



let rec mapM ~f xs =
  match xs with
  | [] -> return []
  | x::xs ->
    let* r   = f x in
    let* res = mapM ~f xs in
    return (r::res)

let identity x = x

let with_output ?(silent=true) file k =
  with_temp_file ~prefix:"garbage" ~suffix:"err" (fun err ->
      with_temp_file ~prefix:"test" ~suffix:"ml" (fun f ->
          let* exit_ = chdir "reducer" ((if silent then stderr_to err else identity) (stdout_to f (run_exit_code "cargo" ["run"; file]))) in
          if not (Int.equal exit_ 0) then
            return (file, ReducerFailed)
          else
            let* (exit_, output) = (pipe_both ((if silent then stderr_to err else identity) (run_exit_code "dune" ["utop"; "oxide"; "--"; f])) read_all) in
            if not (Int.equal exit_ 0) then
              return (file, TypeCheckerFailed)
            else
              k output))

let run_file file =
  with_output file (fun output ->
      let* exists = file_exists (file ^ ".output") in
      if not exists then
        return (file, OutputMissing)
      else
        let expected = Stdio.In_channel.read_all (file ^ ".output") in
        return (file, if String.equal expected output then
                  OutputMatches
                else OutputDoesntMatch)
        )

let write_results results dir =
  let h t =
    `List (List.map ~f:(fun x -> `String (fst x))
             (List.filter ~f:(fun x -> equal_result (snd x) t)
                        results)) in
  stdout_to (dir ^ "/results.json")
    (print
       (Json.pretty_to_string
          (`Assoc [("matches", h OutputMatches);
                   ("doesntmatch", h OutputDoesntMatch);
                   ("missing", h OutputMissing);
                   ("typeerror", h TypeCheckerFailed);
                   ("reducererror", h ReducerFailed)])))

let rec run dir =
  let _ = Stdio.print_endline dir in
  let* files = readdir dir in
  let* results = mapM ~f:(fun name ->
      let* s = stat (dir ^ "/" ^ name) in
      if phys_equal s.st_kind Unix.S_DIR
      then run (dir ^ "/" ^ name)
      else if String.is_suffix ~suffix:".rs" name
      then run_file (dir ^ "/" ^ name)
      else return (name, NotTestFile))
      files in
  let* _ = write_results results dir in
  (* let* _ = eprint ([%derive.show: (string * result) list] results) in *)
  return (dir, NotTestFile)


let check file =
  with_output ~silent:false file (fun output ->
      let* _ = print output in
      return (file, OutputMissing))

let trust file =
  with_output file (fun output ->
      let* _ = stdout_to (file ^ ".output") (print output) in
      return (file, OutputMissing))

let _ =
  let usage () =
    (Stdio.print_endline "usage: ";
     Stdio.print_endline "  PROGNAME run path/to/root/of/tests";
     Stdio.print_endline "  PROGNAME check path/to/single/test.rs";
     Stdio.print_endline "  PROGNAME trust path/to/single/test.rs") in
  if Array.length Sys.argv < 3 then
    (* NOTE(dbp 2019-06-28): Argument parsing, done terribly. *)
    usage ()
  else
    let _ = eval (
        let* wd = cwd_logical in
        let pth =
          if String.is_prefix ~prefix:"/" Sys.argv.(2)
          then Sys.argv.(2) else wd ^ "/" ^ Sys.argv.(2)
        in
        match Sys.argv.(1) with
        |"run" ->
          let* _ = run pth in return ()
        |"check" ->
          let* _ = check pth in return ()
        |"trust" ->
          let* _ = trust pth in return ()
        |_ -> usage (); return ()
      ) in ()
