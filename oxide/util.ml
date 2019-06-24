let fstfst (p : ('a * 'b) * 'c) : 'a = fst (fst p)
let fstsnd (p : ('a * 'b) * 'c) : 'b = snd (fst p)
let sndfst (p : 'a * ('b * 'c)) : 'b = fst (snd p)
let sndsnd (p : 'a * ('b * 'c)) : 'c = snd (snd p)

let uniq_cons (x : 'a) (xs : 'a list) : 'a list =
  if List.mem x xs then xs else List.cons x xs

let list_union (xs : 'a list) (ys : 'a list) : 'a list =
  List.fold_right uniq_cons xs ys

let unwrap (opt : 'a option) : 'a =
  match opt with
  | Some x -> x
  | None -> failwith "attempted to unwrap an empty option"

(* checks if the given list is empty *)
let is_empty (lst : 'a list) : bool = List.length lst = 0
