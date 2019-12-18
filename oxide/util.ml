let fstfst (p : ('a * 'b) * 'c) : 'a = fst (fst p)
let fstsnd (p : ('a * 'b) * 'c) : 'b = snd (fst p)
let sndfst (p : 'a * ('b * 'c)) : 'b = fst (snd p)
let sndsnd (p : 'a * ('b * 'c)) : 'c = snd (snd p)

let uniq_cons (x : 'a) (xs : 'a list) : 'a list =
  if List.mem x xs then xs else List.cons x xs

let list_union (xs : 'a list) (ys : 'a list) : 'a list =
  List.fold_right uniq_cons xs ys

(* replace the element at index i in xs with x *)
let replace xs i x =
  List.mapi (fun idx elem -> if idx = i then x else elem) xs

let unwrap (opt : 'a option) : 'a =
  match opt with
  | Some x -> x
  | None -> failwith "attempted to unwrap an empty option"

(* checks if the given list is empty *)
let is_empty (lst : 'a list) : bool = List.length lst = 0

(* collects all the elements where pred is true *)
let take_while (pred : 'a -> bool) (lst : 'a list) : 'a list =
  let collect (acc : 'a list) (elem : 'a) : 'a list =
    if pred elem then List.cons elem acc else acc
  in List.rev (List.fold_left collect [] lst)

(* drops elements from the list until the predicate returns false *)
let rec drop_while (pred : 'a -> bool) (lst : 'a list) : 'a list =
  match lst with
  | hd :: tl when pred hd -> drop_while pred tl
  | lst -> lst

(* splits the list into a prefix and a suffix such that:
   - forall x in prefix. pred x = true
   - pred (head suffix) = false *)
let rec partition (pred : 'a -> bool) (lst : 'a list) : 'a list * 'a list =
  match lst with
  | [] -> ([], [])
  | hd :: tl when pred hd ->
    let (prefix, suffix) = partition pred tl
    in (List.cons hd prefix, suffix)
  | lst -> ([], lst)
