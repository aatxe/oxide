let fstfst (p : ('a * 'b) * 'c) : 'a = fst (fst p)
let fstsnd (p : ('a * 'b) * 'c) : 'b = snd (fst p)
let sndfst (p : 'a * ('b * 'c)) : 'b = fst (snd p)
let sndsnd (p : 'a * ('b * 'c)) : 'c = snd (snd p)

let compare_keys (x : 'a * 'b) (y : 'a * 'c) : int = compare (fst x) (fst y)

let uniq_cons (x : 'a) (xs : 'a list) : 'a list =
  if List.mem x xs then xs else List.cons x xs

let list_union (xs : 'a list) (ys : 'a list) : 'a list =
  List.fold_right uniq_cons xs ys

(* replace the element at index i in xs with x *)
let replace xs i x =
  List.mapi (fun idx elem -> if idx = i then x else elem) xs

(* replace the element value associated with the given key in xs with new_value *)
let replace_assoc xs key new_value =
  List.map (fun (k, v) -> if k = key then (k, new_value) else (k, v)) xs

let compose (g : 'b -> 'c) (f : 'a -> 'b) : 'a -> 'c = fun x -> g (f x)
let (>>) = compose

let ($) (f : 'a -> 'b) (a : 'a) : 'b = f a
let flip (f : 'a -> 'b -> 'c) : 'b -> 'a -> 'c =
  fun b -> fun a -> f a b

let unwrap (opt : 'a option) : 'a =
  match opt with
  | Some x -> x
  | None -> failwith "attempted to unwrap an empty option"

(* checks if the given list is empty *)
let is_empty (lst : 'a list) : bool = List.length lst = 0
(* checks if the given list is non-empty*)
let non_empty (lst : 'a list) : bool = is_empty lst |> not

(* returns true if the given lists are equal modulo ordering *)
let equal_unordered (lst1 : 'a list) (lst2 : 'b list) : bool =
  (* FIXME: take into account duplicate entries *)
  List.for_all (fun elem -> List.mem elem lst2) lst1 &&
  List.for_all (fun elem -> List.mem elem lst1) lst2

(* collects all the elements where pred is true *)
let take_while (pred : 'a -> bool) (lst : 'a list) : 'a list =
  let collect (acc : 'a list) (elem : 'a) : 'a list =
    if pred elem then List.cons elem acc else acc
  in List.fold_left collect [] lst |> List.rev

(* drops elements from the list until the predicate returns false *)
let rec drop_while (pred : 'a -> bool) (lst : 'a list) : 'a list =
  match lst with
  | hd :: tl when pred hd -> drop_while pred tl
  | lst -> lst

let flat_map (oper : 'a -> 'b list) (lst : 'a list) : 'b list =
  List.map oper lst |> List.flatten

let flatten_opts (lst : 'a option list) : 'a list =
  flat_map (fun opt -> match opt with Some x -> [x] | None -> []) lst

let flat_mapi (oper : int -> 'a -> 'b list) (lst : 'a list) : 'b list =
  List.mapi oper lst |> List.flatten

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
