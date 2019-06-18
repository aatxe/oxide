let fstfst (p : ('a * 'b) * 'c) : 'a = fst (fst p)
let fstsnd (p : ('a * 'b) * 'c) : 'b = snd (fst p)
let sndfst (p : 'a * ('b * 'c)) : 'b = fst (snd p)
let sndsnd (p : 'a * ('b * 'c)) : 'c = snd (snd p)

let list_union (xs : 'a list) (ys : 'a list) =
  let uniq_cons (x : 'a) (xs : 'a list) =
    if List.mem x xs then xs else List.cons x xs
  in List.fold_right uniq_cons xs ys
