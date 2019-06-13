let fstfst (p : ('a * 'b) * 'c) : 'a = fst (fst p)
let fstsnd (p : ('a * 'b) * 'c) : 'b = snd (fst p)
let sndfst (p : 'a * ('b * 'c)) : 'b = fst (snd p)
let sndsnd (p : 'a * ('b * 'c)) : 'c = snd (snd p)
