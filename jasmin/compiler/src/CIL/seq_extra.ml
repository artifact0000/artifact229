
(** val pairfoldl :
    ('a2 -> 'a1 -> 'a1 -> 'a2) -> 'a2 -> 'a1 -> 'a1 list -> 'a2 **)

let rec pairfoldl f z t = function
| [] -> z
| x :: s' -> pairfoldl f (f z t x) x s'
