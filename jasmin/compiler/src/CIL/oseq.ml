open Datatypes
open Ssrfun

(** val onth : 'a1 list -> nat -> 'a1 option **)

let rec onth s i =
  match s with
  | [] -> None
  | x :: s' -> (match i with
                | O -> Some x
                | S i' -> onth s' i')

(** val omap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec omap f = function
| [] -> Some []
| x :: s' ->
  (match f x with
   | Some y -> Option.map (fun x0 -> y :: x0) (omap f s')
   | None -> None)
