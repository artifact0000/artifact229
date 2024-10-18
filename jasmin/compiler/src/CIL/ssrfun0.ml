open Ssrfun

(** val olift : ('a1 -> 'a2) -> 'a1 -> 'a2 option **)

let olift f =
  comp (fun x -> Some x) f
