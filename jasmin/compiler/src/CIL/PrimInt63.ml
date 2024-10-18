open Datatypes

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val compares : Uint63.t -> Uint63.t -> comparison **)

let compares = (fun x y -> let c = Uint63.compares x y in if c = 0 then Eq else if c < 0 then Lt else Gt)
