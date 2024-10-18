
(** val internal_bool_beq : bool -> bool -> bool **)

let internal_bool_beq x y =
  if x then y else if y then false else true
