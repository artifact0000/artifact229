open Hexadecimal

module NilEmpty =
 struct
  (** val string_of_uint : uint -> char list **)

  let rec string_of_uint = function
  | Nil -> []
  | D0 d0 -> '0'::(string_of_uint d0)
  | D1 d0 -> '1'::(string_of_uint d0)
  | D2 d0 -> '2'::(string_of_uint d0)
  | D3 d0 -> '3'::(string_of_uint d0)
  | D4 d0 -> '4'::(string_of_uint d0)
  | D5 d0 -> '5'::(string_of_uint d0)
  | D6 d0 -> '6'::(string_of_uint d0)
  | D7 d0 -> '7'::(string_of_uint d0)
  | D8 d0 -> '8'::(string_of_uint d0)
  | D9 d0 -> '9'::(string_of_uint d0)
  | Da d0 -> 'a'::(string_of_uint d0)
  | Db d0 -> 'b'::(string_of_uint d0)
  | Dc d0 -> 'c'::(string_of_uint d0)
  | Dd d0 -> 'd'::(string_of_uint d0)
  | De d0 -> 'e'::(string_of_uint d0)
  | Df d0 -> 'f'::(string_of_uint d0)
 end
