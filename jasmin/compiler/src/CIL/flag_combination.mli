open Expr
open Wsize

type combine_flags_core =
| CFC_B
| CFC_E
| CFC_L
| CFC_BE
| CFC_LE

val cf_tbl : combine_flags -> bool * combine_flags_core

type flag_combination =
| FCVar0
| FCVar1
| FCVar2
| FCVar3
| FCNot of flag_combination
| FCAnd of flag_combination * flag_combination
| FCOr of flag_combination * flag_combination
| FCEq of flag_combination * flag_combination

type coq_FlagCombinationParams =
  combine_flags_core -> flag_combination
  (* singleton inductive, whose constructor was Build_FlagCombinationParams *)

val fc_of_cfc :
  coq_FlagCombinationParams -> combine_flags_core -> flag_combination

val fc_sem :
  ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
  -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> flag_combination -> 'a1

val cf_xsem :
  coq_FlagCombinationParams -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 ->
  'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  combine_flags -> 'a1
