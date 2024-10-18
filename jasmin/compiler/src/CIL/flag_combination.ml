open Expr
open Wsize

type combine_flags_core =
| CFC_B
| CFC_E
| CFC_L
| CFC_BE
| CFC_LE

(** val cf_tbl : combine_flags -> bool * combine_flags_core **)

let cf_tbl = function
| CF_LT s ->
  (match s with
   | Signed -> (false, CFC_L)
   | Unsigned -> (false, CFC_B))
| CF_LE s ->
  (match s with
   | Signed -> (false, CFC_LE)
   | Unsigned -> (false, CFC_BE))
| CF_EQ -> (false, CFC_E)
| CF_NEQ -> (true, CFC_E)
| CF_GE s ->
  (match s with
   | Signed -> (true, CFC_L)
   | Unsigned -> (true, CFC_B))
| CF_GT s ->
  (match s with
   | Signed -> (true, CFC_LE)
   | Unsigned -> (true, CFC_BE))

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

(** val fc_of_cfc :
    coq_FlagCombinationParams -> combine_flags_core -> flag_combination **)

let fc_of_cfc flagCombinationParams =
  flagCombinationParams

(** val fc_sem :
    ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> flag_combination -> 'a1 **)

let rec fc_sem xnot xand xor xeq x0 x1 x2 x3 = function
| FCVar0 -> x0
| FCVar1 -> x1
| FCVar2 -> x2
| FCVar3 -> x3
| FCNot fc0 -> xnot (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc0)
| FCAnd (fc0, fc1) ->
  xand (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc0)
    (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc1)
| FCOr (fc0, fc1) ->
  xor (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc0)
    (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc1)
| FCEq (fc0, fc1) ->
  xeq (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc0)
    (fc_sem xnot xand xor xeq x0 x1 x2 x3 fc1)

(** val cf_xsem :
    coq_FlagCombinationParams -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
    -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    combine_flags -> 'a1 **)

let cf_xsem fcp xnot xand xor xeq x0 x1 x2 x3 cf =
  let (n, cfc) = cf_tbl cf in
  let x = fc_sem xnot xand xor xeq x0 x1 x2 x3 (fc_of_cfc fcp cfc) in
  if n then xnot x else x
