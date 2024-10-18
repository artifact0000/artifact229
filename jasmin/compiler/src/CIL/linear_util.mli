open BinNums
open BinPos
open Datatypes
open Label
open Linear
open Sopn
open Utils0

val map_lfundef :
  'a1 asmOp -> ('a1 lcmd -> 'a1 lcmd) -> 'a1 lfundef -> 'a1 lfundef

val max_map :
  ('a2 -> 'a2 -> comparison) -> ('a1 -> 'a2 option) -> 'a1 list -> 'a2 option
  -> 'a2 option

val max_lcmd_lbl : 'a1 asmOp -> 'a1 lcmd -> label option

val max_lfd_lbl : 'a1 asmOp -> 'a1 lfundef -> label option

val next_lbl : label -> label

val next_lfd_lbl : 'a1 asmOp -> 'a1 lfundef -> label
