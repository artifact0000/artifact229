open BinNums
open BinPos
open Var0

type label_kind =
| InternalLabel
| ExternalLabel

type label = positive

(** val next_lbl : label -> label **)

let next_lbl lbl =
  Pos.add lbl Coq_xH

type remote_label = funname * label
