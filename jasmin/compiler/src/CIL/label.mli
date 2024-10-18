open BinNums
open BinPos
open Var0

type label_kind =
| InternalLabel
| ExternalLabel

type label = positive

val next_lbl : label -> label

type remote_label = funname * label
