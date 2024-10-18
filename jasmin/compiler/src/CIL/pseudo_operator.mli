open BinNums
open Bool
open Eqtype
open Seq
open Ssrbool
open Type
open Utils0
open Wsize

type spill_op =
| Spill
| Unspill

val spill_op_beq : spill_op -> spill_op -> bool

val spill_op_eq_axiom : spill_op Equality.axiom

val eqTC_spill_op : spill_op eqTypeC

val spill_op_eqType : Equality.coq_type

type pseudo_operator =
| Ospill of spill_op * stype list
| Ocopy of wsize * positive
| Onop
| Omulu of wsize
| Oaddcarry of wsize
| Osubcarry of wsize
| Oswap of stype

val pseudo_operator_beq : pseudo_operator -> pseudo_operator -> bool

val pseudo_operator_eq_axiom : pseudo_operator Equality.axiom

val eqTC_pseudo_operator : pseudo_operator eqTypeC

val pseudo_operator_eqType : Equality.coq_type

val string_of_pseudo_operator : pseudo_operator -> char list
