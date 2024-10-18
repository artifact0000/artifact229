open BinNums
open Eqtype
open Type
open Utils0
open Wsize

type slh_op =
| SLHinit
| SLHupdate
| SLHmove
| SLHprotect of wsize
| SLHprotect_ptr of positive
| SLHprotect_ptr_fail of positive

val slh_op_beq : slh_op -> slh_op -> bool

val slh_op_eq_axiom : slh_op Equality.axiom

val slh_op_eqMixin : slh_op Equality.mixin_of

val slh_op_eqType : Equality.coq_type

type slh_t =
| Slh_None
| Slh_msf

val is_shl_none : slh_t -> bool
