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

(** val slh_op_beq : slh_op -> slh_op -> bool **)

let slh_op_beq x y =
  match x with
  | SLHinit -> (match y with
                | SLHinit -> true
                | _ -> false)
  | SLHupdate -> (match y with
                  | SLHupdate -> true
                  | _ -> false)
  | SLHmove -> (match y with
                | SLHmove -> true
                | _ -> false)
  | SLHprotect x0 ->
    (match y with
     | SLHprotect x1 -> wsize_beq x0 x1
     | _ -> false)
  | SLHprotect_ptr x0 ->
    (match y with
     | SLHprotect_ptr x1 -> internal_positive_beq x0 x1
     | _ -> false)
  | SLHprotect_ptr_fail x0 ->
    (match y with
     | SLHprotect_ptr_fail x1 -> internal_positive_beq x0 x1
     | _ -> false)

(** val slh_op_eq_axiom : slh_op Equality.axiom **)

let slh_op_eq_axiom =
  eq_axiom_of_scheme slh_op_beq

(** val slh_op_eqMixin : slh_op Equality.mixin_of **)

let slh_op_eqMixin =
  { Equality.op = slh_op_beq; Equality.mixin_of__1 = slh_op_eq_axiom }

(** val slh_op_eqType : Equality.coq_type **)

let slh_op_eqType =
  Obj.magic slh_op_eqMixin

type slh_t =
| Slh_None
| Slh_msf

(** val is_shl_none : slh_t -> bool **)

let is_shl_none = function
| Slh_None -> true
| Slh_msf -> false
