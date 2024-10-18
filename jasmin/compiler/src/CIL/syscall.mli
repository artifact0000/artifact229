open BinNums
open Eqtype
open Ssralg
open Type
open Utils0
open Wsize

val syscall_t_beq :
  BinNums.positive Syscall_t.syscall_t ->
  BinNums.positive Syscall_t.syscall_t -> bool

val syscall_t_eq_axiom : BinNums.positive Syscall_t.syscall_t Equality.axiom

val syscall_t_eqMixin : BinNums.positive Syscall_t.syscall_t Equality.mixin_of

val syscall_t_eqType : Equality.coq_type

type syscall_sig_t = { scs_tin : stype list; scs_tout : stype list }

val syscall_sig_u : BinNums.positive Syscall_t.syscall_t -> syscall_sig_t

val syscall_sig_s :
  coq_PointerData -> BinNums.positive Syscall_t.syscall_t -> syscall_sig_t

type 'syscall_state syscall_sem =
  'syscall_state -> coq_Z -> 'syscall_state * GRing.ComRing.sort list
  (* singleton inductive, whose constructor was Build_syscall_sem *)

val get_random :
  'a1 syscall_sem -> 'a1 -> coq_Z -> 'a1 * GRing.ComRing.sort list

type 'syscall_state syscall_state_t = 'syscall_state
