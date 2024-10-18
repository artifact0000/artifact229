open BinNums
open Eqtype
open Ssralg
open Type
open Utils0
open Wsize

(** val syscall_t_beq :
    BinNums.positive Syscall_t.syscall_t ->
    BinNums.positive Syscall_t.syscall_t -> bool **)

let syscall_t_beq x y =
  let Syscall_t.RandomBytes x0 = x in
  let Syscall_t.RandomBytes x1 = y in internal_positive_beq x0 x1

(** val syscall_t_eq_axiom :
    BinNums.positive Syscall_t.syscall_t Equality.axiom **)

let syscall_t_eq_axiom =
  eq_axiom_of_scheme syscall_t_beq

(** val syscall_t_eqMixin :
    BinNums.positive Syscall_t.syscall_t Equality.mixin_of **)

let syscall_t_eqMixin =
  { Equality.op = syscall_t_beq; Equality.mixin_of__1 = syscall_t_eq_axiom }

(** val syscall_t_eqType : Equality.coq_type **)

let syscall_t_eqType =
  Obj.magic syscall_t_eqMixin

type syscall_sig_t = { scs_tin : stype list; scs_tout : stype list }

(** val syscall_sig_u :
    BinNums.positive Syscall_t.syscall_t -> syscall_sig_t **)

let syscall_sig_u = function
| Syscall_t.RandomBytes len ->
  { scs_tin = ((Coq_sarr len) :: []); scs_tout = ((Coq_sarr len) :: []) }

(** val syscall_sig_s :
    coq_PointerData -> BinNums.positive Syscall_t.syscall_t -> syscall_sig_t **)

let syscall_sig_s pd _ =
  { scs_tin = ((Coq_sword (coq_Uptr pd)) :: ((Coq_sword
    (coq_Uptr pd)) :: [])); scs_tout = ((Coq_sword (coq_Uptr pd)) :: []) }

type 'syscall_state syscall_sem =
  'syscall_state -> coq_Z -> 'syscall_state * GRing.ComRing.sort list
  (* singleton inductive, whose constructor was Build_syscall_sem *)

(** val get_random :
    'a1 syscall_sem -> 'a1 -> coq_Z -> 'a1 * GRing.ComRing.sort list **)

let get_random syscall_sem0 =
  syscall_sem0

type 'syscall_state syscall_state_t = 'syscall_state
