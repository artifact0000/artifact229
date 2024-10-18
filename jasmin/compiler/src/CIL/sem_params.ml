open Flag_combination
open Sopn
open Syscall
open Wsize

type 'syscall_state coq_EstateParams = { _pd : coq_PointerData;
                                         _msf_size : coq_MSFsize }

type coq_SemPexprParams =
  coq_FlagCombinationParams
  (* singleton inductive, whose constructor was mk_spp *)

(** val _fcp : coq_SemPexprParams -> coq_FlagCombinationParams **)

let _fcp semPexprParams =
  semPexprParams

type ('asm_op, 'syscall_state) coq_SemInstrParams = { _asmop : 'asm_op asmOp;
                                                      _sc_sem : 'syscall_state
                                                                syscall_sem }
