open Arch_decl
open Arch_extra
open Sem_params
open Syscall

(** val ep_of_asm_e :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> 'a8 syscall_sem -> 'a8
    coq_EstateParams **)

let ep_of_asm_e asm_e _ =
  { _pd = (arch_pd asm_e._asm._arch_decl); _msf_size =
    (arch_msfsz asm_e._asm._arch_decl) }

(** val spp_of_asm_e :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> coq_SemPexprParams **)

let spp_of_asm_e asm_e =
  asm_e._asm._arch_decl.ad_fcp

(** val sip_of_asm_e :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> 'a8 syscall_sem ->
    (('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op, 'a8) coq_SemInstrParams **)

let sip_of_asm_e asm_e scs =
  { _asmop = (asm_opI asm_e); _sc_sem = scs }
