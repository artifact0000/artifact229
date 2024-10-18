open Arch_decl
open Arch_extra
open Sem_params
open Syscall

val ep_of_asm_e :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> 'a8 syscall_sem -> 'a8
  coq_EstateParams

val spp_of_asm_e :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> coq_SemPexprParams

val sip_of_asm_e :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> 'a8 syscall_sem -> (('a1,
  'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op, 'a8) coq_SemInstrParams
