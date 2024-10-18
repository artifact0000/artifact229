open Datatypes
open Arch_decl
open Sem_type
open Seq
open Ssrnat
open Type
open Utils0
open Wsize

type __ = Obj.t

val of_empty : __ -> 'a1

val eqTC_empty : __ eqTypeC

val finTC_empty : __ finTypeC

val empty_toS : stype -> __ coq_ToString

val ak_reg_reg : i_args_kinds

val ak_reg_imm : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds

val ak_reg_addr : i_args_kinds

val ak_reg_imm8_imm8 : i_args_kinds

val ak_reg_reg_reg : i_args_kinds

val ak_reg_reg_imm : ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> i_args_kinds

val ak_reg_reg_imm8 : i_args_kinds

val ak_reg_reg_imm16 : i_args_kinds

val ak_reg_reg_imm8_imm8 : i_args_kinds

val ak_reg_reg_reg_reg : i_args_kinds

val semi_drop2 :
  stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
  sem_prod

val semi_drop3 :
  stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
  sem_prod

val semi_drop4 :
  stype list -> stype list -> sem_tuple exec sem_prod -> sem_tuple exec
  sem_prod

val idt_drop2 :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t

val idt_drop3 :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t

val idt_drop4 :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  instr_desc_t -> ('a1, 'a2, 'a3, 'a4, 'a5) instr_desc_t

val rtuple_drop5th :
  stype -> stype -> stype -> stype -> stype -> sem_tuple exec -> (error,
  sem_ot * (sem_ot * (sem_ot * sem_ot))) result
