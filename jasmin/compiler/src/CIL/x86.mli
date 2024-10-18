open Datatypes
open Arch_decl
open Eqtype
open Utils0
open X86_decl
open X86_instr_decl

val x86_eval_cond :
  (rflag -> (error, bool) result) -> condt -> (error, bool) result

val x86 : (register, register_ext, xmm_register, rflag, condt, x86_op) asm
