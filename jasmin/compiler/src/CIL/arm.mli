open Datatypes
open Arch_decl
open Arm_decl
open Arm_instr_decl
open Eqtype
open Utils0

type __ = Obj.t

val arm_eval_cond :
  (rflag -> (error, bool) result) -> condt -> (error, bool) result

val arm : (register, __, __, rflag, condt, arm_op) asm
