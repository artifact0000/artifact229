open Datatypes
open Arch_decl
open Arch_extra
open Arm
open Arm_decl
open Arm_instr_decl
open Arm_params_core
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Seq
open Sopn
open Ssralg
open Type
open Utils0
open Var0
open Word0
open Wsize

type __ = Obj.t

type arm_extra_op =
| Oarm_swap of wsize
| Oarm_add_large_imm

val arm_extra_op_beq : arm_extra_op -> arm_extra_op -> bool

val arm_extra_op_eq_dec : arm_extra_op -> arm_extra_op -> bool

val arm_extra_op_eq_axiom : arm_extra_op Equality.axiom

val arm_extra_op_eqMixin : arm_extra_op Equality.mixin_of

val arm_extra_op_eqType : Equality.coq_type

val eqTC_arm_extra_op : arm_extra_op eqTypeC

val coq_Oarm_add_large_imm_instr : instruction_desc

val get_instr_desc : arm_extra_op -> instruction_desc

val arm_extra_op_decl : arm_extra_op asmOp

module E :
 sig
  val pass_name : char list

  val internal_error : instr_info -> char list -> pp_error_loc

  val error : instr_info -> char list -> pp_error_loc
 end

val assemble_extra :
  instr_info -> arm_extra_op -> lexpr list -> rexpr list -> (((register, __,
  __, rflag, condt, arm_op) asm_op_msb_t * lexpr list) * rexpr list) list
  cexec

val arm_extra :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) asm_extra

type arm_extended_op =
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op

val coq_Oarm :
  (register, __, __, rflag, condt) arch_toIdent -> arm_op -> arm_extended_op
  sopn
