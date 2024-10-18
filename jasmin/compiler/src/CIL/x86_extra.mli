open BinNums
open Datatypes
open String0
open Arch_decl
open Arch_extra
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Sem_type
open Seq
open Sopn
open Ssralg
open Type
open Utils0
open Var0
open Word0
open Wsize
open X86
open X86_decl
open X86_instr_decl

module E :
 sig
  val pass_name : char list

  val error : instr_info -> char list -> pp_error_loc

  val se_update_arguments : instr_info -> pp_error_loc

  val se_protect_arguments : instr_info -> pp_error_loc

  val se_protect_ptr : instr_info -> pp_error_loc

  val slh_update_after_call : instr_info -> pp_error_loc
 end

type x86_extra_op =
| Oset0 of wsize
| Oconcat128
| Ox86MOVZX32
| Ox86MULX of wsize
| Ox86MULX_hi of wsize
| Ox86SLHinit
| Ox86SLHupdate
| Ox86SLHmove
| Ox86SLHprotect of wsize
| Ox86SLHupdate_after_call

val x86_extra_op_beq : x86_extra_op -> x86_extra_op -> bool

val x86_extra_op_eq_dec : x86_extra_op -> x86_extra_op -> bool

val x86_extra_op_eq_axiom : x86_extra_op Equality.axiom

val x86_extra_op_eqMixin : x86_extra_op Equality.mixin_of

val x86_extra_op_eqType : Equality.coq_type

val coq_Oset0_instr :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> wsize
  -> instruction_desc

val coq_Oconcat128_instr : instruction_desc

val coq_Ox86MOVZX32_instr : instruction_desc

val x86_MULX :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val coq_Ox86MULX_instr :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> wsize
  -> instruction_desc

val x86_MULX_hi :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val coq_Ox86MULX_hi_instr :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> wsize
  -> instruction_desc

val coq_Ox86SLHinit_str : char list

val coq_Ox86SLHinit_instr : instruction_desc

val x86_se_update_sem :
  bool -> GRing.ComRing.sort -> (GRing.ComRing.sort * GRing.ComRing.sort) exec

val coq_Ox86SLHupdate_str : char list

val coq_Ox86SLHupdate_instr : instruction_desc

val coq_Ox86SLHmove_str : char list

val coq_Ox86SLHmove_instr : instruction_desc

val se_protect_small_sem :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort -> sem_tuple exec

val se_protect_large_sem :
  wsize -> GRing.ComRing.sort -> GRing.ComRing.sort ->
  (GRing.ComRing.sort * GRing.ComRing.sort) exec

val coq_Ox86SLHprotect_str : char list

val coq_Ox86SLHprotect_instr :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> wsize
  -> instruction_desc

val coq_Ox86SLHupdate_after_call_str : char list

val coq_Ox86SLHupdate_after_call_instr : instruction_desc

val get_instr_desc :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  x86_extra_op -> instruction_desc

val prim_string : (char list * x86_extra_op prim_constructor) list

val re_i : wsize -> coq_Z -> rexpr

val re8_0 : rexpr

val re8_1 : rexpr

val assemble_slh_init :
  lexpr list -> (((register, register_ext, xmm_register, rflag, condt,
  x86_op) asm_op_msb_t * lexpr list) * rexpr list) list cexec

val assemble_slh_update :
  instr_info -> lexpr list -> rexpr list -> (((register, register_ext,
  xmm_register, rflag, condt, x86_op) asm_op_msb_t * lexpr list) * rexpr
  list) list cexec

val assemble_slh_protect :
  instr_info -> wsize -> lexpr list -> rexpr list -> (((register,
  register_ext, xmm_register, rflag, condt, x86_op) asm_op_msb_t * lexpr
  list) * rexpr list) list cexec

val assemble_slh_move :
  lexpr list -> rexpr list -> (((register, register_ext, xmm_register, rflag,
  condt, x86_op) asm_op_msb_t * lexpr list) * rexpr list) list cexec

val assemble_extra :
  instr_info -> x86_extra_op -> lexpr list -> rexpr list -> (((register,
  register_ext, xmm_register, rflag, condt, x86_op) asm_op_msb_t * lexpr
  list) * rexpr list) list cexec

val eqC_x86_extra_op : x86_extra_op eqTypeC

val x86_extra_op_decl :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  x86_extra_op asmOp

val x86_extra :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  asm_extra

type x86_extended_op =
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op

val coq_Ox86 :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> x86_op
  -> x86_extended_op sopn
