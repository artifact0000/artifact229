open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Arch_params
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Arm_lowering
open Arm_params_common
open Arm_params_core
open Arm_stack_zeroization
open Asm_gen
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Linearization
open Lowering
open Protect_calls
open Seq
open Slh_lowering
open Sopn
open Ssrbool
open Stack_alloc
open Stack_zeroization
open Type
open Utils0
open Var0
open Word_ssrZ
open Wsize

type __ = Obj.t

val is_load : pexpr -> bool

val arm_mov_ofs :
  (register, __, __, rflag, condt) arch_toIdent -> lval -> assgn_tag ->
  vptr_kind -> pexpr -> coq_Z -> (register, __, __, rflag, condt, arm_op,
  arm_extra_op) extended_op instr_r option

val arm_immediate :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z ->
  arm_extended_op instr_r

val arm_swap :
  (register, __, __, rflag, condt) arch_toIdent -> assgn_tag -> var_i ->
  var_i -> var_i -> var_i -> (register, __, __, rflag, condt, arm_op,
  arm_extra_op) extended_op instr_r

val arm_saparams :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op stack_alloc_params

val arm_allocate_stack_frame :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i option ->
  coq_Z -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list)
  list

val arm_free_stack_frame :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i option ->
  coq_Z -> ((FopnArgs.lval list * arm_extended_op sopn) * FopnArgs.rval list)
  list

val arm_set_up_sp_register :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z -> wsize ->
  var_i -> var_i -> ((lexpr list * (register, __, __, rflag, condt, arm_op,
  arm_extra_op) extended_op sopn) * rexpr list) list

val arm_tmp :
  (register, __, __, rflag, condt) arch_toIdent -> Ident.Ident.ident

val arm_tmp2 :
  (register, __, __, rflag, condt) arch_toIdent -> Ident.Ident.ident

val arm_lmove :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> (lexpr
  list * arm_extended_op sopn) * rexpr list

val arm_check_ws : Equality.sort -> bool

val arm_lstore :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> coq_Z -> var_i ->
  (lexpr list * arm_extended_op sopn) * rexpr list

val arm_lload :
  (register, __, __, rflag, condt) arch_toIdent -> var_i -> var_i -> coq_Z ->
  (lexpr list * arm_extended_op sopn) * rexpr list

val arm_liparams :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op linearization_params

val arm_fvars_correct :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> progT ->
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op fun_decl
  list -> bool

val arm_loparams :
  (register, __, __, rflag, condt) arch_toIdent -> ((register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op, lowering_options) lowering_params

val arm_shparams :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op sh_params

val arm_pcparams :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op protect_calls_params

val condt_of_rflag : rflag -> condt

val condt_not : condt -> condt

val condt_and : condt -> condt -> condt option

val condt_or : condt -> condt -> condt option

val is_rflags_GE : rflag -> rflag -> bool

val assemble_cond :
  (register, __, __, rflag, condt) arch_toIdent -> instr_info -> fexpr ->
  condt cexec

val arm_agparams :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) asm_gen_params

val arm_szparams :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op stack_zeroization_params

val arm_is_move_op :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op asm_op_t -> bool

val arm_params :
  (register, __, __, rflag, condt) arch_toIdent -> (register, __, __, rflag,
  condt, arm_op, arm_extra_op, lowering_options) architecture_params
