open BinNums
open Datatypes
open String0
open Arch_decl
open Arch_extra
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Lea
open Linear
open One_varmap
open Oseq
open Seq
open Sopn
open Ssralg
open Ssrbool
open Ssrnat
open Syscall
open Type
open Utils0
open Var0
open Word0
open Wsize

module E :
 sig
  val pass_name : char list

  val gen_error :
    bool -> instr_info option -> var_info option -> pp_error -> pp_error_loc

  val internal_error : instr_info -> char list -> pp_error_loc

  val unexpected_sopn :
    coq_MSFsize -> 'a1 asmOp -> instr_info -> char list -> 'a1 sopn ->
    pp_error_loc

  val error : instr_info -> pp_error -> pp_error_loc

  val verror : bool -> char list -> instr_info -> var_i -> pp_error_loc

  val invalid_name : char list -> instr_info -> var_i -> pp_error_loc

  val invalid_ty : char list -> instr_info -> var_i -> pp_error_loc

  val invalid_flag : instr_info -> var_i -> pp_error_loc

  val berror : instr_info -> fexpr -> char list -> pp_error_loc

  val werror : instr_info -> rexpr -> char list -> pp_error_loc
 end

val fail : instr_info -> char list -> pp_error_loc

val of_var_e :
  stype -> 'a1 coq_ToString -> 'a1 coq_ToIdent -> instr_info -> var_i ->
  (pp_error_loc, 'a1) result

val to_reg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option

val to_regx :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) regx_t option

val to_xreg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) xreg_t option

val to_rflag :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) rflag_t option

val asm_typed_reg_of_var :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg cexec

val var_of_asm_typed_reg :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_typed_reg -> Var.var

type ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) asm_gen_params =
  instr_info -> fexpr -> ('reg, 'regx, 'xreg, 'rflag, 'cond) cond_t cexec
  (* singleton inductive, whose constructor was Build_asm_gen_params *)

val agp_assemble_cond :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> instr_info -> fexpr -> ('a1, 'a2, 'a3, 'a4,
  'a5) cond_t cexec

val scale_of_z : instr_info -> coq_Z -> nat cexec

val reg_of_ovar :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> instr_info -> var_i option
  -> ('a1, 'a2, 'a3, 'a4, 'a5) reg_t option cexec

val assemble_lea :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> instr_info -> lea ->
  (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) address) result

val addr_of_fexpr :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> instr_info ->
  wsize -> fexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) address) result

val addr_of_xpexpr :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> instr_info ->
  wsize -> var_i -> fexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5)
  address) result

val xreg_of_var :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> instr_info -> var_i ->
  ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg cexec

val assemble_word_load :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> instr_info ->
  wsize -> rexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg) result

val assemble_word :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> addr_kind -> Var.var ->
  instr_info -> wsize -> rexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_arg) result

val arg_of_rexpr :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> addr_kind -> Var.var -> instr_info -> stype ->
  rexpr -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg) result

val rexpr_of_lexpr : lexpr -> rexpr

type 't nmap = nat -> 't option

val nget : 'a1 nmap -> nat -> 'a1 option

val nset : 'a1 nmap -> nat -> 'a1 -> Equality.sort -> 'a1 option

val nempty : nat -> 'a1 option

val is_implicit :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  implicit_arg -> rexpr -> bool

val compile_arg :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ((('a1, 'a2, 'a3, 'a4,
  'a5) Arch_decl.arg_desc * stype) * rexpr) -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_arg nmap -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg nmap cexec

val compile_args :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> (('a1, 'a2, 'a3, 'a4,
  'a5) Arch_decl.arg_desc * stype) list -> rexpr list -> ('a1, 'a2, 'a3, 'a4,
  'a5) asm_arg nmap -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg nmap)
  result

val compat_imm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> stype -> Equality.sort ->
  Equality.sort -> bool

val check_sopn_arg :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5) asm_arg list -> rexpr -> (('a1, 'a2, 'a3, 'a4, 'a5)
  Arch_decl.arg_desc * stype) -> bool

val check_sopn_dest :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5) asm_arg list -> rexpr -> (('a1, 'a2, 'a3, 'a4, 'a5)
  Arch_decl.arg_desc * stype) -> bool

val assemble_asm_op_aux :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6) asm_op_msb_t -> lexpr list -> rexpr list -> (pp_error_loc, ('a1,
  'a2, 'a3, 'a4, 'a5) asm_arg list) result

val check_sopn_args :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5) asm_arg list -> rexpr list -> (('a1, 'a2, 'a3, 'a4, 'a5)
  Arch_decl.arg_desc * stype) list -> bool

val check_sopn_dests :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5) asm_arg list -> lexpr list -> (('a1, 'a2, 'a3, 'a4, 'a5)
  Arch_decl.arg_desc * stype) list -> bool

val check_arg_kind_no_imm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_arg -> arg_kind -> bool

val filter_arg_kinds_no_imm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_arg -> arg_kinds -> (unit, arg_kinds) result

val filter_args_kinds_no_imm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_args -> args_kinds -> args_kinds option

val filter_i_args_kinds_no_imm :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> i_args_kinds -> ('a1, 'a2,
  'a3, 'a4, 'a5) asm_args -> i_args_kinds

val enforce_imm_arg_kind :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_arg -> arg_kind -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg option

val enforce_imm_arg_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_arg -> arg_kinds -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg option

val enforce_imm_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  asm_args -> args_kinds -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args option

val enforce_imm_i_args_kinds :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> i_args_kinds -> ('a1, 'a2,
  'a3, 'a4, 'a5) asm_args -> ('a1, 'a2, 'a3, 'a4, 'a5) asm_args option

val pp_arg_kind : arg_kind -> pp_error

val pp_arg_kinds : arg_kind list -> pp_error

val pp_args_kinds : arg_kind list list -> pp_error

val pp_i_args_kinds : arg_kind list list list -> pp_error

val assemble_asm_op :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6) asm_op_msb_t -> lexpr list -> rexpr list -> (pp_error_loc,
  'a6 * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) result

val assemble_asm_args :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ((('a1, 'a2, 'a3, 'a4,
  'a5, 'a6) asm_op_msb_t * lexpr list) * rexpr list) -> (pp_error_loc,
  'a6 * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) result

val assemble_sopn :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> instr_info -> ('a1, 'a2, 'a3, 'a4,
  'a5, 'a6, 'a7) extended_op sopn -> lexpr list -> rexpr list ->
  (pp_error_loc, ('a6 * ('a1, 'a2, 'a3, 'a4, 'a5) asm_arg list) list) result

val is_not_app1 : rexpr -> bool

val assemble_i :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op linstr -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i list cexec

val assemble_c :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5,
  'a6, 'a7) asm_gen_params -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7)
  extended_op lcmd -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_i list cexec

val is_typed_reg :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> Var.var -> bool

val typed_reg_of_vari :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> var_i -> ('a1, 'a2, 'a3,
  'a4, 'a5) asm_typed_reg cexec

val assemble_fd :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_gen_params ->
  Var.var -> Var.var -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op
  lfundef -> (pp_error_loc, ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) asm_fundef) result

val assemble_prog :
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_extra -> ('a1, 'a2, 'a3, 'a4, 'a5)
  calling_convention -> ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) asm_gen_params ->
  ('a1, 'a2, 'a3, 'a4, 'a5, 'a6, 'a7) extended_op lprog -> ('a1, 'a2, 'a3,
  'a4, 'a5, 'a6) asm_prog cexec

val vflags :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> SvExtra.Sv.t

val all_vars :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> SvExtra.Sv.t

val ovm_i :
  ('a1, 'a2, 'a3, 'a4, 'a5) arch_decl -> ('a1, 'a2, 'a3, 'a4, 'a5)
  arch_toIdent -> ('a1, 'a2, 'a3, 'a4, 'a5) calling_convention ->
  one_varmap_info
