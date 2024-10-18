open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Arch_params
open Asm_gen
open Compiler_util
open Eqtype
open Expr
open Fexpr
open Linearization
open Protect_calls
open Seq
open Slh_lowering
open Slh_ops
open Sopn
open Ssrint
open Stack_alloc
open Stack_zeroization
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize
open X86_decl
open X86_extra
open X86_instr_decl
open X86_lowering
open X86_stack_zeroization

val x86_op_align :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> wsize -> wsize -> (lexpr list * (register, register_ext, xmm_register,
  rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list

val lea_ptr :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lval
  -> pexpr -> assgn_tag -> coq_Z -> (register, register_ext, xmm_register,
  rflag, condt, x86_op, x86_extra_op) extended_op instr_r

val x86_mov_ofs :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lval
  -> assgn_tag -> vptr_kind -> pexpr -> coq_Z -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr_r option

val x86_immediate :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> coq_Z -> x86_extended_op instr_r

val x86_swap :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  assgn_tag -> var_i -> var_i -> var_i -> var_i -> x86_extended_op instr_r

val x86_saparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op stack_alloc_params

val x86_allocate_stack_frame :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i option -> coq_Z -> ((lexpr list * x86_extended_op sopn) * rexpr
  list) list

val x86_free_stack_frame :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i option -> coq_Z -> ((lexpr list * x86_extended_op sopn) * rexpr
  list) list

val x86_lassign :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lexpr
  -> wsize -> rexpr -> (lexpr list * x86_extended_op sopn) * rexpr list

val x86_set_up_sp_register :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> coq_Z -> wsize -> var_i -> var_i -> ((lexpr list * (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  sopn) * rexpr list) list

val x86_lmove :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i -> (lexpr list * x86_extended_op sopn) * rexpr list

val x86_check_ws : wsize -> bool

val x86_lstore :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> coq_Z -> var_i -> (lexpr list * x86_extended_op sopn) * rexpr list

val x86_lload :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i -> coq_Z -> (lexpr list * x86_extended_op sopn) * rexpr list

val x86_liparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op linearization_params

val x86_loparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  ((register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op, lowering_options) lowering_params

val lv_none_flags : lval list

val x86_sh_lower :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lval
  list -> slh_op -> pexpr list -> ((lval list * (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op sopn) * pexpr
  list) option

val x86_update_after_call :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> (lval list * (register, register_ext, xmm_register, rflag, condt,
  x86_op, x86_extra_op) extended_op sopn) * pexpr list

val x86_shparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op sh_params

val lexpr_flags :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> lexpr
  list

val x86_fop_movi :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> coq_Z -> (lexpr list * (register, register_ext, xmm_register, rflag,
  condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list

val x86_fop_movx :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i -> (lexpr list * (register, register_ext, xmm_register, rflag,
  condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list

val x86_fop_cmpi :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> coq_Z -> (lexpr list * (register, register_ext, xmm_register, rflag,
  condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list

val x86_fop_protect_64 :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i -> (lexpr list * (register, register_ext, xmm_register, rflag,
  condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list

val x86_lcmd_pop :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> var_i -> ((lexpr list * (register, register_ext, xmm_register, rflag,
  condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list) list

val x86_lcmd_pushi :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> var_i
  -> coq_Z -> ((lexpr list * (register, register_ext, xmm_register, rflag,
  condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list) list

val r_uncons : 'a2 -> 'a1 list -> ('a2, 'a1 * 'a1 list) result

val fcond_eq :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr

val fcond_ne :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr

val fcond_lt :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr

val fcond_gt :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> fexpr

val x86_is_update_after_call :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op sopn -> bool

type btree_position =
| BTPleft
| BTPright
| BTPmiddle

val go_left : btree_position -> btree_position

val go_right : btree_position -> btree_position

val update_after_call_cond :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (char list option -> pp_error_loc) -> coq_Z -> var_i -> btree_position ->
  cs_info bintree -> (((lexpr list * (register, register_ext, xmm_register,
  rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr list)
  list * fexpr) cexec

val lower_update_after_call :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (char list option -> pp_error_loc) -> coq_Z -> var_i -> cs_info bintree ->
  lexpr list -> rexpr list -> ((lexpr list * (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr
  list) list cexec

val load_tag :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  load_tag_args -> var_i * ((lexpr list * (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op sopn) * rexpr
  list) list

val save_ra :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (char list option -> pp_error_loc) -> save_tag_args -> coq_Z -> ((lexpr
  list * (register, register_ext, xmm_register, rflag, condt, x86_op,
  x86_extra_op) extended_op sopn) * rexpr list) list cexec

val x86_pcparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op protect_calls_params

val not_condt : condt -> condt

val or_condt : instr_info -> fexpr -> condt -> condt -> condt cexec

val and_condt :
  instr_info -> fexpr -> condt -> condt -> (pp_error_loc, condt) result

val of_var_e_bool :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  instr_info -> var_i -> rflag cexec

val assemble_cond_r :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  instr_info -> fexpr -> condt cexec

val assemble_cond :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  instr_info -> fexpr -> condt cexec

val x86_agparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  asm_gen_params

val x86_szparams :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op stack_zeroization_params

val x86_is_move_op :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op asm_op_t -> bool

val x86_params :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op,
  lowering_options) architecture_params
