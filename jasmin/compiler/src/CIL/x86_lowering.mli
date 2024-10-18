open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Compiler_util
open Eqtype
open Expr
open Lea
open Lowering
open Pseudo_operator
open Seq
open Sopn
open Ssralg
open Ssrfun
open Type
open Utils0
open Var0
open Word0
open Word_ssrZ
open Wsize
open X86_decl
open X86_extra
open X86_instr_decl

val is_regx_e : pexpr -> bool

val is_regx_l : lval -> bool

val mov_ws :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> wsize
  -> lval -> pexpr -> assgn_tag -> x86_extended_op instr_r

type lowering_options = { use_lea : bool; use_set0 : bool }

val vword : wsize -> Ident.Ident.ident -> Var.var

val fv_of : fresh_vars -> Var.var

val fv_cf : fresh_vars -> Var.var

val fv_sf : fresh_vars -> Var.var

val fv_zf : fresh_vars -> Var.var

val fvars : fresh_vars -> SvExtra.Sv.t

val disj_fvars : fresh_vars -> SvExtra.Sv.t -> bool

val fvars_correct :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> progT -> (register, register_ext, xmm_register, rflag, condt,
  x86_op, x86_extra_op) extended_op fun_decl list -> bool

val var_info_of_lval : lval -> var_info

val stype_of_lval : lval -> stype

val wsize_of_stype : stype -> wsize

val wsize_of_lval : lval -> wsize

val lower_cond_classify :
  fresh_vars -> var_info -> pexpr -> ((((lval
  list * wsize) * pexpr) * pexpr) * pexpr) option

val lower_condition :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> var_info -> pexpr -> (register, register_ext, xmm_register,
  rflag, condt, x86_op, x86_extra_op) extended_op instr_r list * pexpr

type add_inc_dec =
| AddInc of pexpr
| AddDec of pexpr
| AddNone

val add_inc_dec_classify : wsize -> pexpr -> pexpr -> add_inc_dec

type sub_inc_dec =
| SubInc
| SubDec
| SubNone

val sub_inc_dec_classify : Equality.sort -> pexpr -> sub_inc_dec

type divmod_pos =
| DM_Fst
| DM_Snd

type lower_cassgn_t =
| LowerMov of bool
| LowerCopn of (register, register_ext, xmm_register, rflag, condt, x86_op,
               x86_extra_op) extended_op sopn * pexpr list
| LowerInc of (register, register_ext, xmm_register, rflag, condt, x86_op,
              x86_extra_op) extended_op sopn * pexpr
| LowerLea of wsize * lea
| LowerFopn of wsize
   * (register, register_ext, xmm_register, rflag, condt, x86_op,
     x86_extra_op) extended_op sopn * pexpr list * wsize option
| LowerDiscardFlags of nat
   * (register, register_ext, xmm_register, rflag, condt, x86_op,
     x86_extra_op) extended_op sopn * pexpr list
| LowerCond
| LowerIf of stype * pexpr * pexpr * pexpr
| LowerDivMod of divmod_pos * signedness * wsize
   * (register, register_ext, xmm_register, rflag, condt, x86_op,
     x86_extra_op) extended_op sopn * pexpr * pexpr
| LowerConcat of pexpr * pexpr
| LowerAssgn

val is_lea : wsize -> lval -> pexpr -> lea option

val is_lnot : pexpr -> pexpr option

val is_andn : pexpr -> pexpr -> (pexpr * pexpr) option

val mulr : wsize -> pexpr -> pexpr -> x86_op * pexpr list

val check_shift_amount : wsize -> pexpr -> pexpr option

val check_signed_range : wsize option -> wsize -> coq_Z -> bool

val lower_cassgn_classify :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  Equality.sort -> pexpr -> lval -> lower_cassgn_t

type opn_5flags_cases_t =
| Opn5f_large_immed of pexpr * pexpr * pexpr list
| Opn5f_other

val opn_5flags_cases :
  pexpr list -> wsize option -> wsize -> opn_5flags_cases_t

val opn_no_imm :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op sopn -> (register, register_ext, xmm_register, rflag, condt,
  x86_op, x86_extra_op) extended_op sopn

val opn_5flags :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> wsize option -> wsize -> var_info -> lval -> lval ->
  assgn_tag -> (register, register_ext, xmm_register, rflag, condt, x86_op,
  x86_extra_op) extended_op sopn -> pexpr list -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr_r list

val reduce_wconst : wsize -> pexpr -> pexpr

val lower_cassgn :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  lowering_options -> (instr_info -> warning_msg -> instr_info) -> fresh_vars
  -> instr_info -> lval -> assgn_tag -> stype -> pexpr -> (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  instr list

val lower_addcarry_classify :
  bool -> lval list -> pexpr list -> ((((var_info * (wsize ->
  x86_op)) * pexpr list) * lval) * lval) option

val lower_addcarry :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> wsize -> bool -> lval list -> assgn_tag -> pexpr list ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op instr_r list

val lower_mulu :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> wsize -> lval list -> assgn_tag -> pexpr list -> (register,
  register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op
  instr_r list

val lower_swap :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent -> stype
  -> lval list -> assgn_tag -> pexpr list -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op instr_r list

val lower_pseudo_operator :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> lval list -> assgn_tag -> pseudo_operator -> pexpr list ->
  (register, register_ext, xmm_register, rflag, condt, x86_op, x86_extra_op)
  extended_op instr_r list

val lower_copn :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  fresh_vars -> lval list -> assgn_tag -> (register, register_ext,
  xmm_register, rflag, condt, x86_op, x86_extra_op) extended_op sopn -> pexpr
  list -> (register, register_ext, xmm_register, rflag, condt, x86_op,
  x86_extra_op) extended_op instr_r list

val lower_i :
  (register, register_ext, xmm_register, rflag, condt) arch_toIdent ->
  lowering_options -> (instr_info -> warning_msg -> instr_info) -> fresh_vars
  -> (register, register_ext, xmm_register, rflag, condt, x86_op,
  x86_extra_op) extended_op instr -> (register, register_ext, xmm_register,
  rflag, condt, x86_op, x86_extra_op) extended_op instr list
