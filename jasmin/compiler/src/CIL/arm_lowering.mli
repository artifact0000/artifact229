open BinInt
open BinNums
open Datatypes
open Arch_decl
open Arch_extra
open Arm_decl
open Arm_extra
open Arm_instr_decl
open Eqtype
open Expr
open Lowering
open Pseudo_operator
open Seq
open Shift_kind
open Sopn
open Ssralg
open Ssrbool
open Type
open Utils0
open Var0
open Word0
open Wsize

type __ = Obj.t

val fv_NF : fresh_vars -> Ident.Ident.ident

val fv_ZF : fresh_vars -> Ident.Ident.ident

val fv_CF : fresh_vars -> Ident.Ident.ident

val fv_VF : fresh_vars -> Ident.Ident.ident

val all_fresh_vars : fresh_vars -> Ident.Ident.ident list

val fvNF : fresh_vars -> Var.var

val fvZF : fresh_vars -> Var.var

val fvCF : fresh_vars -> Var.var

val fvVF : fresh_vars -> Var.var

val fresh_flags : fresh_vars -> Var.var list

val fvars : fresh_vars -> SvExtra.Sv.t

val chk_ws_reg : wsize -> unit option

val flags_of_mn : fresh_vars -> arm_mnemonic -> Var.var list

val lflags_of_mn : fresh_vars -> arm_mnemonic -> lval list

val lower_TST : pexpr -> pexpr -> pexpr list option

val lower_condition_Papp2 :
  fresh_vars -> sop2 -> pexpr -> pexpr -> ((arm_mnemonic * pexpr) * pexpr
  list) option

val lower_condition_pexpr :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> pexpr ->
  (((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op sopn) * pexpr list) * pexpr) option

val lower_condition :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> pexpr ->
  (register, __, __, rflag, condt, arm_op, arm_extra_op) extended_op instr_r
  list * pexpr

val get_arg_shift :
  wsize -> pexpr list -> ((pexpr * shift_kind) * pexpr) option

val arg_shift : arm_mnemonic -> wsize -> pexpr list -> arm_op * pexpr list

val lower_Pvar : wsize -> gvar -> (arm_op * pexpr list) option

val lower_load : wsize -> pexpr -> (arm_op * pexpr list) option

val is_load : pexpr -> bool

val coq_Z_mod_lnot : coq_Z -> wsize -> coq_Z

val mov_imm_mnemonic : pexpr -> (arm_mnemonic * pexpr) option

val lower_Papp1 : wsize -> sop1 -> pexpr -> (arm_op * pexpr list) option

val is_mul : pexpr -> (pexpr * pexpr) option

val is_rsb : wsize -> pexpr -> pexpr -> bool

val lower_Papp2_op :
  wsize -> sop2 -> pexpr -> pexpr -> ((arm_mnemonic * pexpr) * pexpr list)
  option

val lower_Papp2 :
  wsize -> sop2 -> pexpr -> pexpr -> (arm_op * pexpr list) option

val lower_pexpr_aux : wsize -> pexpr -> (arm_op * pexpr list) option

val no_pre :
  (register, __, __, rflag, condt) arch_toIdent -> (arm_op * pexpr list)
  option -> (((register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op instr_r list * arm_op) * pexpr list) option

val lower_pexpr :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> wsize ->
  pexpr -> (((register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op instr_r list * arm_op) * pexpr list) option

val lower_store : wsize -> pexpr -> (arm_op * pexpr list) option

val lower_cassgn_word :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> lval ->
  wsize -> pexpr -> ((register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op instr_r list * ((lval list * (register, __, __, rflag, condt,
  arm_op, arm_extra_op) extended_op sopn) * pexpr list)) option

val lower_cassgn_bool :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> lval ->
  assgn_tag -> pexpr -> (register, __, __, rflag, condt, arm_op,
  arm_extra_op) extended_op instr_r list option

val lower_add_carry :
  (register, __, __, rflag, condt) arch_toIdent -> lval list -> pexpr list ->
  ((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op sopn) * pexpr list) option

val lower_mulu :
  (register, __, __, rflag, condt) arch_toIdent -> lval list -> pexpr list ->
  ((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op sopn) * pexpr list) option

val with_shift : arm_options -> shift_kind -> arm_options

val lower_base_op :
  (register, __, __, rflag, condt) arch_toIdent -> lval list -> arm_op ->
  pexpr list -> ((lval list * (register, __, __, rflag, condt, arm_op,
  arm_extra_op) extended_op sopn) * pexpr list) option

val lower_swap :
  (register, __, __, rflag, condt) arch_toIdent -> stype -> lval list ->
  pexpr list -> ((lval list * (register, __, __, rflag, condt, arm_op,
  arm_extra_op) extended_op sopn) * pexpr list) option

val lower_pseudo_operator :
  (register, __, __, rflag, condt) arch_toIdent -> lval list ->
  pseudo_operator -> pexpr list -> ((lval list * (register, __, __, rflag,
  condt, arm_op, arm_extra_op) extended_op sopn) * pexpr list) option

val lower_copn :
  (register, __, __, rflag, condt) arch_toIdent -> lval list -> (register,
  __, __, rflag, condt, arm_op, arm_extra_op) extended_op sopn -> pexpr list
  -> ((lval list * (register, __, __, rflag, condt, arm_op, arm_extra_op)
  extended_op sopn) * pexpr list) option

type lowering_options = unit

val lower_i :
  (register, __, __, rflag, condt) arch_toIdent -> fresh_vars -> (register,
  __, __, rflag, condt, arm_op, arm_extra_op) extended_op instr -> (register,
  __, __, rflag, condt, arm_op, arm_extra_op) extended_op instr list
