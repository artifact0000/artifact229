open Datatypes
open Compiler_util
open Eqtype
open Expr
open Pseudo_operator
open Seq
open Sopn
open Type
open Utils0
open Var0
open Wsize

module E :
 sig
  val pass : char list

  val ii_loop_iterator : instr_info -> pp_error_loc

  val error : instr_info -> pp_error -> pp_error_loc
 end

val is_spill_op : 'a1 asmOp -> 'a1 sopn -> (spill_op * stype list) option

val to_spill_e : SvExtra.Sv.t -> pexpr -> SvExtra.Sv.t

val to_spill_i : 'a1 asmOp -> SvExtra.Sv.t -> 'a1 instr -> SvExtra.Sv.t

type spill_env = SvExtra.Sv.t

val update_lv : spill_env -> lval -> spill_env

val update_lvs : spill_env -> lval list -> spill_env

val get_Pvar : instr_info -> pexpr -> var_i cexec

val get_Pvars : instr_info -> pexpr list -> var_i list cexec

val check_ty :
  instr_info -> var_i list -> stype list -> (pp_error_loc, unit) result

val spill_x :
  'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
  assgn_tag -> spill_env -> var_i -> (pp_error_loc, SvExtra.Sv.t * 'a1 instr)
  result

val spill_es :
  'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
  assgn_tag -> spill_env -> stype list -> pexpr list -> (pp_error_loc,
  spill_env * 'a1 instr list) result

val unspill_x :
  'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
  assgn_tag -> spill_env -> var_i -> (pp_error_loc, 'a1 instr) result

val unspill_es :
  'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> instr_info ->
  assgn_tag -> spill_env -> stype list -> pexpr list -> (pp_error_loc, 'a1
  instr list) result

val spill_c :
  'a1 asmOp -> (spill_env -> 'a1 instr -> (spill_env * 'a1 instr list) cexec)
  -> spill_env -> 'a1 instr list -> (spill_env * 'a1 instr list) cexec

val merge_env : spill_env -> spill_env -> SvExtra.Sv.t

val loop :
  'a1 asmOp -> (spill_env -> 'a1 instr list -> (spill_env * 'a1 instr list)
  cexec) -> instr_info -> 'a1 instr list -> nat -> spill_env ->
  (spill_env * 'a1 instr list) cexec

val wloop :
  'a1 asmOp -> (spill_env -> 'a1 instr list -> (spill_env * 'a1 instr list)
  cexec) -> instr_info -> 'a1 instr list -> 'a1 instr list -> nat ->
  SvExtra.Sv.t -> (SvExtra.Sv.t * ('a1 instr list * 'a1 instr list)) cexec

val spill_i :
  'a1 asmOp -> (instr_info -> Var.var -> Var.var cexec) -> spill_env -> 'a1
  instr -> (spill_env * 'a1 instr list) cexec

val init_map :
  (v_kind -> instr_info -> Ident.Ident.name -> stype -> Ident.Ident.ident) ->
  SvExtra.Sv.t -> Var.var Mvar.t

val get_spill :
  Var.var Mvar.t -> instr_info -> Var.var -> (pp_error_loc, Var.var) result

val check_map : Var.var Mvar.t -> SvExtra.Sv.t -> bool * SvExtra.Sv.t

val spill_fd :
  'a1 asmOp -> (v_kind -> instr_info -> Ident.Ident.name -> stype ->
  Ident.Ident.ident) -> funname -> ('a1, 'a2) _fundef -> ('a1, 'a2) _fundef
  cexec

val spill_prog :
  'a1 asmOp -> (v_kind -> instr_info -> Ident.Ident.name -> stype ->
  Ident.Ident.ident) -> progT -> 'a1 prog -> 'a1 prog cexec
