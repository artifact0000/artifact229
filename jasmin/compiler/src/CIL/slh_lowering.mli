open BinNums
open Datatypes
open Compiler_util
open Constant_prop
open Eqtype
open Expr
open Flag_combination
open Return_address_kind
open Seq
open Slh_ops
open Sopn
open Type
open Utils0
open Var0
open Wsize

module E :
 sig
  val pass : char list

  val pp_user_error :
    instr_info option -> var_info option -> pp_error -> pp_error_loc

  val cond_not_found : instr_info -> pexpr option -> pexpr -> pp_error_loc

  val lvar_variable : instr_info -> pp_error_loc

  val expr_variable : instr_info -> pexpr -> pp_error_loc

  val msf_not_found_r : var_i -> SvExtra.Sv.t -> pp_error_loc

  val msf_not_found : instr_info -> var_i -> SvExtra.Sv.t -> pp_error_loc

  val invalid_nb_args : pp_error_loc

  val invalid_nb_lvals : pp_error_loc

  val cond_uses_mem : instr_info -> pexpr -> pp_error_loc

  val lowering_failed : instr_info -> pp_error_loc

  val invalid_type_for_msf : instr_info -> pp_error_loc

  val update_after_call_failed :
    instr_info -> char list option -> pp_error_loc

  val not_implemented : funname -> char list -> pp_error_loc
 end

module Env :
 sig
  type t = { cond : pexpr option; msf_vars : SvExtra.Sv.t }

  val cond : t -> pexpr option

  val msf_vars : t -> SvExtra.Sv.t

  val restrict_cond : pexpr option -> SvExtra.Sv.t -> pexpr option

  val empty : t

  val initial : Var.var option -> t

  val update_cond : t -> pexpr -> t

  val meet : t -> t -> t

  val le : t -> t -> bool

  val is_msf_var : t -> Var.var -> bool

  val is_cond : t -> pexpr -> bool

  val after_SLHmove : t -> Var.var option -> t

  val after_assign_var : t -> Var.var -> t

  val after_assign_vars : t -> SvExtra.Sv.t -> t
 end

val check_e_msf : instr_info -> Env.t -> pexpr -> (pp_error_loc, unit) result

val check_lv : instr_info -> lval -> (pp_error_loc, Var.var option) result

val check_lv_msf :
  coq_MSFsize -> instr_info -> lval -> (pp_error_loc, Var.var option) result

val check_slho :
  coq_MSFsize -> instr_info -> lval list -> slh_op -> pexpr list -> Env.t ->
  Env.t cexec

val check_f_arg :
  instr_info -> Env.t -> pexpr -> slh_t -> (pp_error_loc, unit) result

val check_f_args :
  instr_info -> Env.t -> pexpr list -> slh_t list -> (pp_error_loc, unit
  list) result

val check_f_lv :
  coq_MSFsize -> instr_info -> Env.t -> lval -> slh_t -> (pp_error_loc,
  Env.t) result

val check_f_lvs :
  coq_MSFsize -> instr_info -> Env.t -> lval list -> slh_t list ->
  (pp_error_loc, Env.t) result

val init_fun_env :
  coq_MSFsize -> Env.t -> var_i list -> stype list -> slh_t list ->
  (pp_error_loc, Env.t) result

val check_res :
  coq_MSFsize -> Env.t -> var_i list -> stype list -> slh_t list ->
  (pp_error_loc, unit) result

val check_for :
  instr_info -> Var.var -> (Env.t -> Env.t cexec) -> nat -> Env.t -> Env.t
  cexec

val neg_const_prop : coq_FlagCombinationParams -> pexpr -> pexpr

val check_while :
  coq_FlagCombinationParams -> instr_info -> pexpr -> (Env.t -> Env.t cexec)
  -> (Env.t -> Env.t cexec) -> nat -> Env.t -> Env.t cexec

type 'asm_op sh_params = { shp_lower : (lval list -> slh_op -> pexpr list ->
                                       ((lval list * 'asm_op sopn) * pexpr
                                       list) option);
                           shp_update_after_call : ((char list option ->
                                                   pp_error_loc) -> var_i ->
                                                   ((lval list * 'asm_op
                                                   sopn) * pexpr list) cexec) }

type slh_function_info = { slhfi_tin : slh_t list; slhfi_tout : slh_t list;
                           slhfi_rak : return_address_kind }

val check_i :
  'a1 asmOp -> coq_MSFsize -> coq_FlagCombinationParams -> (funname ->
  slh_function_info) -> 'a1 instr -> Env.t -> Env.t cexec

val check_cmd :
  'a1 asmOp -> coq_MSFsize -> coq_FlagCombinationParams -> (funname ->
  slh_function_info) -> Env.t -> 'a1 instr list -> Env.t cexec

val check_fd :
  'a1 asmOp -> coq_MSFsize -> progT -> coq_FlagCombinationParams -> (funname
  -> slh_function_info) -> funname -> 'a1 fundef -> Env.t cexec

val is_protect_ptr : slh_op -> positive option

val lower_slho :
  'a1 asmOp -> 'a1 sh_params -> instr_info -> lval list -> assgn_tag ->
  slh_op -> pexpr list -> 'a1 instr_r cexec

val output_msfs :
  (funname -> slh_function_info) -> funname -> lval list -> var_i list

val update_msf :
  'a1 asmOp -> 'a1 sh_params -> (funname -> slh_function_info) -> instr_info
  -> funname -> lval list -> 'a1 instr_r list cexec

val lower_i :
  'a1 asmOp -> coq_PointerData -> 'a1 sh_params -> (funname ->
  slh_function_info) -> bool -> 'a1 instr -> 'a1 instr list cexec

val lower_cmd :
  'a1 asmOp -> coq_PointerData -> 'a1 sh_params -> (funname ->
  slh_function_info) -> bool -> 'a1 instr list -> 'a1 instr list cexec

val protected_ret :
  'a1 asmOp -> coq_PointerData -> progT -> (funname -> slh_function_info) ->
  Env.t -> funname -> 'a1 fundef -> 'a1 instr list cexec

val lower_fd :
  'a1 asmOp -> coq_PointerData -> coq_MSFsize -> progT ->
  coq_FlagCombinationParams -> 'a1 sh_params -> (funname ->
  slh_function_info) -> bool -> funname -> 'a1 fundef -> 'a1 fundef cexec

val lower_slh_prog :
  'a1 asmOp -> coq_PointerData -> coq_MSFsize -> progT ->
  coq_FlagCombinationParams -> 'a1 sh_params -> (funname ->
  slh_function_info) -> bool -> funname list -> 'a1 prog -> 'a1 prog cexec
