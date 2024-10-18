open Datatypes
open Compiler_util
open Eqtype
open Expr
open Sem_type
open Seq
open Sopn
open Ssrfun
open Syscall
open Type
open Utils0
open Var0
open Warray_
open Word_ssrZ
open Wsize

module E :
 sig
  val pass_name : char list

  val gen_error : bool -> instr_info option -> char list -> pp_error_loc

  val error : char list -> pp_error_loc

  val loop_iterator : pp_error_loc

  val fold2 : pp_error_loc
 end

module M :
 sig
  module Mv :
   sig
    val oget : SvExtra.Sv.t Mvar.t -> Equality.sort -> SvExtra.Sv.t

    type t_ = { mvar : Var.var Mvar.t; mid : SvExtra.Sv.t Mvar.t }

    val mvar : t_ -> Var.var Mvar.t

    val mid : t_ -> SvExtra.Sv.t Mvar.t

    type t = t_

    val get : t -> Var.var -> Var.var option

    val rm_id : t -> Equality.sort -> Var.var Mvar.t

    val ms_upd :
      SvExtra.Sv.t Mvar.t -> (SvExtra.Sv.t -> SvExtra.Sv.t) -> Equality.sort
      -> SvExtra.Sv.t Mvar.Map.t

    val rm_x : t -> Equality.sort -> SvExtra.Sv.t Mvar.Map.t

    val remove : t -> Equality.sort -> t_

    val set : t -> Equality.sort -> Equality.sort -> t_

    val add : t_ -> Equality.sort -> Var.var -> t_

    val empty : t_
   end

  val bool_dec : bool -> bool

  val v_compat_type : coq_WithSubWord -> Var.var -> Var.var -> bool

  val v_compat_typeP : coq_WithSubWord -> Var.var -> Var.var -> bool

  type t_ = { mv : Mv.t; mset : SvExtra.Sv.t }

  val mv : coq_WithSubWord -> t_ -> Mv.t

  val mset : coq_WithSubWord -> t_ -> SvExtra.Sv.t

  type t = t_

  val get : coq_WithSubWord -> t -> Var.var -> Var.var option

  val set : coq_WithSubWord -> t_ -> Var.var -> Var.var -> t_

  val add : coq_WithSubWord -> t_ -> Var.var -> Var.var -> t_

  val addc : coq_WithSubWord -> t_ -> Var.var -> Var.var -> t_

  val empty_s : coq_WithSubWord -> SvExtra.Sv.t -> t_

  val empty : coq_WithSubWord -> t_

  val merge_aux : coq_WithSubWord -> t_ -> t_ -> Equality.sort Mvar.t

  val merge : coq_WithSubWord -> t_ -> t_ -> t_

  val remove : coq_WithSubWord -> t_ -> Equality.sort -> t_

  val incl : coq_WithSubWord -> t_ -> t_ -> bool
 end

val alloc_error : char list -> pp_error_loc

val cerr_varalloc : Var.var -> Var.var -> char list -> pp_error_loc

val check_v : coq_WithSubWord -> var_i -> var_i -> M.t -> M.t cexec

val error_e : pp_error_loc

val check_gv : coq_WithSubWord -> gvar -> gvar -> M.t -> M.t cexec

val check_e : coq_WithSubWord -> pexpr -> pexpr -> M.t -> M.t cexec

val check_var_aux : coq_WithSubWord -> Var.var -> Var.var -> M.t_ -> M.t cexec

val check_varc : coq_WithSubWord -> var_i -> var_i -> M.t_ -> M.t cexec

val is_Pvar : (stype * pexpr) option -> (stype * var_i) option

val error_lv : pp_error_loc

val check_lval :
  coq_WithSubWord -> (stype * pexpr) option -> lval -> lval -> M.t -> M.t
  cexec

val loop :
  coq_WithSubWord -> (M.t -> M.t cexec) -> nat -> M.t -> (pp_error_loc, M.t)
  result

val loop2 :
  coq_WithSubWord -> (M.t -> (M.t * M.t) cexec) -> nat -> M.t ->
  (pp_error_loc, M.t) result

val check_es :
  coq_WithSubWord -> pexpr list -> pexpr list -> M.t -> (pp_error_loc, M.t)
  result

val check_lvals :
  coq_WithSubWord -> lval list -> lval list -> M.t -> (pp_error_loc, M.t)
  result

val check_var : coq_WithSubWord -> var_i -> var_i -> M.t -> M.t cexec

val check_vars :
  coq_WithSubWord -> var_i list -> var_i list -> M.t -> (pp_error_loc, M.t)
  result

val check_I :
  coq_WithSubWord -> 'a1 asmOp -> 'a1 instr -> 'a1 instr -> M.t_ ->
  (pp_error_loc, M.t_) result

val check_cmd :
  coq_WithSubWord -> 'a1 asmOp -> 'a1 instr list -> 'a1 instr list -> M.t_ ->
  (pp_error_loc, M.t_) result

val check_fundef :
  coq_WithSubWord -> 'a1 asmOp -> progT -> (extra_fun_t -> extra_prog_t ->
  extra_prog_t -> M.t cexec) -> (M.t -> extra_fun_t -> extra_fun_t -> var_i
  list -> var_i list -> M.t cexec) -> extra_prog_t -> extra_prog_t ->
  (funname * 'a1 fundef) -> (funname * 'a1 fundef) -> unit -> unit cexec

val check_prog_error : pp_error_loc

val check_prog :
  coq_WithSubWord -> 'a1 asmOp -> progT -> (extra_fun_t -> extra_prog_t ->
  extra_prog_t -> M.t cexec) -> (M.t -> extra_fun_t -> extra_fun_t -> var_i
  list -> var_i list -> M.t cexec) -> extra_prog_t -> (funname * 'a1 fundef)
  list -> extra_prog_t -> (funname * 'a1 fundef) list -> (pp_error_loc, unit)
  result

val init_alloc_uprog :
  coq_WithSubWord -> extra_fun_t -> extra_prog_t -> extra_prog_t -> M.t cexec

val check_f_extra_u :
  coq_WithSubWord -> M.t -> extra_fun_t -> extra_fun_t -> var_i list -> var_i
  list -> (pp_error_loc, M.t) result

val check_ufundef :
  coq_WithSubWord -> 'a1 asmOp -> extra_prog_t -> extra_prog_t ->
  (funname * 'a1 fundef) -> (funname * 'a1 fundef) -> unit -> unit cexec

val check_uprog :
  coq_WithSubWord -> 'a1 asmOp -> extra_prog_t -> (funname * 'a1 fundef) list
  -> extra_prog_t -> (funname * 'a1 fundef) list -> (pp_error_loc, unit)
  result

val init_alloc_sprog :
  coq_WithSubWord -> coq_PointerData -> extra_fun_t -> extra_prog_t ->
  extra_prog_t -> M.t cexec

val check_f_extra_s :
  coq_WithSubWord -> coq_PointerData -> M.t -> extra_fun_t -> extra_fun_t ->
  var_i list -> var_i list -> M.t cexec

val check_sprog :
  coq_WithSubWord -> 'a1 asmOp -> coq_PointerData -> extra_prog_t ->
  (funname * 'a1 fundef) list -> extra_prog_t -> (funname * 'a1 fundef) list
  -> (pp_error_loc, unit) result
