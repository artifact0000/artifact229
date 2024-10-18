open BinInt
open BinNums
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Sopn
open Ssrbool
open Type
open Utils0
open Var0
open Warray_
open Word_ssrZ
open Wsize

module E :
 sig
  val pass : char list

  val reg_error : var_i -> char list -> pp_error_loc

  val reg_error_expr : pexpr -> char list -> pp_error_loc

  val reg_ierror : var_i -> char list -> pp_error_loc

  val length_mismatch : pp_error_loc

  val reg_ierror_no_var : char list -> pp_error_loc
 end

type varr_info = { vi_v : Var.var; vi_s : wsize; vi_n : Ident.Ident.ident list }

type expand_info = { vars : Var.var list; arrs : varr_info list;
                     finfo : fun_info }

type array_info = { ai_ty : wsize; ai_len : coq_Z; ai_elems : Var.var list }

type t = { svars : SvExtra.Sv.t; sarrs : array_info Mvar.t }

type expd_t = ((wsize * coq_Z) option list * (wsize * coq_Z) option list) Mf.t

val init_elems :
  SvExtra.Sv.elt -> (SvExtra.Sv.t * coq_Z) -> (pp_error_loc,
  SvExtra.Sv.t * coq_Z) result

val init_array_info :
  varr_info -> (SvExtra.Sv.t * array_info Mvar.t) -> (pp_error_loc,
  SvExtra.Sv.t * array_info Mvar.Map.t) result

val init_map : expand_info -> (pp_error_loc, t * fun_info) result

val check_gvar : t -> gvar -> bool

val expand_e : t -> pexpr -> pexpr cexec

val expand_lv : t -> lval -> (pp_error_loc, lval) result

val expand_es : t -> pexpr list -> (pp_error_loc, pexpr list) result

val expand_lvs : t -> lval list -> (pp_error_loc, lval list) result

val expand_param :
  t -> (Equality.sort * Equality.sort) option -> pexpr -> pexpr list cexec

val expand_return :
  t -> (wsize * coq_Z) option -> lval -> (pp_error_loc, lval list) result

val expand_i : 'a1 asmOp -> expd_t -> t -> 'a1 instr -> 'a1 instr cexec

val expand_tyv :
  t -> bool -> char list -> stype -> var_i -> (pp_error_loc, (stype
  list * var_i list) * (wsize * coq_Z) option) result

val expand_fsig :
  'a1 asmOp -> (funname -> 'a1 ufundef -> expand_info) -> funname list ->
  funname -> 'a1 ufundef -> (pp_error_loc, (('a1, extra_fun_t)
  _fundef * t) * ((wsize * coq_Z) option list * (wsize * coq_Z) option list))
  result

val expand_fbody :
  'a1 asmOp -> expd_t -> funname -> ('a1 ufundef * t) -> (pp_error_loc, ('a1,
  extra_fun_t) _fundef) result

val expand_prog :
  'a1 asmOp -> (funname -> 'a1 ufundef -> expand_info) -> funname list -> 'a1
  uprog -> 'a1 uprog cexec
