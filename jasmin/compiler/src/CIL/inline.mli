open Datatypes
open Allocation
open Compiler_util
open Expr
open Sem_type
open Seq
open Sopn
open Type
open Utils0
open Var0

module E :
 sig
  val pass : char list

  val inline_error : pp_error -> pp_error_loc
 end

val get_flag : lval -> assgn_tag -> assgn_tag

val assgn_tuple :
  'a1 asmOp -> instr_info -> lval list -> assgn_tag -> stype list -> pexpr
  list -> 'a1 instr list

val inline_c :
  'a1 asmOp -> ('a1 instr -> SvExtra.Sv.t -> (SvExtra.Sv.t * 'a1 instr list)
  cexec) -> 'a1 instr list -> SvExtra.Sv.t -> (pp_error_loc,
  SvExtra.Sv.t * 'a1 instr list) result

val locals_p : 'a1 asmOp -> 'a1 ufundef -> SvExtra.Sv.t

val check_rename :
  coq_WithSubWord -> 'a1 asmOp -> funname -> 'a1 ufundef -> 'a1 ufundef ->
  SvExtra.Sv.t -> (pp_error_loc, unit) result

val get_fun :
  'a1 asmOp -> 'a1 ufun_decls -> funname -> (pp_error_loc, 'a1 fundef) result

val inline_i :
  coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
  'a1 ufundef) -> 'a1 ufun_decls -> 'a1 instr -> SvExtra.Sv.t ->
  (SvExtra.Sv.t * 'a1 instr list) cexec

val inline_fd :
  coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
  'a1 ufundef) -> 'a1 ufun_decls -> 'a1 ufundef -> (pp_error_loc, ('a1,
  extra_fun_t) _fundef) result

val inline_fd_cons :
  coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
  'a1 ufundef) -> (funname * 'a1 ufundef) -> 'a1 ufun_decls cexec ->
  (pp_error_loc, (funname * 'a1 fundef) list) result

val inline_prog :
  coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
  'a1 ufundef) -> 'a1 ufun_decls -> 'a1 ufun_decls cexec

val inline_prog_err :
  coq_WithSubWord -> 'a1 asmOp -> (instr_info -> funname -> 'a1 ufundef ->
  'a1 ufundef) -> 'a1 uprog -> (pp_error_loc, ('a1, extra_fun_t,
  extra_prog_t) _prog) result
