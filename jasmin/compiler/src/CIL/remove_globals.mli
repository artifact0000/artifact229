open Datatypes
open Compiler_util
open Eqtype
open Expr
open Global
open Seq
open Sopn
open Ssralg
open Type
open Utils0
open Var0
open Word0
open Wsize

module E :
 sig
  val pass : char list

  val rm_glob_error : instr_info -> Var.var -> pp_error_loc

  val rm_glob_error_dup : instr_info -> Var.var -> pp_error_loc

  val loop_iterator : pp_error_loc

  val rm_glob_ierror : char list -> pp_error_loc
 end

val check_data : glob_value -> wsize -> GRing.ComRing.sort -> bool

val find_glob :
  instr_info -> var_i -> glob_decl list -> wsize -> GRing.ComRing.sort ->
  (pp_error_loc, Var.var) result

val add_glob :
  (glob_decl list -> Var.var -> Ident.Ident.ident) -> instr_info -> Var.var
  -> glob_decl list -> wsize -> GRing.ComRing.sort -> (pp_error_loc,
  glob_decl list) result

val extend_glob_i :
  'a1 asmOp -> (glob_decl list -> Var.var -> Ident.Ident.ident) -> 'a1 instr
  -> glob_decl list -> (pp_error_loc, glob_decl list) result

val extend_glob_prog :
  'a1 asmOp -> (glob_decl list -> Var.var -> Ident.Ident.ident) -> 'a1 uprog
  -> (pp_error_loc, glob_decl list) result

val get_var_ :
  instr_info -> Var.var Mvar.t -> gvar -> (pp_error_loc, gvar) result

val remove_glob_e :
  instr_info -> Var.var Mvar.t -> pexpr -> (pp_error_loc, pexpr) result

val remove_glob_lv :
  instr_info -> Var.var Mvar.t -> lval -> (pp_error_loc, lval) result

val remove_glob :
  'a1 asmOp -> (Var.var Mvar.t -> 'a1 instr -> (Var.var Mvar.t * 'a1 instr
  list) cexec) -> Var.var Mvar.t -> 'a1 instr list -> (Var.var Mvar.t * 'a1
  instr list) cexec

val merge_glob : Var.var -> Var.var option -> Var.var option -> Var.var option

val coq_Mincl : Var.var Mvar.t -> Var.var Mvar.t -> bool

val merge_env : Var.var Mvar.t -> Var.var Mvar.t -> Var.var Mvar.t

val loop :
  'a1 asmOp -> (Var.var Mvar.t -> (Var.var Mvar.t * 'a1 instr list) cexec) ->
  nat -> Var.var Mvar.t -> (pp_error_loc, Var.var Mvar.t * 'a1 instr list)
  result

type 'asm_op check2_r =
| Check2_r of pexpr * (Var.var Mvar.t * 'asm_op instr list)
   * (Var.var Mvar.t * 'asm_op instr list)

type 'asm_op loop2_r =
| Loop2_r of pexpr * 'asm_op instr list * 'asm_op instr list * Var.var Mvar.t

val loop2 :
  'a1 asmOp -> (Var.var Mvar.t -> 'a1 check2_r cexec) -> nat -> Var.var
  Mvar.t -> (pp_error_loc, 'a1 loop2_r) result

val remove_glob_i :
  'a1 asmOp -> glob_decl list -> Var.var Mvar.t -> 'a1 instr -> (Var.var
  Mvar.t * 'a1 instr list) cexec

val remove_glob_fundef :
  'a1 asmOp -> glob_decl list -> 'a1 ufundef -> (pp_error_loc, ('a1,
  extra_fun_t) _fundef) result

val remove_glob_prog :
  'a1 asmOp -> (glob_decl list -> Var.var -> Ident.Ident.ident) -> 'a1 uprog
  -> (pp_error_loc, ('a1, extra_fun_t, extra_prog_t) _prog) result
