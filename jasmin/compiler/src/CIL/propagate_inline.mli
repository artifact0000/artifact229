open Datatypes
open Compiler_util
open Constant_prop
open Eqtype
open Expr
open Flag_combination
open Seq
open Sopn
open Utils0
open Var0

module E :
 sig
  val pass : char list

  val ii_loop_iterator : instr_info -> pp_error_loc
 end

type pi_cel = { pi_def : pexpr; pi_fv : SvExtra.Sv.t; pi_m : bool }

type pimap = pi_cel Mvar.t

val piempty : pimap

val remove : pimap -> Var.var -> pi_cel Mvar.t

val remove_m : pimap -> pi_cel Mvar.t

val set : pimap -> Var.var -> pexpr -> pimap

val merge : pimap -> pimap -> pi_cel Mvar.t

val incl : pimap -> pimap -> bool

val scfc : coq_FlagCombinationParams -> combine_flags -> pexpr list -> pexpr

val pi_e : coq_FlagCombinationParams -> pimap -> pexpr -> pexpr

val pi_es : coq_FlagCombinationParams -> pimap -> pexpr list -> pexpr list

val pi_lv : coq_FlagCombinationParams -> pimap -> lval -> pimap * lval

val pi_lvs :
  coq_FlagCombinationParams -> pimap -> lval list -> pimap * lval list

val set_lv : pimap -> lval -> Equality.sort -> pexpr -> pimap

val pi_c :
  'a1 asmOp -> (pimap -> 'a1 instr -> (pimap * 'a1 instr) cexec) -> pimap ->
  'a1 instr list -> (pp_error_loc, pimap * 'a1 instr list) result

val loop_for :
  'a1 asmOp -> (pimap -> 'a1 instr -> (pimap * 'a1 instr) cexec) ->
  instr_info -> Var.var -> 'a1 instr list -> nat -> pimap -> (pp_error_loc,
  pimap * 'a1 instr list) result

val loop_while :
  'a1 asmOp -> coq_FlagCombinationParams -> (pimap -> 'a1 instr ->
  (pimap * 'a1 instr) cexec) -> instr_info -> 'a1 instr list -> pexpr -> 'a1
  instr list -> nat -> pimap -> (pp_error_loc, ((pimap * 'a1 instr
  list) * pexpr) * 'a1 instr list) result

val pi_i :
  'a1 asmOp -> coq_FlagCombinationParams -> pimap -> 'a1 instr ->
  (pp_error_loc, pimap * 'a1 instr) result

val pi_fun :
  'a1 asmOp -> coq_FlagCombinationParams -> progT -> 'a1 fundef ->
  (pp_error_loc, ('a1, extra_fun_t) _fundef) result

val pi_prog :
  'a1 asmOp -> coq_FlagCombinationParams -> progT -> 'a1 prog ->
  (pp_error_loc, ('a1, extra_fun_t, extra_prog_t) _prog) result
