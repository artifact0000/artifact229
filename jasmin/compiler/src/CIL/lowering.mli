open Compiler_util
open Expr
open Seq
open Sopn
open Type
open Utils0
open Var0

type fresh_vars = Ident.Ident.name -> stype -> Ident.Ident.ident

val disj_fvars : SvExtra.Sv.t -> SvExtra.Sv.t -> bool

val fvars_correct :
  'a1 asmOp -> progT -> Ident.Ident.ident list -> SvExtra.Sv.t -> 'a1
  fun_decl list -> bool

val is_lval_in_memory : lval -> bool

val lower_cmd :
  'a1 asmOp -> ('a2 -> (instr_info -> warning_msg -> instr_info) ->
  fresh_vars -> 'a1 instr -> 'a1 instr list) -> 'a2 -> (instr_info ->
  warning_msg -> instr_info) -> fresh_vars -> 'a1 instr list -> 'a1 instr list

val lower_fd :
  'a1 asmOp -> ('a2 -> (instr_info -> warning_msg -> instr_info) ->
  fresh_vars -> 'a1 instr -> 'a1 instr list) -> 'a2 -> (instr_info ->
  warning_msg -> instr_info) -> fresh_vars -> progT -> 'a1 fundef -> 'a1
  fundef

val lower_prog :
  'a1 asmOp -> ('a2 -> (instr_info -> warning_msg -> instr_info) ->
  fresh_vars -> 'a1 instr -> 'a1 instr list) -> 'a2 -> (instr_info ->
  warning_msg -> instr_info) -> fresh_vars -> progT -> 'a1 prog -> 'a1 prog
